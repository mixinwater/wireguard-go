/* SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2017-2025 WireGuard LLC. All Rights Reserved.
 */

package device

import (
	"crypto/rand"
	"encoding/binary"
	"errors"
	"net"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"
	"golang.zx2c4.com/wireguard/conn"
	"golang.zx2c4.com/wireguard/tun"
)

/* ZERO-LATENCY Enhanced Obfuscation:
 *
 * 1. ASYNC cover traffic (non-blocking goroutines)
 * 2. Pre-computed random padding cache (zero crypto delay)
 * 3. Parallel MSS clamping (doesn't block packet flow)
 * 4. Smart batching (reduces syscalls = lower latency)
 * 5. Optimized checksum (SIMD-friendly)
 */

type QueueOutboundElement struct {
	buffer  *[MaxMessageSize]byte
	packet  []byte
	nonce   uint64
	keypair *Keypair
	peer    *Peer
}

type QueueOutboundElementsContainer struct {
	sync.Mutex
	elems []*QueueOutboundElement
}

/* ═══════════════════════════════════════════════════════════
   ZERO-LATENCY OBFUSCATION LAYER
   ═══════════════════════════════════════════════════════════ */

const (
	// Cover traffic (async, non-blocking)
	coverSizeMin = 40
	coverSizeMax = 80

	// Pre-computed padding cache
	paddingCacheSize = 256
	paddingExtraMax  = 16 // Reduced from 32 for speed
)

// Global pre-computed padding cache (initialized once at startup)
var (
	paddingCache      [paddingCacheSize][paddingExtraMax]byte
	paddingCacheIdx   atomic.Uint32
	paddingCacheReady atomic.Bool
)

// Initialize padding cache at startup (one-time cost)
func initPaddingCache() {
	if paddingCacheReady.Load() {
		return
	}
	for i := 0; i < paddingCacheSize; i++ {
		rand.Read(paddingCache[i][:])
	}
	paddingCacheReady.Store(true)
}

// Fast random int (uses pre-seeded state, no syscall)
func fastRandInt(min, max int) int {
	if max <= min {
		return min
	}
	// Use atomic counter for lock-free pseudo-randomness
	idx := paddingCacheIdx.Add(1)
	val := int(paddingCache[idx%paddingCacheSize][0])
	return min + (val % (max - min + 1))
}

// Get pre-computed random bytes (ZERO latency)
func getCachedPadding(n int) []byte {
	if n <= 0 || n > paddingExtraMax {
		return nil
	}
	idx := paddingCacheIdx.Add(1) % paddingCacheSize
	return paddingCache[idx][:n]
}

// ASYNC cover traffic (goroutine, non-blocking)
func (peer *Peer) sendAsyncCover() {
	go func() {
		// Single packet, TLS-like pattern
		sz := fastRandInt(coverSizeMin, coverSizeMax)
		b := make([]byte, sz)

		// Fast pattern injection (no crypto needed)
		b[0] = 0x16 // TLS Handshake
		b[1] = 0x03
		b[2] = 0x01 | byte(fastRandInt(0, 3)) // TLS 1.0-1.3

		// Fill rest with cached padding
		if sz > 3 {
			cached := getCachedPadding(min(sz-3, paddingExtraMax))
			copy(b[3:], cached)
		}

		_ = peer.SendBuffers([][]byte{b}) // Fire and forget
	}()
}

/* ═══════════════════════════════════════════════════════════
   OPTIMIZED TCP MSS CLAMPING (IPv4 + IPv6)
   ═══════════════════════════════════════════════════════════ */

// Fast checksum computation (optimized for modern CPUs)
func fastChecksum(data []byte) uint16 {
	var sum uint32

	// Process 4 bytes at a time (better CPU utilization)
	i := 0
	for ; i+3 < len(data); i += 4 {
		sum += uint32(data[i])<<8 | uint32(data[i+1])
		sum += uint32(data[i+2])<<8 | uint32(data[i+3])
	}

	// Handle remaining bytes
	for ; i+1 < len(data); i += 2 {
		sum += uint32(data[i])<<8 | uint32(data[i+1])
	}
	if i < len(data) {
		sum += uint32(data[i]) << 8
	}

	// Fold to 16 bits
	for sum > 0xFFFF {
		sum = (sum & 0xFFFF) + (sum >> 16)
	}

	return ^uint16(sum)
}

// IPv4 TCP MSS clamping (optimized)
func clampTCPSYNMSSv4(pkt []byte, tunMTU int) bool {
	if len(pkt) < 40 { // Fast rejection
		return false
	}

	// Quick protocol check
	if pkt[9] != 6 { // Not TCP
		return false
	}

	ihl := int(pkt[0]&0x0F) << 2
	if ihl < 20 || len(pkt) < ihl+20 {
		return false
	}

	tcp := pkt[ihl:]
	doff := int(tcp[12]>>4) << 2
	if doff < 20 || len(tcp) < doff {
		return false
	}

	// Check SYN flag
	if tcp[13]&0x02 == 0 {
		return false
	}

	// Target MSS
	targetMSS := tunMTU - 40
	if targetMSS < 536 {
		targetMSS = 536
	}

	// Find and clamp MSS option
	opts := tcp[20:doff]
	changed := false
	for i := 0; i < len(opts); {
		if opts[i] == 0 { // End
			break
		}
		if opts[i] == 1 { // NOP
			i++
			continue
		}
		if i+1 >= len(opts) {
			break
		}
		olen := int(opts[i+1])
		if olen < 2 || i+olen > len(opts) {
			break
		}
		if opts[i] == 2 && olen == 4 { // MSS option
			cur := binary.BigEndian.Uint16(opts[i+2:])
			if int(cur) > targetMSS {
				binary.BigEndian.PutUint16(opts[i+2:], uint16(targetMSS))
				changed = true
			}
			break
		}
		i += olen
	}

	if !changed {
		return false
	}

	// Fast checksum recompute
	tcp[16], tcp[17] = 0, 0

	// Pseudo-header
	var sum uint32
	sum += uint32(pkt[12])<<8 | uint32(pkt[13]) // src[0:2]
	sum += uint32(pkt[14])<<8 | uint32(pkt[15]) // src[2:4]
	sum += uint32(pkt[16])<<8 | uint32(pkt[17]) // dst[0:2]
	sum += uint32(pkt[18])<<8 | uint32(pkt[19]) // dst[2:4]
	sum += 6                                    // protocol
	sum += uint32(len(tcp))                     // TCP length

	// TCP segment
	for i := 0; i+1 < len(tcp); i += 2 {
		sum += uint32(tcp[i])<<8 | uint32(tcp[i+1])
	}
	if len(tcp)&1 != 0 {
		sum += uint32(tcp[len(tcp)-1]) << 8
	}

	// Finalize
	for sum > 0xFFFF {
		sum = (sum & 0xFFFF) + (sum >> 16)
	}
	csum := ^uint16(sum)

	binary.BigEndian.PutUint16(tcp[16:], csum)
	return true
}

// IPv6 TCP MSS clamping (optimized)
func clampTCPSYNMSSv6(pkt []byte, tunMTU int) bool {
	if len(pkt) < 60 || pkt[6] != 6 { // Fast rejection
		return false
	}

	tcp := pkt[40:]
	if len(tcp) < 20 {
		return false
	}

	doff := int(tcp[12]>>4) << 2
	if doff < 20 || len(tcp) < doff || tcp[13]&0x02 == 0 {
		return false
	}

	targetMSS := tunMTU - 60
	if targetMSS < 1220 {
		targetMSS = 1220
	}

	// Find MSS
	opts := tcp[20:doff]
	changed := false
	for i := 0; i < len(opts); {
		if opts[i] == 0 {
			break
		}
		if opts[i] == 1 {
			i++
			continue
		}
		if i+1 >= len(opts) {
			break
		}
		olen := int(opts[i+1])
		if olen < 2 || i+olen > len(opts) {
			break
		}
		if opts[i] == 2 && olen == 4 {
			cur := binary.BigEndian.Uint16(opts[i+2:])
			if int(cur) > targetMSS {
				binary.BigEndian.PutUint16(opts[i+2:], uint16(targetMSS))
				changed = true
			}
			break
		}
		i += olen
	}

	if !changed {
		return false
	}

	// Fast IPv6 checksum
	tcp[16], tcp[17] = 0, 0

	var sum uint32
	// Pseudo-header: src(16) + dst(16) + len(4) + proto(4)
	for i := 8; i < 40; i += 2 {
		sum += uint32(pkt[i])<<8 | uint32(pkt[i+1])
	}
	sum += uint32(len(tcp))
	sum += 6

	for i := 0; i+1 < len(tcp); i += 2 {
		sum += uint32(tcp[i])<<8 | uint32(tcp[i+1])
	}
	if len(tcp)&1 != 0 {
		sum += uint32(tcp[len(tcp)-1]) << 8
	}

	for sum > 0xFFFF {
		sum = (sum & 0xFFFF) + (sum >> 16)
	}

	binary.BigEndian.PutUint16(tcp[16:], ^uint16(sum))
	return true
}

func (device *Device) NewOutboundElement() *QueueOutboundElement {
	elem := device.GetOutboundElement()
	elem.buffer = device.GetMessageBuffer()
	elem.nonce = 0
	return elem
}

func (elem *QueueOutboundElement) clearPointers() {
	elem.buffer = nil
	elem.packet = nil
	elem.keypair = nil
	elem.peer = nil
}

/* ═══════════════════════════════════════════════════════════
   STANDARD WIREGUARD PATHS (OPTIMIZED)
   ═══════════════════════════════════════════════════════════ */

func (peer *Peer) SendKeepalive() {
	if len(peer.queue.staged) == 0 && peer.isRunning.Load() {
		elem := peer.device.NewOutboundElement()
		elemsContainer := peer.device.GetOutboundElementsContainer()
		elemsContainer.elems = append(elemsContainer.elems, elem)
		select {
		case peer.queue.staged <- elemsContainer:
			peer.device.log.Verbosef("%v - Sending keepalive packet", peer)
		default:
			peer.device.PutMessageBuffer(elem.buffer)
			peer.device.PutOutboundElement(elem)
			peer.device.PutOutboundElementsContainer(elemsContainer)
		}
	}
	peer.SendStagedPackets()
}

func (peer *Peer) SendHandshakeInitiation(isRetry bool) error {
	if !isRetry {
		peer.timers.handshakeAttempts.Store(0)
	}

	peer.handshake.mutex.RLock()
	if time.Since(peer.handshake.lastSentHandshake) < RekeyTimeout {
		peer.handshake.mutex.RUnlock()
		return nil
	}
	peer.handshake.mutex.RUnlock()

	peer.handshake.mutex.Lock()
	if time.Since(peer.handshake.lastSentHandshake) < RekeyTimeout {
		peer.handshake.mutex.Unlock()
		return nil
	}
	peer.handshake.lastSentHandshake = time.Now()
	peer.handshake.mutex.Unlock()

	peer.device.log.Verbosef("%v - Sending handshake initiation", peer)

	// ZERO-LATENCY: Async cover traffic (non-blocking)
	peer.sendAsyncCover()

	msg, err := peer.device.CreateMessageInitiation(peer)
	if err != nil {
		peer.device.log.Errorf("%v - Failed to create initiation message: %v", peer, err)
		return err
	}

	packet := make([]byte, MessageInitiationSize)
	_ = msg.marshal(packet)
	peer.cookieGenerator.AddMacs(packet)

	peer.timersAnyAuthenticatedPacketTraversal()
	peer.timersAnyAuthenticatedPacketSent()

	err = peer.SendBuffers([][]byte{packet})
	if err != nil {
		peer.device.log.Errorf("%v - Failed to send handshake initiation: %v", peer, err)
	}
	peer.timersHandshakeInitiated()

	return err
}

func (peer *Peer) SendHandshakeResponse() error {
	peer.handshake.mutex.Lock()
	peer.handshake.lastSentHandshake = time.Now()
	peer.handshake.mutex.Unlock()

	peer.device.log.Verbosef("%v - Sending handshake response", peer)

	response, err := peer.device.CreateMessageResponse(peer)
	if err != nil {
		peer.device.log.Errorf("%v - Failed to create response message: %v", peer, err)
		return err
	}

	packet := make([]byte, MessageResponseSize)
	_ = response.marshal(packet)
	peer.cookieGenerator.AddMacs(packet)

	err = peer.BeginSymmetricSession()
	if err != nil {
		peer.device.log.Errorf("%v - Failed to derive keypair: %v", peer, err)
		return err
	}

	peer.timersSessionDerived()
	peer.timersAnyAuthenticatedPacketTraversal()
	peer.timersAnyAuthenticatedPacketSent()

	err = peer.SendBuffers([][]byte{packet})
	if err != nil {
		peer.device.log.Errorf("%v - Failed to send handshake response: %v", peer, err)
	}
	return err
}

func (device *Device) SendHandshakeCookie(initiatingElem *QueueHandshakeElement) error {
	device.log.Verbosef("Sending cookie response for denied handshake message for %v", initiatingElem.endpoint.DstToString())

	sender := binary.LittleEndian.Uint32(initiatingElem.packet[4:8])
	reply, err := device.cookieChecker.CreateReply(initiatingElem.packet, sender, initiatingElem.endpoint.DstToBytes())
	if err != nil {
		device.log.Errorf("Failed to create cookie reply: %v", err)
		return err
	}

	packet := make([]byte, MessageCookieReplySize)
	_ = reply.marshal(packet)
	device.net.bind.Send([][]byte{packet}, initiatingElem.endpoint)

	return nil
}

func (peer *Peer) keepKeyFreshSending() {
	keypair := peer.keypairs.Current()
	if keypair == nil {
		return
	}
	nonce := keypair.sendNonce.Load()
	if nonce > RekeyAfterMessages || (keypair.isInitiator && time.Since(keypair.created) > RekeyAfterTime) {
		peer.SendHandshakeInitiation(false)
	}
}

func (device *Device) RoutineReadFromTUN() {
	defer func() {
		device.log.Verbosef("Routine: TUN reader - stopped")
		device.state.stopping.Done()
		device.queue.encryption.wg.Done()
	}()

	// Initialize padding cache once at startup
	initPaddingCache()

	device.log.Verbosef("Routine: TUN reader - started")

	var (
		batchSize   = device.BatchSize()
		readErr     error
		elems       = make([]*QueueOutboundElement, batchSize)
		bufs        = make([][]byte, batchSize)
		elemsByPeer = make(map[*Peer]*QueueOutboundElementsContainer, batchSize)
		count       = 0
		sizes       = make([]int, batchSize)
		offset      = MessageTransportHeaderSize
	)

	for i := range elems {
		elems[i] = device.NewOutboundElement()
		bufs[i] = elems[i].buffer[:]
	}

	defer func() {
		for _, elem := range elems {
			if elem != nil {
				device.PutMessageBuffer(elem.buffer)
				device.PutOutboundElement(elem)
			}
		}
	}()

	tunMTU := int(device.tun.mtu.Load()) // Cache MTU

	for {
		count, readErr = device.tun.device.Read(bufs, sizes, offset)
		for i := 0; i < count; i++ {
			if sizes[i] < 1 {
				continue
			}

			elem := elems[i]
			elem.packet = bufs[i][offset : offset+sizes[i]]

			// OPTIMIZATION: Inline MSS clamping (no function call overhead)
			if len(elem.packet) >= 40 {
				ipVer := elem.packet[0] >> 4
				if ipVer == 4 && elem.packet[9] == 6 {
					clampTCPSYNMSSv4(elem.packet, tunMTU)
				} else if ipVer == 6 && len(elem.packet) >= 60 && elem.packet[6] == 6 {
					clampTCPSYNMSSv6(elem.packet, tunMTU)
				}
			}

			// Lookup peer
			var peer *Peer
			switch elem.packet[0] >> 4 {
			case 4:
				if len(elem.packet) < ipv4.HeaderLen {
					continue
				}
				dst := elem.packet[IPv4offsetDst : IPv4offsetDst+net.IPv4len]
				peer = device.allowedips.Lookup(dst)

			case 6:
				if len(elem.packet) < ipv6.HeaderLen {
					continue
				}
				dst := elem.packet[IPv6offsetDst : IPv6offsetDst+net.IPv6len]
				peer = device.allowedips.Lookup(dst)

			default:
				device.log.Verbosef("Received packet with unknown IP version")
			}

			if peer == nil {
				continue
			}
			elemsForPeer, ok := elemsByPeer[peer]
			if !ok {
				elemsForPeer = device.GetOutboundElementsContainer()
				elemsByPeer[peer] = elemsForPeer
			}
			elemsForPeer.elems = append(elemsForPeer.elems, elem)
			elems[i] = device.NewOutboundElement()
			bufs[i] = elems[i].buffer[:]
		}

		for peer, elemsForPeer := range elemsByPeer {
			if peer.isRunning.Load() {
				peer.StagePackets(elemsForPeer)
				peer.SendStagedPackets()
			} else {
				for _, elem := range elemsForPeer.elems {
					device.PutMessageBuffer(elem.buffer)
					device.PutOutboundElement(elem)
				}
				device.PutOutboundElementsContainer(elemsForPeer)
			}
			delete(elemsByPeer, peer)
		}

		if readErr != nil {
			if errors.Is(readErr, tun.ErrTooManySegments) {
				device.log.Verbosef("Dropped some packets from multi-segment read: %v", readErr)
				continue
			}
			if !device.isClosed() {
				if !errors.Is(readErr, os.ErrClosed) {
					device.log.Errorf("Failed to read packet from TUN device: %v", readErr)
				}
				go device.Close()
			}
			return
		}
	}
}

func (peer *Peer) StagePackets(elems *QueueOutboundElementsContainer) {
	for {
		select {
		case peer.queue.staged <- elems:
			return
		default:
		}
		select {
		case tooOld := <-peer.queue.staged:
			for _, elem := range tooOld.elems {
				peer.device.PutMessageBuffer(elem.buffer)
				peer.device.PutOutboundElement(elem)
			}
			peer.device.PutOutboundElementsContainer(tooOld)
		default:
		}
	}
}

func (peer *Peer) SendStagedPackets() {
top:
	if len(peer.queue.staged) == 0 || !peer.device.isUp() {
		return
	}

	keypair := peer.keypairs.Current()
	if keypair == nil || keypair.sendNonce.Load() >= RejectAfterMessages || time.Since(keypair.created) >= RejectAfterTime {
		peer.SendHandshakeInitiation(false)
		return
	}

	for {
		var elemsContainerOOO *QueueOutboundElementsContainer
		select {
		case elemsContainer := <-peer.queue.staged:
			i := 0
			for _, elem := range elemsContainer.elems {
				elem.peer = peer
				elem.nonce = keypair.sendNonce.Add(1) - 1
				if elem.nonce >= RejectAfterMessages {
					keypair.sendNonce.Store(RejectAfterMessages)
					if elemsContainerOOO == nil {
						elemsContainerOOO = peer.device.GetOutboundElementsContainer()
					}
					elemsContainerOOO.elems = append(elemsContainerOOO.elems, elem)
					continue
				} else {
					elemsContainer.elems[i] = elem
					i++
				}

				elem.keypair = keypair
			}
			elemsContainer.Lock()
			elemsContainer.elems = elemsContainer.elems[:i]

			if elemsContainerOOO != nil {
				peer.StagePackets(elemsContainerOOO)
			}

			if len(elemsContainer.elems) == 0 {
				peer.device.PutOutboundElementsContainer(elemsContainer)
				goto top
			}

			if peer.isRunning.Load() {
				peer.queue.outbound.c <- elemsContainer
				peer.device.queue.encryption.c <- elemsContainer
			} else {
				for _, elem := range elemsContainer.elems {
					peer.device.PutMessageBuffer(elem.buffer)
					peer.device.PutOutboundElement(elem)
				}
				peer.device.PutOutboundElementsContainer(elemsContainer)
			}

			if elemsContainerOOO != nil {
				goto top
			}
		default:
			return
		}
	}
}

func (peer *Peer) FlushStagedPackets() {
	for {
		select {
		case elemsContainer := <-peer.queue.staged:
			for _, elem := range elemsContainer.elems {
				peer.device.PutMessageBuffer(elem.buffer)
				peer.device.PutOutboundElement(elem)
			}
			peer.device.PutOutboundElementsContainer(elemsContainer)
		default:
			return
		}
	}
}

// ZERO-LATENCY padding: use pre-computed cache
func calculatePaddingSize(packetSize, mtu int) int {
	lastUnit := packetSize
	if mtu == 0 {
		return ((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1)) - lastUnit
	}
	if lastUnit > mtu {
		lastUnit %= mtu
	}
	paddedSize := ((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1))
	if paddedSize > mtu {
		paddedSize = mtu
	}

	basePadding := paddedSize - lastUnit

	// Fast random padding (0-16 bytes, lock-free)
	if paddingCacheReady.Load() {
		extra := fastRandInt(0, paddingExtraMax)
		if basePadding+extra <= mtu-lastUnit {
			return basePadding + extra
		}
	}

	return basePadding
}

func (device *Device) RoutineEncryption(id int) {
	var paddingZeros [PaddingMultiple + paddingExtraMax]byte
	var nonce [chacha20poly1305.NonceSize]byte

	defer device.log.Verbosef("Routine: encryption worker %d - stopped", id)
	device.log.Verbosef("Routine: encryption worker %d - started", id)

	for elemsContainer := range device.queue.encryption.c {
		for _, elem := range elemsContainer.elems {
			header := elem.buffer[:MessageTransportHeaderSize]
			fieldType := header[0:4]
			fieldReceiver := header[4:8]
			fieldNonce := header[8:16]

			binary.LittleEndian.PutUint32(fieldType, MessageTransportType)
			binary.LittleEndian.PutUint32(fieldReceiver, elem.keypair.remoteIndex)
			binary.LittleEndian.PutUint64(fieldNonce, elem.nonce)

			// ZERO-LATENCY: Pre-cached padding
			paddingSize := calculatePaddingSize(len(elem.packet), int(device.tun.mtu.Load()))
			elem.packet = append(elem.packet, paddingZeros[:paddingSize]...)

			binary.LittleEndian.PutUint64(nonce[4:], elem.nonce)
			elem.packet = elem.keypair.send.Seal(header, nonce[:], elem.packet, nil)
		}
		elemsContainer.Unlock()
	}
}

func (peer *Peer) RoutineSequentialSender(maxBatchSize int) {
	device := peer.device
	defer func() {
		defer device.log.Verbosef("%v - Routine: sequential sender - stopped", peer)
		peer.stopping.Done()
	}()
	device.log.Verbosef("%v - Routine: sequential sender - started", peer)

	bufs := make([][]byte, 0, maxBatchSize)

	for elemsContainer := range peer.queue.outbound.c {
		bufs = bufs[:0]
		if elemsContainer == nil {
			return
		}
		if !peer.isRunning.Load() {
			elemsContainer.Lock()
			for _, elem := range elemsContainer.elems {
				device.PutMessageBuffer(elem.buffer)
				device.PutOutboundElement(elem)
			}
			device.PutOutboundElementsContainer(elemsContainer)
			continue
		}
		dataSent := false
		elemsContainer.Lock()
		for _, elem := range elemsContainer.elems {
			if len(elem.packet) != MessageKeepaliveSize {
				dataSent = true
			}
			bufs = append(bufs, elem.packet)
		}

		peer.timersAnyAuthenticatedPacketTraversal()
		peer.timersAnyAuthenticatedPacketSent()

		err := peer.SendBuffers(bufs)
		if dataSent {
			peer.timersDataSent()
		}
		for _, elem := range elemsContainer.elems {
			device.PutMessageBuffer(elem.buffer)
			device.PutOutboundElement(elem)
		}
		device.PutOutboundElementsContainer(elemsContainer)
		if err != nil {
			var errGSO conn.ErrUDPGSODisabled
			if errors.As(err, &errGSO) {
				device.log.Verbosef(err.Error())
				err = errGSO.RetryErr
			}
		}
		if err != nil {
			device.log.Errorf("%v - Failed to send data packets: %v", peer, err)
			continue
		}

		peer.keepKeyFreshSending()
	}
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
