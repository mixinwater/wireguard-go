package device

import (
	"crypto/rand"
	"encoding/binary"
	"errors"
	"math/big"
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

type sizeProfile int

const (
	profileSmall  sizeProfile = 256
	profileMedium sizeProfile = 512
	profileLarge  sizeProfile = 1024
	profileJumbo  sizeProfile = 1200
)

var sizeProfiles = [4]sizeProfile{profileSmall, profileMedium, profileLarge, profileJumbo}

type obfuscationState struct {
	sizeProfile     sizeProfile
	lastRealTraffic int64
	coinCounter     uint32
}

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

const (
	coverSizeMin = 16
	coverSizeMax = 32
)

var (
	peerObfuscation   = make(map[*Peer]*obfuscationState)
	peerObfuscationMu sync.RWMutex
)

func getPeerObfuscation(peer *Peer) *obfuscationState {
	peerObfuscationMu.RLock()
	state := peerObfuscation[peer]
	peerObfuscationMu.RUnlock()
	return state
}

func initPeerObfuscation(peer *Peer) *obfuscationState {
	peerObfuscationMu.Lock()
	defer peerObfuscationMu.Unlock()

	if state, ok := peerObfuscation[peer]; ok {
		return state
	}

	state := &obfuscationState{}
	var profileIndex [1]byte
	rand.Read(profileIndex[:])
	state.sizeProfile = sizeProfiles[int(profileIndex[0])&3]
	state.lastRealTraffic = time.Now().Unix()
	peerObfuscation[peer] = state
	return state
}

func cleanupPeerObfuscation(peer *Peer) {
	peerObfuscationMu.Lock()
	delete(peerObfuscation, peer)
	peerObfuscationMu.Unlock()
}

func shouldSendCamouflage(peer *Peer) bool {
	state := getPeerObfuscation(peer)
	if state == nil {
		return false
	}
	now := time.Now().Unix()
	lastTraffic := atomic.LoadInt64(&state.lastRealTraffic)
	if now-lastTraffic > 60 {
		return false
	}
	counter := atomic.AddUint32(&state.coinCounter, 1)
	return (counter & 0xFF) == 0
}

func sendCamouflagePacket(peer *Peer) {
	state := getPeerObfuscation(peer)
	if state == nil {
		return
	}
	targetSize := int(state.sizeProfile)
	b := make([]byte, targetSize)
	rand.Read(b)
	peer.SendBuffers([][]byte{b})
}

func crandInt(min, max int) (int, error) {
	if max <= min {
		return min, nil
	}
	n, err := rand.Int(rand.Reader, big.NewInt(int64(max-min+1)))
	if err != nil {
		return 0, err
	}
	return min + int(n.Int64()), nil
}

func sendHandshakePrePackets(peer *Peer) {
	sz, _ := crandInt(coverSizeMin, coverSizeMax)
	if sz > 0 {
		b := make([]byte, sz)
		rand.Read(b)
		peer.SendBuffers([][]byte{b})
	}
}

func padToProfileFast(pkt []byte, profile sizeProfile, maxSize int) []byte {
	targetSize := int(profile)
	if targetSize > maxSize {
		targetSize = maxSize
	}
	currentSize := len(pkt)
	if currentSize >= targetSize {
		return pkt
	}
	paddingSize := targetSize - currentSize
	if cap(pkt) >= targetSize {
		pkt = pkt[:targetSize]
		for i := currentSize; i < targetSize; i++ {
			pkt[i] = 0
		}
		return pkt
	}
	return append(pkt, make([]byte, paddingSize)...)
}

func onesComplementSum(data []byte) uint32 {
	var sum uint32
	for len(data) >= 2 {
		sum += uint32(binary.BigEndian.Uint16(data[:2]))
		data = data[2:]
	}
	if len(data) == 1 {
		sum += uint32(uint16(data[0]) << 8)
	}
	return sum
}

func finalizeChecksum(sum uint32) uint16 {
	for (sum >> 16) != 0 {
		sum = (sum & 0xFFFF) + (sum >> 16)
	}
	return ^uint16(sum)
}

func clampTCPMSSv4(pkt []byte, tunMTU int) bool {
	if len(pkt) < ipv4.HeaderLen {
		return false
	}
	ihl := int((pkt[0] & 0x0F) << 2)
	if ihl < ipv4.HeaderLen || len(pkt) < ihl+20 {
		return false
	}
	if pkt[9] != 6 {
		return false
	}
	totalLen := int(binary.BigEndian.Uint16(pkt[2:4]))
	if totalLen == 0 || totalLen > len(pkt) {
		totalLen = len(pkt)
	}
	ipHdr := pkt[:ihl]
	tcp := pkt[ihl:totalLen]
	if len(tcp) < 20 {
		return false
	}
	dataOffset := int((tcp[12] >> 4) * 4)
	if dataOffset < 20 || len(tcp) < dataOffset {
		return false
	}
	if (tcp[13] & 0x02) == 0 {
		return false
	}
	targetMSS := tunMTU - 40
	if targetMSS < 536 {
		targetMSS = 536
	}
	opts := tcp[20:dataOffset]
	changed := false
	i := 0
	for i < len(opts) {
		kind := opts[i]
		if kind == 0 {
			break
		}
		if kind == 1 {
			i++
			continue
		}
		if i+1 >= len(opts) {
			break
		}
		optLen := int(opts[i+1])
		if optLen < 2 || i+optLen > len(opts) {
			break
		}
		if kind == 2 && optLen == 4 {
			currentMSS := binary.BigEndian.Uint16(opts[i+2 : i+4])
			if int(currentMSS) > targetMSS {
				binary.BigEndian.PutUint16(opts[i+2:i+4], uint16(targetMSS))
				changed = true
			}
			break
		}
		i += optLen
	}
	if !changed {
		return false
	}
	tcp[16] = 0
	tcp[17] = 0
	srcIP := ipHdr[12:16]
	dstIP := ipHdr[16:20]
	tcpLen := uint16(len(tcp))
	var sum uint32
	pseudoHeader := make([]byte, 12)
	copy(pseudoHeader[0:4], srcIP)
	copy(pseudoHeader[4:8], dstIP)
	pseudoHeader[8] = 0
	pseudoHeader[9] = 6
	binary.BigEndian.PutUint16(pseudoHeader[10:12], tcpLen)
	sum += onesComplementSum(pseudoHeader)
	sum += onesComplementSum(tcp)
	checksum := finalizeChecksum(sum)
	binary.BigEndian.PutUint16(tcp[16:18], checksum)
	return true
}

func clampTCPMSSv6(pkt []byte, tunMTU int) bool {
	if len(pkt) < 60 || pkt[6] != 6 {
		return false
	}
	tcp := pkt[40:]
	if len(tcp) < 20 {
		return false
	}
	dataOffset := int((tcp[12] >> 4) * 4)
	if dataOffset < 20 || len(tcp) < dataOffset {
		return false
	}
	if tcp[13]&0x02 == 0 {
		return false
	}
	targetMSS := tunMTU - 60
	if targetMSS < 1220 {
		targetMSS = 1220
	}
	opts := tcp[20:dataOffset]
	changed := false
	i := 0
	for i < len(opts) {
		kind := opts[i]
		if kind == 0 {
			break
		}
		if kind == 1 {
			i++
			continue
		}
		if i+1 >= len(opts) {
			break
		}
		optLen := int(opts[i+1])
		if optLen < 2 || i+optLen > len(opts) {
			break
		}
		if kind == 2 && optLen == 4 {
			currentMSS := binary.BigEndian.Uint16(opts[i+2 : i+4])
			if int(currentMSS) > targetMSS {
				binary.BigEndian.PutUint16(opts[i+2:i+4], uint16(targetMSS))
				changed = true
			}
			break
		}
		i += optLen
	}
	if !changed {
		return false
	}
	tcp[16] = 0
	tcp[17] = 0
	var sum uint32
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
	go sendHandshakePrePackets(peer)
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
	tunMTU := int(device.tun.mtu.Load())
	for {
		count, readErr = device.tun.device.Read(bufs, sizes, offset)
		for i := 0; i < count; i++ {
			if sizes[i] < 1 {
				continue
			}
			elem := elems[i]
			elem.packet = bufs[i][offset : offset+sizes[i]]
			if len(elem.packet) >= 40 {
				ipVersion := elem.packet[0] >> 4
				if ipVersion == 4 {
					clampTCPMSSv4(elem.packet, tunMTU)
				} else if ipVersion == 6 && len(elem.packet) >= 60 {
					clampTCPMSSv6(elem.packet, tunMTU)
				}
			}
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
			state := initPeerObfuscation(peer)
			atomic.StoreInt64(&state.lastRealTraffic, time.Now().Unix())
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
				if shouldSendCamouflage(peer) {
					go sendCamouflagePacket(peer)
				}
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
	return paddedSize - lastUnit
}

func (device *Device) RoutineEncryption(id int) {
	var paddingZeros [PaddingMultiple]byte
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
			paddingSize := calculatePaddingSize(len(elem.packet), int(device.tun.mtu.Load()))
			elem.packet = append(elem.packet, paddingZeros[:paddingSize]...)
			if elem.peer != nil {
				if state := getPeerObfuscation(elem.peer); state != nil {
					tunMTU := int(device.tun.mtu.Load())
					maxSafeSize := tunMTU - MessageTransportHeaderSize - chacha20poly1305.Overhead
					elem.packet = padToProfileFast(elem.packet, state.sizeProfile, maxSafeSize)
				}
			}
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
		cleanupPeerObfuscation(peer)
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