package device

import (
	"context"
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

// ---------------------------------------------------------------------------
// Obfuscation types and constants
// ---------------------------------------------------------------------------

type sizeProfile int

const (
	profileSmall  sizeProfile = 256
	profileMedium sizeProfile = 512
	profileLarge  sizeProfile = 1024
	profileJumbo  sizeProfile = 1200
)

var sizeProfiles = [4]sizeProfile{profileSmall, profileMedium, profileLarge, profileJumbo}

type obfuscationState struct {
	sizeProfile                 sizeProfile
	lastRealTraffic             int64
	lastSuccessfulSend          int64
	lastPatternChange           int64
	lastKeepalive               int64
	lastReceived                int64
	lastHandshake               int64
	lastHandshakeResponse       int64
	lastRecoveryAttempt         int64
	coinCounter                 uint32
	successCount                uint32
	totalCount                  uint32
	failureStreak               uint32
	profileRotation             int64
	burstCounter                uint32
	lastBurst                   int64
	timeJitter                  int32
	paddingVariance             int32
	prePacketCount              int32
	camouflageFreq              int32
	lastHealthCheck             int64
	activePattern               int32
	recoveryMode                int32
	connectionStale             int32
	forceRehandshake            int32
	recoveryAttempts            uint32
	handshakeAttempts           uint32
	consecutiveFailedHandshakes uint32
	randomizedObfuscation       int32
	recoveryStartTime           int64  // when recovery mode was entered
	lastRehandshakeBackoff      int64  // tracks backoff for forced rehandshakes
	rehandshakeBackoffSecs      int32  // current backoff duration in seconds
}

// ---------------------------------------------------------------------------
// Core WireGuard types
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Obfuscation constants — tuned for stability
// ---------------------------------------------------------------------------

const (
	coverSizeMin               = 16
	coverSizeMax               = 64
	profileRotationInterval    = 120
	burstWindow                = 3
	burstThreshold             = 15
	trafficTimeoutNormal       = 15
	trafficTimeoutRecovery     = 8
	failureStreakThreshold     = 5  // raised from 3 to reduce false recovery triggers
	obfKeepaliveInterval       = 8
	idleTimeout                = 60
	staleConnectionTimeout     = 45 // raised from 25 to allow more time before declaring stale
	probeInterval              = 5
	handshakeTimeout           = 35
	handshakeResponseTimeout   = 10
	recoveryCheckInterval      = 2  // raised from 1 to reduce CPU usage
	maxRecoveryAttempts        = 5  // raised from 3 for more chances
	aggressiveRecoveryInterval = 30 // raised from 20 to reduce churn
	handshakeBlockedThreshold  = 5
	minPatternChangeInterval   = 30 // minimum seconds between pattern changes
	maxRecoveryDuration        = 300 // 5 minutes max in recovery mode
	initialRehandshakeBackoff  = 5  // start at 5 seconds
	maxRehandshakeBackoff      = 60 // cap at 60 seconds
)

// ---------------------------------------------------------------------------
// Fast non-cryptographic randomness (uses WireGuard's existing fastrandn)
// ---------------------------------------------------------------------------

// fastRandRange returns a random int in [min, max] using fastrandn.
// NOT cryptographically secure — suitable for padding, timing jitter, etc.
func fastRandRange(min, max int) int {
	if max <= min {
		return min
	}
	return min + int(fastrandn(uint32(max-min+1)))
}

// crandBytes fills b with cryptographically secure random bytes.
// Used only for camouflage packet content where randomness quality matters.
func crandBytes(b []byte) {
	rand.Read(b)
}

// ---------------------------------------------------------------------------
// Peer-local obfuscation state management (replaces global map)
// ---------------------------------------------------------------------------

func ensurePeerObfuscation(peer *Peer) *obfuscationState {
	if state := peer.obfState.Load(); state != nil {
		return state
	}

	// Use sync.Once to ensure exactly one initialization per peer lifecycle
	peer.obfInitOnce.Do(func() {
		state := &obfuscationState{}
		state.sizeProfile = sizeProfiles[fastrandn(4)]
		now := time.Now().Unix()
		state.lastRealTraffic = now
		state.lastSuccessfulSend = now
		state.lastPatternChange = now
		state.lastKeepalive = now
		state.lastReceived = now
		state.lastHandshake = now
		state.lastHandshakeResponse = now
		state.lastRecoveryAttempt = now
		state.profileRotation = now
		state.lastHealthCheck = now
		state.timeJitter = 1
		state.paddingVariance = 160
		state.prePacketCount = 3
		state.camouflageFreq = 6
		state.rehandshakeBackoffSecs = initialRehandshakeBackoff

		peer.obfState.Store(state)

		peer.device.log.Verbosef("OBF: Initialized obfuscation for peer %v - Profile: %d, RANDOMIZED MODE", peer, state.sizeProfile)

		ctx, cancel := context.WithCancel(context.Background())
		peer.obfCancel = cancel
		go monitorConnectionHealth(ctx, peer, state)
	})

	return peer.obfState.Load()
}

func getPeerObfuscation(peer *Peer) *obfuscationState {
	return peer.obfState.Load()
}

// ---------------------------------------------------------------------------
// Connection health monitor (runs as a goroutine per peer)
// ---------------------------------------------------------------------------

func monitorConnectionHealth(ctx context.Context, peer *Peer, state *obfuscationState) {
	ticker := time.NewTicker(time.Duration(recoveryCheckInterval) * time.Second)
	defer ticker.Stop()

	peer.device.log.Verbosef("OBF: Started connection monitor for peer %v", peer)

	for {
		select {
		case <-ctx.Done():
			peer.device.log.Verbosef("OBF: Stopping connection monitor for peer %v (context cancelled)", peer)
			return
		case <-ticker.C:
		}

		if !peer.isRunning.Load() {
			peer.device.log.Verbosef("OBF: Stopping connection monitor for peer %v", peer)
			return
		}

		now := time.Now().Unix()
		lastReceived := atomic.LoadInt64(&state.lastReceived)
		lastHandshake := atomic.LoadInt64(&state.lastHandshake)
		lastHandshakeResponse := atomic.LoadInt64(&state.lastHandshakeResponse)
		lastSuccess := atomic.LoadInt64(&state.lastSuccessfulSend)
		lastRecovery := atomic.LoadInt64(&state.lastRecoveryAttempt)
		recoveryMode := atomic.LoadInt32(&state.recoveryMode)

		timeSinceReceived := now - lastReceived
		timeSinceSuccess := now - lastSuccess
		timeSinceHandshake := now - lastHandshake
		timeSinceHandshakeResponse := now - lastHandshakeResponse

		// --- Recovery mode timeout: exit after maxRecoveryDuration ---
		if recoveryMode > 0 {
			recoveryStart := atomic.LoadInt64(&state.recoveryStartTime)
			if recoveryStart > 0 && now-recoveryStart > maxRecoveryDuration {
				peer.device.log.Verbosef("OBF: Recovery mode timeout after %ds, resetting to normal mode", now-recoveryStart)
				exitRecoveryMode(state)
			}
		}

		// --- Detect handshake blocking ---
		failedHandshakes := atomic.LoadUint32(&state.consecutiveFailedHandshakes)
		if failedHandshakes >= handshakeBlockedThreshold {
			peer.device.log.Verbosef("OBF: HANDSHAKE BLOCKING DETECTED - %d consecutive failures, enabling randomized obfuscation", failedHandshakes)
			atomic.StoreInt32(&state.randomizedObfuscation, 1)
			atomic.StoreUint32(&state.consecutiveFailedHandshakes, 0)
			enterRecoveryMode(state, peer)
			delay := fastRandRange(500, 2000)
			time.Sleep(time.Duration(delay) * time.Millisecond)
		}

		// --- Detect handshake timeouts ---
		if timeSinceHandshake < handshakeResponseTimeout && timeSinceHandshakeResponse > handshakeResponseTimeout && timeSinceHandshake > 5 {
			attempts := atomic.AddUint32(&state.handshakeAttempts, 1)
			if attempts > 3 {
				peer.device.log.Verbosef("OBF: Handshakes timing out (%d attempts), likely being blocked", attempts)
				failedCount := atomic.AddUint32(&state.consecutiveFailedHandshakes, 1)
				if failedCount >= handshakeBlockedThreshold {
					atomic.StoreInt32(&state.randomizedObfuscation, 1)
					peer.device.log.Verbosef("OBF: ENABLING RANDOMIZED OBFUSCATION MODE")
				}
			}
		}

		// --- Detect stale connection ---
		if timeSinceReceived > staleConnectionTimeout {
			if atomic.CompareAndSwapInt32(&state.connectionStale, 0, 1) {
				peer.device.log.Verbosef("OBF: STALE CONNECTION DETECTED - No RX for %ds, triggering recovery", timeSinceReceived)
				enterRecoveryMode(state, peer)
				atomic.StoreInt32(&state.randomizedObfuscation, 1)
				changeObfuscationPattern(state, true)
				requestRehandshake(state, peer, now)
			}
		}

		// --- Detect traffic timeout ---
		if timeSinceSuccess > trafficTimeoutNormal {
			if recoveryMode == 0 {
				peer.device.log.Verbosef("OBF: Traffic timeout detected (%ds without successful send), entering recovery mode", timeSinceSuccess)
				enterRecoveryMode(state, peer)
				changeObfuscationPattern(state, true)
				requestRehandshake(state, peer, now)
			}
		}

		// --- Detect handshake timeout ---
		if timeSinceHandshake > handshakeTimeout {
			peer.device.log.Verbosef("OBF: Handshake timeout (%ds), requesting rehandshake", timeSinceHandshake)
			requestRehandshake(state, peer, now)
		}

		// --- Aggressive recovery with backoff ---
		if recoveryMode > 0 && now-lastRecovery > aggressiveRecoveryInterval {
			attempts := atomic.AddUint32(&state.recoveryAttempts, 1)
			atomic.StoreInt64(&state.lastRecoveryAttempt, now)

			peer.device.log.Verbosef("OBF: AGGRESSIVE RECOVERY attempt #%d (RX: %ds ago, TX: %ds ago)",
				attempts, timeSinceReceived, timeSinceSuccess)

			changeObfuscationPattern(state, true)
			requestRehandshake(state, peer, now)

			if attempts >= maxRecoveryAttempts {
				peer.device.log.Verbosef("OBF: Maximum recovery attempts reached, switching to full randomization")
				atomic.StoreInt32(&state.randomizedObfuscation, 1)
				atomic.StoreUint32(&state.recoveryAttempts, 0)
			}
		}

		// --- Execute pending rehandshake with backoff ---
		if atomic.LoadInt32(&state.forceRehandshake) > 0 {
			backoff := atomic.LoadInt32(&state.rehandshakeBackoffSecs)
			lastBackoff := atomic.LoadInt64(&state.lastRehandshakeBackoff)
			if now-lastBackoff >= int64(backoff) {
				atomic.StoreInt32(&state.forceRehandshake, 0)
				atomic.StoreInt64(&state.lastRehandshakeBackoff, now)
				atomic.StoreInt64(&state.lastHandshake, now)

				// Exponential backoff: double the interval, cap at max
				newBackoff := backoff * 2
				if newBackoff > maxRehandshakeBackoff {
					newBackoff = maxRehandshakeBackoff
				}
				atomic.StoreInt32(&state.rehandshakeBackoffSecs, newBackoff)

				peer.device.log.Verbosef("OBF: Forcing handshake initiation (next backoff: %ds)", newBackoff)
				peer.SendHandshakeInitiation(true)
			}
		}

		// --- Keepalive probing ---
		lastKeepalive := atomic.LoadInt64(&state.lastKeepalive)
		if now-lastKeepalive > obfKeepaliveInterval {
			atomic.StoreInt64(&state.lastKeepalive, now)
			peer.SendKeepalive()
		}

		// --- Idle probing ---
		lastRealTraffic := atomic.LoadInt64(&state.lastRealTraffic)
		if now-lastRealTraffic > idleTimeout && now-lastKeepalive > probeInterval {
			atomic.StoreInt64(&state.lastKeepalive, now)
			peer.SendKeepalive()
		}
	}
}

// enterRecoveryMode transitions to recovery mode, recording the start time.
func enterRecoveryMode(state *obfuscationState, peer *Peer) {
	if atomic.CompareAndSwapInt32(&state.recoveryMode, 0, 1) {
		atomic.StoreInt64(&state.recoveryStartTime, time.Now().Unix())
		atomic.StoreInt32(&state.rehandshakeBackoffSecs, initialRehandshakeBackoff)
		peer.device.log.Verbosef("OBF: Entering recovery mode")
	}
}

// exitRecoveryMode cleanly exits recovery mode and resets counters.
func exitRecoveryMode(state *obfuscationState) {
	atomic.StoreInt32(&state.recoveryMode, 0)
	atomic.StoreInt32(&state.randomizedObfuscation, 0)
	atomic.StoreUint32(&state.recoveryAttempts, 0)
	atomic.StoreInt64(&state.recoveryStartTime, 0)
	atomic.StoreInt32(&state.rehandshakeBackoffSecs, initialRehandshakeBackoff)
}

// requestRehandshake sets the rehandshake flag (actual execution is gated by backoff).
func requestRehandshake(state *obfuscationState, peer *Peer, now int64) {
	atomic.StoreInt32(&state.forceRehandshake, 1)
}

// ---------------------------------------------------------------------------
// Receive-side hooks (called from receive.go)
// ---------------------------------------------------------------------------

// MarkReceivedTraffic should be called whenever valid data is received from the peer.
// This is the critical hook that keeps the health monitor from falsely triggering recovery.
func MarkReceivedTraffic(peer *Peer) {
	state := getPeerObfuscation(peer)
	if state == nil {
		return
	}

	now := time.Now().Unix()
	lastReceived := atomic.LoadInt64(&state.lastReceived)

	if now-lastReceived > 5 {
		peer.device.log.Verbosef("OBF: Received traffic from server (gap: %ds)", now-lastReceived)
	}

	atomic.StoreInt64(&state.lastReceived, now)
	atomic.StoreInt64(&state.lastHandshakeResponse, now)
	atomic.StoreUint32(&state.handshakeAttempts, 0)
	atomic.StoreUint32(&state.consecutiveFailedHandshakes, 0)
	wasStale := atomic.SwapInt32(&state.connectionStale, 0)

	if wasStale > 0 {
		peer.device.log.Verbosef("OBF: Connection recovered from stale state")
	}

	// Reset rehandshake backoff on successful receive
	atomic.StoreInt32(&state.rehandshakeBackoffSecs, initialRehandshakeBackoff)

	// Check if we can exit recovery mode
	recoveryMode := atomic.LoadInt32(&state.recoveryMode)
	if recoveryMode > 0 {
		total := atomic.LoadUint32(&state.totalCount)
		successCount := atomic.LoadUint32(&state.successCount)
		if total > 100 {
			ratio := float64(successCount) / float64(total)
			if ratio > 0.95 {
				peer.device.log.Verbosef("OBF: Exiting recovery mode - connection stable (%.1f%% success)", ratio*100)
				exitRecoveryMode(state)
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Pattern management
// ---------------------------------------------------------------------------

func changeObfuscationPattern(state *obfuscationState, randomize bool) {
	now := time.Now().Unix()
	lastChange := atomic.LoadInt64(&state.lastPatternChange)

	// Rate-limit pattern changes to prevent thrashing
	if now-lastChange < minPatternChangeInterval {
		return
	}
	atomic.StoreInt64(&state.lastPatternChange, now)

	if randomize || atomic.LoadInt32(&state.randomizedObfuscation) > 0 {
		atomic.StoreInt32(&state.paddingVariance, int32(fastRandRange(128, 320)))
		atomic.StoreInt32(&state.prePacketCount, int32(fastRandRange(2, 7)))
		atomic.StoreInt32(&state.camouflageFreq, int32(fastRandRange(4, 8)))
		atomic.StoreInt32(&state.timeJitter, int32(fastRandRange(0, 4)))
		atomic.AddInt32(&state.activePattern, 1)
	} else {
		pattern := atomic.AddInt32(&state.activePattern, 1) % 4

		switch pattern {
		case 0:
			atomic.StoreInt32(&state.paddingVariance, 160)
			atomic.StoreInt32(&state.prePacketCount, 3)
			atomic.StoreInt32(&state.camouflageFreq, 6)
			atomic.StoreInt32(&state.timeJitter, 1)
		case 1:
			atomic.StoreInt32(&state.paddingVariance, 256)
			atomic.StoreInt32(&state.prePacketCount, 4)
			atomic.StoreInt32(&state.camouflageFreq, 5)
			atomic.StoreInt32(&state.timeJitter, 2)
		case 2:
			atomic.StoreInt32(&state.paddingVariance, 192)
			atomic.StoreInt32(&state.prePacketCount, 2)
			atomic.StoreInt32(&state.camouflageFreq, 7)
			atomic.StoreInt32(&state.timeJitter, 1)
		case 3:
			atomic.StoreInt32(&state.paddingVariance, 224)
			atomic.StoreInt32(&state.prePacketCount, 5)
			atomic.StoreInt32(&state.camouflageFreq, 4)
			atomic.StoreInt32(&state.timeJitter, 3)
		}
	}

	rotateProfile(state)
}

func updateStats(state *obfuscationState, success bool, peer *Peer) {
	total := atomic.AddUint32(&state.totalCount, 1)

	if success {
		atomic.AddUint32(&state.successCount, 1)
		atomic.StoreUint32(&state.failureStreak, 0)
		atomic.StoreInt64(&state.lastSuccessfulSend, time.Now().Unix())
	} else {
		streak := atomic.AddUint32(&state.failureStreak, 1)

		if streak >= failureStreakThreshold {
			peer.device.log.Verbosef("OBF: Failure streak reached %d, triggering recovery", streak)
			enterRecoveryMode(state, peer)
			changeObfuscationPattern(state, true)
			requestRehandshake(state, peer, time.Now().Unix())
		}
	}

	if total%50 == 0 {
		successCount := atomic.LoadUint32(&state.successCount)
		ratio := float64(successCount) / float64(total)

		peer.device.log.Verbosef("OBF: Stats - Success rate: %.1f%% (%d/%d)", ratio*100, successCount, total)

		if ratio < 0.5 {
			peer.device.log.Verbosef("OBF: Low success rate detected, entering recovery")
			enterRecoveryMode(state, peer)
			changeObfuscationPattern(state, true)
		}
	}

	if total > 1000000 {
		atomic.StoreUint32(&state.successCount, 0)
		atomic.StoreUint32(&state.totalCount, 0)
	}
}

func shouldRotateProfile(state *obfuscationState, now int64) bool {
	lastRotation := atomic.LoadInt64(&state.profileRotation)

	recoveryMode := atomic.LoadInt32(&state.recoveryMode)
	interval := int64(profileRotationInterval)
	if recoveryMode > 0 {
		interval = 45
	}

	if now-lastRotation > interval {
		atomic.StoreInt64(&state.profileRotation, now)
		return true
	}
	return false
}

func rotateProfile(state *obfuscationState) {
	// Simple modular rotation — no infinite loop
	currentIdx := int(fastrandn(4))
	for _, p := range sizeProfiles {
		if p == state.sizeProfile {
			break
		}
		currentIdx++
	}
	// Pick a different profile by advancing 1-3 positions
	advance := 1 + int(fastrandn(3))
	newIdx := (currentIdx + advance) % 4
	state.sizeProfile = sizeProfiles[newIdx]
}

func logObfuscationSettings(peer *Peer, state *obfuscationState) {
	pattern := atomic.LoadInt32(&state.activePattern)
	variance := atomic.LoadInt32(&state.paddingVariance)
	prePackets := atomic.LoadInt32(&state.prePacketCount)
	camouflageFreq := atomic.LoadInt32(&state.camouflageFreq)
	jitter := atomic.LoadInt32(&state.timeJitter)
	randomized := atomic.LoadInt32(&state.randomizedObfuscation)

	if randomized > 0 {
		peer.device.log.Verbosef("OBF: RANDOMIZED Pattern %d - Profile:%d Variance:%d PrePkts:%d CamoFreq:%d Jitter:%d",
			pattern, state.sizeProfile, variance, prePackets, camouflageFreq, jitter)
	} else {
		peer.device.log.Verbosef("OBF: Pattern %d activated - Profile:%d Variance:%d PrePkts:%d CamoFreq:%d Jitter:%d",
			pattern, state.sizeProfile, variance, prePackets, camouflageFreq, jitter)
	}
}

// ---------------------------------------------------------------------------
// Burst detection and camouflage
// ---------------------------------------------------------------------------

func detectBurstTraffic(state *obfuscationState, now int64) bool {
	lastBurst := atomic.LoadInt64(&state.lastBurst)

	if now-lastBurst > burstWindow {
		atomic.StoreUint32(&state.burstCounter, 0)
		atomic.StoreInt64(&state.lastBurst, now)
	}

	count := atomic.AddUint32(&state.burstCounter, 1)
	return count > burstThreshold
}

func shouldSendCamouflage(peer *Peer, state *obfuscationState, now int64) bool {
	lastTraffic := atomic.LoadInt64(&state.lastRealTraffic)

	recoveryMode := atomic.LoadInt32(&state.recoveryMode)
	timeout := int64(45)
	if recoveryMode > 0 {
		timeout = 30
	}

	if now-lastTraffic > timeout {
		return false
	}

	if detectBurstTraffic(state, now) {
		return false
	}

	counter := atomic.AddUint32(&state.coinCounter, 1)
	freq := atomic.LoadInt32(&state.camouflageFreq)
	mask := uint32((1 << freq) - 1)

	return (counter & mask) == 0
}

// sendCamouflagePacket sends a structurally valid WireGuard keepalive-sized
// packet through the normal pipeline instead of raw random bytes.
// This makes it indistinguishable from real WireGuard traffic to DPI.
func sendCamouflagePacket(peer *Peer) {
	state := getPeerObfuscation(peer)
	if state == nil {
		return
	}

	// Send a keepalive through the normal path — this produces a properly
	// encrypted, structurally valid WireGuard transport message.
	peer.SendKeepalive()
}

// ---------------------------------------------------------------------------
// Pre-handshake packets
// ---------------------------------------------------------------------------

func sendHandshakePrePackets(peer *Peer) {
	state := getPeerObfuscation(peer)
	if state == nil {
		return
	}

	randomized := atomic.LoadInt32(&state.randomizedObfuscation)

	var numPackets int
	var minDelay, maxDelay int
	var minSize, maxSize int

	if randomized > 0 {
		numPackets = fastRandRange(3, 8)
		minDelay = fastRandRange(10, 50)
		maxDelay = fastRandRange(50, 150)
		minSize = fastRandRange(coverSizeMin, coverSizeMin+20)
		maxSize = fastRandRange(coverSizeMax-10, coverSizeMax+20)

		peer.device.log.Verbosef("OBF: Sending %d RANDOMIZED pre-handshake packets (delay %d-%dms, size %d-%d)",
			numPackets, minDelay, maxDelay, minSize, maxSize)
	} else {
		numPackets = int(atomic.LoadInt32(&state.prePacketCount))
		variance := fastRandRange(-1, 1)
		numPackets += variance
		if numPackets < 2 {
			numPackets = 2
		}
		if numPackets > 6 {
			numPackets = 6
		}
		minSize = coverSizeMin
		maxSize = coverSizeMax
		minDelay = 10
		jitter := atomic.LoadInt32(&state.timeJitter)
		maxDelay = 30 + int(jitter)*20

		peer.device.log.Verbosef("OBF: Sending %d pre-handshake packets", numPackets)
	}

	for i := 0; i < numPackets; i++ {
		sz := fastRandRange(minSize, maxSize)
		if sz > 0 {
			b := make([]byte, sz)
			crandBytes(b)
			peer.SendBuffers([][]byte{b})
		}

		if i < numPackets-1 {
			delay := fastRandRange(minDelay, maxDelay)
			if delay > 0 {
				time.Sleep(time.Duration(delay) * time.Millisecond)
			}
		}
	}
}

// ---------------------------------------------------------------------------
// Smart padding
// ---------------------------------------------------------------------------

func padToProfileSmart(pkt []byte, state *obfuscationState, maxSize int, peer *Peer) []byte {
	targetSize := int(state.sizeProfile)

	variance := int(atomic.LoadInt32(&state.paddingVariance))
	vrand := fastRandRange(-variance, variance)
	targetSize += vrand

	if targetSize > maxSize {
		targetSize = maxSize
	}

	currentSize := len(pkt)
	if currentSize >= targetSize {
		return pkt
	}

	// Clamp to buffer capacity to avoid allocation
	if targetSize > cap(pkt) {
		targetSize = cap(pkt)
	}

	if currentSize >= targetSize {
		return pkt
	}

	pkt = pkt[:targetSize]
	// Zero-fill the padding region
	for i := currentSize; i < targetSize; i++ {
		pkt[i] = 0
	}
	return pkt
}

// ---------------------------------------------------------------------------
// TCP MSS clamping (unchanged — correct implementation)
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Core WireGuard send pipeline
// ---------------------------------------------------------------------------

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

	state := getPeerObfuscation(peer)
	if state != nil {
		atomic.StoreInt64(&state.lastHandshake, time.Now().Unix())
		logObfuscationSettings(peer, state)

		randomized := atomic.LoadInt32(&state.randomizedObfuscation)
		if randomized > 0 {
			// Meaningful jitter range for DPI evasion: 100-500ms
			delay := fastRandRange(100, 500)
			peer.device.log.Verbosef("OBF: Applying RANDOM handshake jitter: %dms", delay)
			time.Sleep(time.Duration(delay) * time.Millisecond)
		} else {
			jitter := atomic.LoadInt32(&state.timeJitter)
			if jitter > 0 {
				delay := fastRandRange(50, 150+int(jitter)*50)
				peer.device.log.Verbosef("OBF: Applying handshake jitter: %dms", delay)
				time.Sleep(time.Duration(delay) * time.Millisecond)
			}
		}
	}

	sendHandshakePrePackets(peer)

	msg, err := peer.device.CreateMessageInitiation(peer)
	if err != nil {
		peer.device.log.Errorf("%v - Failed to create initiation message: %v", peer, err)
		if state != nil {
			updateStats(state, false, peer)
		}
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
		if state != nil {
			updateStats(state, false, peer)
		}
	} else {
		peer.device.log.Verbosef("OBF: Handshake initiation sent successfully")
		if state != nil {
			updateStats(state, true, peer)
		}
	}
	peer.timersHandshakeInitiated()
	return err
}

func (peer *Peer) SendHandshakeResponse() error {
	peer.handshake.mutex.Lock()
	peer.handshake.lastSentHandshake = time.Now()
	peer.handshake.mutex.Unlock()
	peer.device.log.Verbosef("%v - Sending handshake response", peer)

	state := getPeerObfuscation(peer)
	if state != nil {
		MarkReceivedTraffic(peer)
		atomic.StoreInt64(&state.lastHandshake, time.Now().Unix())
	}

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

// ---------------------------------------------------------------------------
// TUN reader — hot path optimized
// ---------------------------------------------------------------------------

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

		// Batch time.Now() once per read batch instead of per-packet
		now := time.Now().Unix()

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

			// Initialize obfuscation state once per peer lifecycle (lock-free after first call)
			state := ensurePeerObfuscation(peer)
			atomic.StoreInt64(&state.lastRealTraffic, now)

			// Profile rotation check (uses batched timestamp)
			if shouldRotateProfile(state, now) {
				rotateProfile(state)
				device.log.Verbosef("OBF: Rotated size profile to %d", state.sizeProfile)
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

				// Inline camouflage check — no goroutine spawn
				state := getPeerObfuscation(peer)
				if state != nil && shouldSendCamouflage(peer, state, now) {
					sendCamouflagePacket(peer)
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

// ---------------------------------------------------------------------------
// Staging and sending
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Encryption
// ---------------------------------------------------------------------------

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
					// Correct MTU calculation: account for transport header + poly1305 tag
					// to prevent IP-level fragmentation of the outer UDP packet.
					maxSafeSize := tunMTU - MessageTransportHeaderSize - chacha20poly1305.Overhead
					if maxSafeSize < 0 {
						maxSafeSize = 0
					}
					elem.packet = padToProfileSmart(elem.packet, state, maxSafeSize, elem.peer)
				}
			}
			binary.LittleEndian.PutUint64(nonce[4:], elem.nonce)
			elem.packet = elem.keypair.send.Seal(header, nonce[:], elem.packet, nil)
		}
		elemsContainer.Unlock()
	}
}

// ---------------------------------------------------------------------------
// Sequential sender
// ---------------------------------------------------------------------------

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

		state := getPeerObfuscation(peer)
		if state != nil {
			if err != nil {
				updateStats(state, false, peer)
			} else {
				updateStats(state, true, peer)
			}
		}

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