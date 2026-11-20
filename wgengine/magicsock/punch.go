// Copyright (c) Tailscale Inc & contributors
// SPDX-License-Identifier: BSD-3-Clause

package magicsock

import (
	"context"
	"crypto/rand"
	"errors"
	"fmt"
	mathrand "math/rand/v2"
	"net"
	"net/netip"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/tailscale/wireguard-go/conn"
	"go4.org/mem"
	"tailscale.com/disco"
	"tailscale.com/envknob"
	"tailscale.com/feature/buildfeatures"
	"tailscale.com/net/netns"
	"tailscale.com/net/stun"
	"tailscale.com/syncs"
	"tailscale.com/tailcfg"
	"tailscale.com/tstime/mono"
	"tailscale.com/types/key"
	"tailscale.com/types/nettype"
	"tailscale.com/types/opt"
)

// Enhanced NAT hole-punching configuration knobs (modeled after UU Remote's
// multi-tier Cone / Linear-Symmetric / Random-Symmetric traversal engine).
var (
	// envEnhancedPunch enables enhanced NAT hole punching (linear port
	// prediction + multi-socket birthday attack with winning-socket handover).
	// Enabled by default; set TS_ENHANCED_PUNCH=false to disable.
	envEnhancedPunch = envknob.RegisterOptBool("TS_ENHANCED_PUNCH")

	// envEnhancedPunchSockets controls how many concurrent UDP sockets the
	// symmetric-NAT side opens during Stage 2 (birthday attack). Default: 150.
	envEnhancedPunchSockets = envknob.RegisterInt("TS_ENHANCED_PUNCH_SOCKETS")

	// envEnhancedPunchProbes controls how many random/predicted destination
	// ports the cone side sprays during Stage 2. Default: 1200.
	envEnhancedPunchProbes = envknob.RegisterInt("TS_ENHANCED_PUNCH_PROBES")

	// envEnhancedPunchPPS controls the packet-per-second pacing rate for port
	// spraying to avoid tripping stateful firewall flood limits. Default: 300.
	envEnhancedPunchPPS = envknob.RegisterInt("TS_ENHANCED_PUNCH_PPS")

	// envEnhancedPunchSTUNServers is an optional comma-separated list of
	// fallback STUN host:port servers used ONLY when the DERP map has fewer
	// than 2 STUN IPs (so netcheck could not determine MappingVariesByDestIP).
	// Set to "none" to disable fallback STUN probing.
	envEnhancedPunchSTUNServers = envknob.RegisterString("TS_ENHANCED_PUNCH_STUN_SERVERS")

	// envEnhancedPunchFWCheck controls whether firewall connectivity checks
	// (similar to UU Remote's PunchCheckFireWall) run during punching.
	envEnhancedPunchFWCheck = envknob.RegisterOptBool("TS_ENHANCED_PUNCH_FW_CHECK")
)

const (
	defaultPunchSockets       = 150
	defaultLinearPunchSockets = 16
	defaultBothLinearSockets  = 32
	defaultPunchProbes        = 1200
	defaultPunchPPS           = 300

	punchLinearStageDuration   = 2 * time.Second
	punchBirthdayStageDuration = 5 * time.Second
	punchOfferTimeout          = 3 * time.Second
	punchNATCacheTTL           = 2 * time.Minute
	punchFirewallCooldown      = 5 * time.Minute

	receivePunchName = "ReceivePunch"
)

// Test-overridable timing knobs.
var (
	enhancedPunchInitialDelay = 3 * time.Second
	enhancedPunchCooldown     = 30 * time.Second
	enhancedPunchLinearWait   = punchLinearStageDuration
	enhancedPunchBirthdayWait = punchBirthdayStageDuration
)

var defaultFallbackSTUNServers = []string{
	"stun.miwifi.com:3478",
	"stun.chat.bilibili.com:3478",
	"stun.hitv.com:3478",
}

var defaultFirewallCheckTargets = []string{
	"223.5.5.5:53",
	"119.29.29.29:53",
}

func enhancedPunchEnabled() bool {
	if v, ok := envEnhancedPunch().Get(); ok {
		return v
	}
	return true
}

func enhancedPunchSockets() int {
	if n := envEnhancedPunchSockets(); n > 0 {
		return min(n, 512)
	}
	return defaultPunchSockets
}

func enhancedPunchProbes() int {
	if n := envEnhancedPunchProbes(); n > 0 {
		return min(n, 8192)
	}
	return defaultPunchProbes
}

func enhancedPunchPPS() int {
	if n := envEnhancedPunchPPS(); n > 0 {
		return min(n, 2000)
	}
	return defaultPunchPPS
}

func enhancedPunchFWCheckEnabled() bool {
	if v, ok := envEnhancedPunchFWCheck().Get(); ok {
		return v
	}
	return !inTest()
}

// punchReadResult carries a WireGuard packet received on an endpoint's adopted
// punch UDP socket into wireguard-go via receivePunch.
type punchReadResult struct {
	ep      *endpoint
	buf     []byte // pooled buffer
	n       int
	src     netip.AddrPort
	release func()
}

var punchBufPool = sync.Pool{
	New: func() any {
		b := make([]byte, 64<<10)
		return &b
	},
}

// natProfile caches the local node's classified IPv4 NAT behavior.
type natProfile struct {
	natType    disco.NATType
	publicAddr netip.AddrPort
	portDelta  int16
	updatedAt  time.Time
}

// classifyNATSamples classifies IPv4 NAT mapping behavior into 3 tiers:
// Cone, LinearSymmetric (with port step delta), or RandomSymmetric.
func classifyNATSamples(samples []netip.AddrPort, mappingVaries opt.Bool) (natType disco.NATType, base netip.AddrPort, delta int16) {
	var valid []netip.AddrPort
	for _, s := range samples {
		if s.IsValid() && s.Addr().Is4() && s.Port() != 0 {
			valid = append(valid, s)
		}
	}
	if len(valid) > 0 {
		base = valid[0]
	}

	if v, ok := mappingVaries.Get(); ok && !v {
		return disco.NATCone, base, 0
	}

	if len(valid) < 2 {
		if v, ok := mappingVaries.Get(); ok && v {
			return disco.NATRandomSymmetric, base, 0
		}
		return disco.NATUnknown, base, 0
	}

	// Collect unique observed endpoints and check if all share the same public IP.
	var uniquePorts []uint16
	seenPort := make(map[uint16]bool, len(valid))
	sameIP := true
	firstIP := valid[0].Addr()
	for _, s := range valid {
		if s.Addr() != firstIP {
			sameIP = false
		}
		if !seenPort[s.Port()] {
			seenPort[s.Port()] = true
			uniquePorts = append(uniquePorts, s.Port())
		}
	}

	if sameIP && len(uniquePorts) == 1 {
		return disco.NATCone, valid[0], 0
	}
	if !sameIP {
		// Different public IPs across STUN targets (e.g., CGNAT IP pool or split routing).
		return disco.NATRandomSymmetric, valid[0], 0
	}

	// Same public IP, multiple distinct ports -> Symmetric NAT.
	// Check whether the allocated ports are closely clustered / linearly incrementing
	// (max adjacent gap <= 16), matching UU Remote's LinearSymmetric vs RandomSymmetric split.
	sorted := slices.Clone(uniquePorts)
	slices.Sort(sorted)
	maxGap := 0
	sumGap := 0
	for i := 1; i < len(sorted); i++ {
		gap := int(sorted[i]) - int(sorted[i-1])
		if gap > maxGap {
			maxGap = gap
		}
		sumGap += gap
	}
	if maxGap > 0 && maxGap <= 16 {
		avgStep := max(sumGap/(len(sorted)-1), 1)
		// Use the highest observed port as the latest base for forward prediction.
		latest := netip.AddrPortFrom(firstIP, sorted[len(sorted)-1])
		return disco.NATLinearSymmetric, latest, int16(avgStep)
	}
	return disco.NATRandomSymmetric, valid[len(valid)-1], 0
}

type punchSession struct {
	id         [8]byte
	peerKey    key.NodePublic
	peerDisco  key.DiscoPublic
	ep         *endpoint
	ctx        context.Context
	cancel     context.CancelFunc
	localNAT   natProfile
	remoteNAT  disco.NATType
	remoteAddr netip.AddrPort
	remoteStep int16
	numSockets int
	started    bool
	won        atomic.Bool
}

// punchManager coordinates UU-style enhanced NAT hole punching for a [Conn].
//
// Lock ordering: punchManager.mu is a leaf lock (never acquire Conn.mu or
// endpoint.mu while holding punchManager.mu).
type punchManager struct {
	c *Conn

	mu              syncs.Mutex
	byPeer          map[key.NodePublic]*punchSession
	byID            map[[8]byte]*punchSession
	natCache        natProfile
	firewallBlocked time.Time
	testNATOverride *natProfile // non-nil only in unit tests
}

func newPunchManager(c *Conn) *punchManager {
	return &punchManager{
		c:      c,
		byPeer: make(map[key.NodePublic]*punchSession),
		byID:   make(map[[8]byte]*punchSession),
	}
}

func (pm *punchManager) close() {
	pm.mu.Lock()
	sessions := make([]*punchSession, 0, len(pm.byPeer))
	for _, s := range pm.byPeer {
		sessions = append(sessions, s)
	}
	clear(pm.byPeer)
	clear(pm.byID)
	pm.mu.Unlock()

	for _, s := range sessions {
		s.cancel()
	}
}

func (pm *punchManager) invalidateNATCache() {
	pm.mu.Lock()
	pm.natCache = natProfile{}
	pm.mu.Unlock()
}

func (pm *punchManager) cancelPeer(pk key.NodePublic) {
	pm.mu.Lock()
	s := pm.byPeer[pk]
	if s != nil {
		delete(pm.byPeer, pk)
		delete(pm.byID, s.id)
	}
	pm.mu.Unlock()
	if s != nil {
		s.cancel()
	}
}

func (pm *punchManager) isFirewallBlocked(now time.Time) bool {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	return !pm.firewallBlocked.IsZero() && now.Before(pm.firewallBlocked)
}

func (pm *punchManager) markFirewallBlocked() {
	pm.mu.Lock()
	pm.firewallBlocked = time.Now().Add(punchFirewallCooldown)
	pm.mu.Unlock()
}

// getLocalNATProfile determines our 3-level IPv4 NAT classification using
// the latest netcheck report, falling back to a quick multi-STUN probe only
// when the DERP map had fewer than 2 STUN servers.
func (pm *punchManager) getLocalNATProfile(ctx context.Context) natProfile {
	pm.mu.Lock()
	if pm.testNATOverride != nil {
		p := *pm.testNATOverride
		pm.mu.Unlock()
		return p
	}
	if pm.natCache.natType != disco.NATUnknown && time.Since(pm.natCache.updatedAt) < punchNATCacheTTL {
		p := pm.natCache
		pm.mu.Unlock()
		return p
	}
	pm.mu.Unlock()

	rep := pm.c.lastNetCheckReport.Load()
	var samples []netip.AddrPort
	var mappingVaries opt.Bool
	var derpPubIP netip.Addr
	if rep != nil {
		// Only trust MappingVariesByDestIP==false if netcheck actually heard from
		// >= 2 distinct DERP/STUN regions; with a single-region DERPMap, repeated
		// STUN probes hit the same destination IP:port and falsely report false
		// even behind a symmetric NAT!
		if v, ok := rep.MappingVariesByDestIP.Get(); ok && (v || len(rep.RegionV4Latency) >= 2) {
			mappingVaries = rep.MappingVariesByDestIP
		}
		if len(rep.GlobalV4Sequence) > 0 && len(rep.RegionV4Latency) >= 2 {
			samples = append(samples, rep.GlobalV4Sequence...)
		} else if rep.GlobalV4.IsValid() {
			samples = append(samples, rep.GlobalV4)
		}
		if rep.GlobalV4.IsValid() && rep.GlobalV4.Addr().Is4() {
			derpPubIP = rep.GlobalV4.Addr()
		}
	}

	natType, base, delta := classifyNATSamples(samples, mappingVaries)

	// If DERPMap only had 1 STUN server (MappingVariesByDestIP is blank),
	// probe fallback STUN servers from a single temporary UDP socket so single-DERP
	// Headscale setups still get accurate Cone / Linear / Random classification.
	if natType == disco.NATUnknown {
		extra := pm.probeFallbackSTUN(ctx, derpPubIP)
		if len(extra) >= 2 {
			natType, base, delta = classifyNATSamples(extra, "")
		} else if len(extra) == 1 && !base.IsValid() {
			base = extra[0]
		}
	}

	// Always prefer the real pconn4 STUN address as base when Cone, since
	// Cone-side spraying & listening happens on pconn4.
	if natType == disco.NATCone && rep != nil && rep.GlobalV4.IsValid() && rep.GlobalV4.Addr().Is4() {
		base = rep.GlobalV4
	}
	if !base.IsValid() && rep != nil && rep.GlobalV4.IsValid() && rep.GlobalV4.Addr().Is4() {
		base = rep.GlobalV4
	}

	prof := natProfile{
		natType:    natType,
		publicAddr: base,
		portDelta:  delta,
		updatedAt:  time.Now(),
	}
	if natType != disco.NATUnknown {
		pm.mu.Lock()
		pm.natCache = prof
		pm.mu.Unlock()
	}
	return prof
}

// probeFallbackSTUN sends standard RFC 5389 STUN Binding requests from one
// temporary UDP socket to multiple distinct STUN servers. If expectedIP is
// valid (the IP seen by our DERP STUN), responses with a different public IP
// (e.g. routed through a split proxy/VPN) are discarded.
func (pm *punchManager) probeFallbackSTUN(ctx context.Context, expectedIP netip.Addr) []netip.AddrPort {
	raw := strings.TrimSpace(envEnhancedPunchSTUNServers())
	var servers []string
	switch {
	case strings.EqualFold(raw, "none") || strings.EqualFold(raw, "off"):
		return nil
	case raw != "":
		for s := range strings.SplitSeq(raw, ",") {
			if s = strings.TrimSpace(s); s != "" {
				servers = append(servers, s)
			}
		}
	case inTest():
		return nil
	default:
		servers = defaultFallbackSTUNServers
	}
	if len(servers) < 2 {
		return nil
	}

	pctx, cancel := context.WithTimeout(ctx, 1800*time.Millisecond)
	defer cancel()

	sock, err := pm.c.listenPunchSocket(pctx)
	if err != nil {
		return nil
	}
	defer sock.Close()

	var results []netip.AddrPort
	buf := make([]byte, 1500)
	for _, srv := range servers {
		if pctx.Err() != nil {
			break
		}
		host, portStr, err := net.SplitHostPort(srv)
		if err != nil {
			continue
		}
		portNum, err := strconv.Atoi(portStr)
		if err != nil || portNum <= 0 || portNum > 65535 {
			continue
		}
		ips, err := net.DefaultResolver.LookupNetIP(pctx, "ip4", host)
		if err != nil || len(ips) == 0 {
			continue
		}
		dst := netip.AddrPortFrom(ips[0].Unmap(), uint16(portNum))
		txid := stun.NewTxID()
		req := stun.Request(txid)
		if _, err := sock.WriteToUDPAddrPort(req, dst); err != nil {
			continue
		}
		_ = sock.SetReadDeadline(time.Now().Add(500 * time.Millisecond))
		for {
			n, _, err := sock.ReadFromUDPAddrPort(buf)
			if err != nil {
				break
			}
			gotTx, mapped, err := stun.ParseResponse(buf[:n])
			if err != nil || gotTx != txid || !mapped.IsValid() || !mapped.Addr().Is4() {
				continue
			}
			if expectedIP.IsValid() && mapped.Addr() != expectedIP {
				// Likely routed via a proxy/VPN tunnel instead of direct WAN; ignore.
				break
			}
			results = append(results, mapped)
			break
		}
	}
	return results
}

// initiate starts an enhanced hole-punching negotiation with ep over DERP.
func (pm *punchManager) initiate(ep *endpoint) {
	if !buildfeatures.HasNATTraversal || !hasUDPTransport || !enhancedPunchEnabled() {
		return
	}
	if pm.c.closing.Load() || pm.c.onlyTCP443.Load() || debugNeverDirectUDP() || debugAlwaysDERP() {
		return
	}
	if pm.isFirewallBlocked(time.Now()) {
		return
	}

	epDisco := ep.disco.Load()
	if epDisco == nil {
		return
	}
	ep.mu.Lock()
	derpAddr := ep.derpAddr
	alreadyDirect := ep.bestAddr.isDirect() && mono.Now().Before(ep.trustBestAddrUntil)
	ep.mu.Unlock()
	if alreadyDirect || !derpAddr.IsValid() {
		return
	}

	prof := pm.getLocalNATProfile(pm.c.connCtx)
	if !prof.publicAddr.IsValid() || !prof.publicAddr.Addr().Is4() {
		return
	}

	var punchID [8]byte
	if _, err := rand.Read(punchID[:]); err != nil {
		return
	}

	sctx, cancel := context.WithTimeout(pm.c.connCtx, punchOfferTimeout+enhancedPunchLinearWait+enhancedPunchBirthdayWait+2*time.Second)
	s := &punchSession{
		id:         punchID,
		peerKey:    ep.publicKey,
		peerDisco:  epDisco.key(),
		ep:         ep,
		ctx:        sctx,
		cancel:     cancel,
		localNAT:   prof,
		numSockets: enhancedPunchSockets(),
	}

	pm.mu.Lock()
	if _, exists := pm.byPeer[ep.publicKey]; exists {
		pm.mu.Unlock()
		cancel()
		return
	}
	pm.byPeer[ep.publicKey] = s
	pm.byID[punchID] = s
	pm.mu.Unlock()

	stage := uint8(2)
	if prof.natType == disco.NATLinearSymmetric {
		stage = 1
	}

	pm.c.logf("magicsock: enhanced-punch: offering to %v (%v) id=%x local_nat=%s pub=%v delta=%d",
		ep.publicKey.ShortString(), ep.discoShort(), punchID[:4], prof.natType, prof.publicAddr, prof.portDelta)

	offer := &disco.PunchOffer{
		PunchID:    punchID,
		NATType:    prof.natType,
		Stage:      stage,
		IsReply:    false,
		PortDelta:  prof.portDelta,
		NumSockets: uint16(s.numSockets),
		PublicAddr: prof.publicAddr,
	}
	if _, err := pm.c.sendDiscoMessage(epAddr{ap: derpAddr}, ep.publicKey, epDisco.key(), offer, discoLog); err != nil {
		pm.cleanupSession(s)
		return
	}

	// Clean up automatically if peer never replies (e.g., unmodded Tailscale peer).
	time.AfterFunc(punchOfferTimeout, func() {
		pm.mu.Lock()
		cur := pm.byID[punchID]
		notStarted := cur == s && !cur.started
		pm.mu.Unlock()
		if notStarted {
			pm.cleanupSession(s)
		}
	})
}

// handlePunchOffer handles an inbound PunchOffer received via DERP.
func (pm *punchManager) handlePunchOffer(ep *endpoint, peerDisco key.DiscoPublic, m *disco.PunchOffer) {
	if !buildfeatures.HasNATTraversal || !hasUDPTransport || !enhancedPunchEnabled() {
		return
	}
	if pm.c.closing.Load() || pm.c.onlyTCP443.Load() || debugNeverDirectUDP() || debugAlwaysDERP() {
		return
	}
	if pm.isFirewallBlocked(time.Now()) {
		return
	}
	if !m.PublicAddr.IsValid() || !m.PublicAddr.Addr().Is4() {
		return
	}

	ep.mu.Lock()
	derpAddr := ep.derpAddr
	alreadyDirect := ep.bestAddr.isDirect() && mono.Now().Before(ep.trustBestAddrUntil)
	ep.mu.Unlock()
	if alreadyDirect {
		return
	}

	if m.IsReply {
		// Peer accepted our initial PunchOffer! Start executing our side.
		pm.mu.Lock()
		s := pm.byID[m.PunchID]
		if s == nil || s.started || s.peerKey != ep.publicKey {
			pm.mu.Unlock()
			return
		}
		s.remoteNAT = m.NATType
		s.remoteAddr = m.PublicAddr
		s.remoteStep = m.PortDelta
		if m.NumSockets > 0 && int(m.NumSockets) < s.numSockets {
			s.numSockets = int(m.NumSockets)
		}
		s.started = true
		pm.mu.Unlock()

		go pm.runSession(s)
		return
	}

	// Initial offer from peer. Classify our local NAT first.
	prof := pm.getLocalNATProfile(pm.c.connCtx)
	if !prof.publicAddr.IsValid() || !prof.publicAddr.Addr().Is4() || !derpAddr.IsValid() {
		return
	}

	// Skip enhanced multi-socket punching if both sides are Cone NAT
	// (standard Tailscale CallMeMaybe is already optimal for Cone<->Cone).
	if prof.natType == disco.NATCone && m.NATType == disco.NATCone {
		return
	}

	sctx, cancel := context.WithTimeout(pm.c.connCtx, enhancedPunchLinearWait+enhancedPunchBirthdayWait+3*time.Second)
	sockets := enhancedPunchSockets()
	if m.NumSockets > 0 && int(m.NumSockets) < sockets {
		sockets = int(m.NumSockets)
	}
	s := &punchSession{
		id:         m.PunchID,
		peerKey:    ep.publicKey,
		peerDisco:  peerDisco,
		ep:         ep,
		ctx:        sctx,
		cancel:     cancel,
		localNAT:   prof,
		remoteNAT:  m.NATType,
		remoteAddr: m.PublicAddr,
		remoteStep: m.PortDelta,
		numSockets: sockets,
		started:    true,
	}

	pm.mu.Lock()
	if existing := pm.byPeer[ep.publicKey]; existing != nil {
		if existing.started {
			pm.mu.Unlock()
			cancel()
			return
		}
		// Glare tie-breaker: higher DiscoPublic key wins; lower key yields to peer's offer.
		if pm.c.discoAtomic.Public().Compare(peerDisco) > 0 {
			pm.mu.Unlock()
			cancel()
			return
		}
		delete(pm.byID, existing.id)
		existing.cancel()
	}
	pm.byPeer[ep.publicKey] = s
	pm.byID[s.id] = s
	pm.mu.Unlock()

	// Reply with our NAT profile so peer launches in lockstep.
	reply := &disco.PunchOffer{
		PunchID:    m.PunchID,
		NATType:    prof.natType,
		Stage:      m.Stage,
		IsReply:    true,
		PortDelta:  prof.portDelta,
		NumSockets: uint16(sockets),
		PublicAddr: prof.publicAddr,
	}
	if _, err := pm.c.sendDiscoMessage(epAddr{ap: derpAddr}, ep.publicKey, peerDisco, reply, discoLog); err != nil {
		pm.cleanupSession(s)
		return
	}

	go pm.runSession(s)
}

func (pm *punchManager) cleanupSession(s *punchSession) {
	s.cancel()
	pm.mu.Lock()
	if pm.byID[s.id] == s {
		delete(pm.byID, s.id)
	}
	if pm.byPeer[s.peerKey] == s {
		delete(pm.byPeer, s.peerKey)
	}
	pm.mu.Unlock()
}

// runSession dispatches the UU-style NAT traversal strategy matrix based on
// (localNAT, remoteNAT).
func (pm *punchManager) runSession(s *punchSession) {
	defer pm.cleanupSession(s)

	local := s.localNAT.natType
	remote := s.remoteNAT
	// Treat unknown as RandomSymmetric so single-DERP / fallback-failed peers still attempt birthday attack.
	if local == disco.NATUnknown {
		local = disco.NATRandomSymmetric
	}
	if remote == disco.NATUnknown {
		remote = disco.NATRandomSymmetric
	}

	if local == disco.NATCone && remote == disco.NATCone {
		return
	}

	pm.c.logf("magicsock: enhanced-punch: start id=%x peer=%v strategy=%s->%s remote=%v sockets=%d",
		s.id[:4], s.peerKey.ShortString(), local, remote, s.remoteAddr, s.numSockets)

	// Start UU-style firewall circuit breaker in background.
	if enhancedPunchFWCheckEnabled() {
		go pm.monitorFirewall(s)
	}

	// Obtain shared disco key once for fast packet sealing/opening on punch sockets.
	pm.c.mu.Lock()
	if pm.c.closed {
		pm.c.mu.Unlock()
		return
	}
	di := pm.c.discoInfoForKnownPeerLocked(s.peerDisco)
	sharedKey := di.sharedKey
	pm.c.mu.Unlock()

	switch {
	case local == disco.NATCone && remote == disco.NATLinearSymmetric:
		// Stage 1: ConePunchToLinearSymmetric
		pm.coneSprayPorts(s, sharedKey, predictedPorts(s.remoteAddr.Port(), s.remoteStep, 16, 128), enhancedPunchLinearWait)
		if s.won.Load() || s.ctx.Err() != nil {
			return
		}
		// Stage 2: escalate to ConePunchToRandomSymmetric (birthday attack)
		pm.c.logf("magicsock: enhanced-punch: id=%x escalating ConePunchToLinear->ConePunchToRandom", s.id[:4])
		pm.coneSprayPorts(s, sharedKey, birthdayPorts(s.remoteAddr.Port(), enhancedPunchProbes()), enhancedPunchBirthdayWait)

	case local == disco.NATCone && remote == disco.NATRandomSymmetric:
		// ConePunchToRandomSymmetric
		pm.coneSprayPorts(s, sharedKey, birthdayPorts(s.remoteAddr.Port(), enhancedPunchProbes()), enhancedPunchBirthdayWait)

	case local == disco.NATLinearSymmetric && remote == disco.NATCone:
		// Stage 1: LinearSymmetricPunchToCone
		pm.symmetricPunchToTarget(s, sharedKey, min(defaultLinearPunchSockets, s.numSockets), []uint16{s.remoteAddr.Port()}, enhancedPunchLinearWait)
		if s.won.Load() || s.ctx.Err() != nil {
			return
		}
		// Stage 2: escalate to RandomSymmetricPunchToCone (birthday attack, 150 sockets)
		pm.c.logf("magicsock: enhanced-punch: id=%x escalating LinearToCone->RandomToCone (sockets=%d)", s.id[:4], s.numSockets)
		pm.symmetricPunchToTarget(s, sharedKey, s.numSockets, []uint16{s.remoteAddr.Port()}, enhancedPunchBirthdayWait)

	case local == disco.NATRandomSymmetric && remote == disco.NATCone:
		// RandomSymmetricPunchToCone (150-socket birthday attack)
		pm.symmetricPunchToTarget(s, sharedKey, s.numSockets, []uint16{s.remoteAddr.Port()}, enhancedPunchBirthdayWait)

	case local == disco.NATLinearSymmetric && remote == disco.NATLinearSymmetric:
		// Stage 1: BothLinearSymmetricPunch using diagonal-band port prediction.
		// Because flow #k on each side maps sequentially to base + k*step, targeting
		// within ±W of index k boosts expected hits from 1.0 to K/(2W) (>98% with 240 flows).
		ports := diagonalLinearPorts(s.remoteAddr.Port(), s.remoteStep, 240, 24)
		pm.symmetricPunchToTarget(s, sharedKey, min(defaultBothLinearSockets, s.numSockets), ports, enhancedPunchLinearWait)
		if s.won.Load() || s.ctx.Err() != nil {
			return
		}
		// Stage 2: escalate to BothRandomSymmetricPunch (CGNAT PBA-biased)
		pm.c.logf("magicsock: enhanced-punch: id=%x escalating BothLinear->BothRandom", s.id[:4])
		pm.symmetricPunchToTarget(s, sharedKey, min(64, s.numSockets), pbaBirthdayPorts(s.remoteAddr.Port(), enhancedPunchProbes()), enhancedPunchBirthdayWait)

	default:
		// LinearSymmetric<->RandomSymmetric or BothRandomSymmetricPunch.
		// Focuses 75% of probes into ±1024 around peer's observed port (ISP CGNAT PBA
		// port-block allocation) with 2-pass refresh so both NAT4 tables overlap in time.
		pm.symmetricPunchToTarget(s, sharedKey, min(64, s.numSockets), pbaBirthdayPorts(s.remoteAddr.Port(), enhancedPunchProbes()), enhancedPunchBirthdayWait)
	}
}

// coneSprayPorts sends paced PunchProbe packets from our existing pconn4 to
// targetPorts on s.remoteAddr.Addr().
func (pm *punchManager) coneSprayPorts(s *punchSession, sharedKey key.DiscoShared, targetPorts []uint16, maxDur time.Duration) {
	if len(targetPorts) == 0 {
		return
	}
	stageCtx, cancel := context.WithTimeout(s.ctx, maxDur)
	defer cancel()

	probePkt := pm.sealPunchPacket(sharedKey, &disco.PunchProbe{
		PunchID: s.id,
		NodeKey: pm.c.publicKeyAtomic.Load(),
	})

	// Give the symmetric peer a short head start (~250ms in production) to
	// finish opening its batch of UDP sockets before our first spray arrives.
	if !inTest() {
		select {
		case <-stageCtx.Done():
			return
		case <-time.After(250 * time.Millisecond):
		}
	}

	pps := enhancedPunchPPS()
	interval := time.Second / time.Duration(max(pps, 1))
	ticker := time.NewTicker(interval)
	defer ticker.Stop()

	remoteIP := s.remoteAddr.Addr()
	var consecutiveErrs int

	// Send one pass across targetPorts, then keep waiting until stageCtx expires
	// in case an in-flight PunchAck arrives shortly after.
	for _, port := range targetPorts {
		if s.won.Load() || stageCtx.Err() != nil {
			return
		}
		dst := netip.AddrPortFrom(remoteIP, port)
		if _, err := pm.c.pconn4.WriteToUDPAddrPort(probePkt, dst); err != nil {
			consecutiveErrs++
			if consecutiveErrs >= 32 {
				pm.c.logf("magicsock: enhanced-punch: id=%x aborting spray due to write errors: %v", s.id[:4], err)
				pm.markFirewallBlocked()
				s.cancel()
				return
			}
		} else {
			consecutiveErrs = 0
		}

		select {
		case <-stageCtx.Done():
			return
		case <-ticker.C:
		}
	}

	// Wait briefly for late replies before escalating.
	select {
	case <-stageCtx.Done():
	case <-time.After(400 * time.Millisecond):
	}
}

// symmetricPunchToTarget opens numSockets independent UDP sockets on the
// symmetric-NAT side, punches outbound mappings toward targetPorts on
// s.remoteAddr.Addr(), and waits for any socket to collide with an inbound
// PunchProbe or PunchAck. On collision, the winning socket is hot-handed over
// to s.ep via adoptPunchConn and all other sockets are closed.
func (pm *punchManager) symmetricPunchToTarget(s *punchSession, sharedKey key.DiscoShared, numSockets int, targetPorts []uint16, maxDur time.Duration) {
	if numSockets <= 0 || len(targetPorts) == 0 {
		return
	}
	stageCtx, cancel := context.WithTimeout(s.ctx, maxDur)
	defer cancel()

	probePkt := pm.sealPunchPacket(sharedKey, &disco.PunchProbe{
		PunchID: s.id,
		NodeKey: pm.c.publicKeyAtomic.Load(),
	})

	sockets := make([]nettype.PacketConn, 0, numSockets)
	var winnerIdx atomic.Int32
	winnerIdx.Store(-1)

	var wg sync.WaitGroup
	remoteIP := s.remoteAddr.Addr()

	// Multi-target (Symmetric <-> Symmetric): create sockets first, then send
	// targetPorts in 2 paced passes across the sockets. Re-sending the exact same
	// (socket, dstPort) 5-tuple on Pass 2 reuses the existing NAT4 mapping on our
	// side while hitting mappings the peer finished creating during Pass 1.
	if len(targetPorts) > 1 {
		for i := range numSockets {
			if s.won.Load() || stageCtx.Err() != nil {
				break
			}
			sock, err := pm.c.listenPunchSocket(stageCtx)
			if err != nil {
				pm.c.logf("magicsock: enhanced-punch: id=%x socket alloc stopped at %d: %v", s.id[:4], i, err)
				break
			}
			idx := len(sockets)
			sockets = append(sockets, sock)
			wg.Add(1)
			go func(idx int, conn nettype.PacketConn) {
				defer wg.Done()
				pm.readCandidatePunchSocket(stageCtx, s, sharedKey, idx, conn, &winnerIdx, cancel)
			}(idx, sock)
		}

		if len(sockets) > 0 {
			pps := max(enhancedPunchPPS()*2, 600)
			interval := time.Second / time.Duration(pps)
			for pass := range 2 {
				if s.won.Load() || stageCtx.Err() != nil {
					break
				}
				if pass > 0 {
					wait := 350 * time.Millisecond
					if inTest() {
						wait = 60 * time.Millisecond
					}
					select {
					case <-stageCtx.Done():
					case <-time.After(wait):
					}
				}
				for j, port := range targetPorts {
					if s.won.Load() || stageCtx.Err() != nil {
						break
					}
					sock := sockets[j%len(sockets)]
					dst := netip.AddrPortFrom(remoteIP, port)
					_, _ = sock.WriteToUDPAddrPort(probePkt, dst)
					if !inTest() && (j+1)%8 == 0 {
						select {
						case <-stageCtx.Done():
						case <-time.After(interval * 8):
						}
					}
				}
			}
			// Wait briefly for in-flight PunchAck replies.
			select {
			case <-stageCtx.Done():
			case <-time.After(min(maxDur/3, 600*time.Millisecond)):
			}
		}

		win := int(winnerIdx.Load())
		for i, sock := range sockets {
			if i != win {
				_ = sock.Close()
			}
		}
		wg.Wait()
		return
	}

	// Single-target (Symmetric -> Cone): open numSockets independent UDP sockets
	// with gentle pacing so NAT conntrack doesn't drop bursts.
	for i := range numSockets {
		if s.won.Load() || stageCtx.Err() != nil {
			break
		}
		sock, err := pm.c.listenPunchSocket(stageCtx)
		if err != nil {
			pm.c.logf("magicsock: enhanced-punch: id=%x socket alloc stopped at %d: %v", s.id[:4], i, err)
			break
		}
		idx := len(sockets)
		sockets = append(sockets, sock)

		// Start listener on this punch socket.
		wg.Add(1)
		go func(idx int, conn nettype.PacketConn) {
			defer wg.Done()
			pm.readCandidatePunchSocket(stageCtx, s, sharedKey, idx, conn, &winnerIdx, cancel)
		}(idx, sock)

		dst := netip.AddrPortFrom(remoteIP, targetPorts[0])
		_, _ = sock.WriteToUDPAddrPort(probePkt, dst)

		// Pace creation slightly (~1ms per socket => 150 sockets in ~150ms) unless in test.
		if !inTest() && (i+1)%5 == 0 {
			select {
			case <-stageCtx.Done():
			case <-time.After(5 * time.Millisecond):
			}
		}
	}

	// Keep the NAT mappings alive with one refresh burst midway through the stage
	// for single-target (Symmetric -> Cone) punching.
	if len(targetPorts) == 1 && !s.won.Load() && stageCtx.Err() == nil {
		refreshTicker := time.NewTicker(min(maxDur/2, 1500*time.Millisecond))
		defer refreshTicker.Stop()
		dst := netip.AddrPortFrom(remoteIP, targetPorts[0])
	waitLoop:
		for {
			select {
			case <-stageCtx.Done():
				break waitLoop
			case <-refreshTicker.C:
				if s.won.Load() {
					break waitLoop
				}
				for _, sock := range sockets {
					if s.won.Load() || stageCtx.Err() != nil {
						break waitLoop
					}
					_, _ = sock.WriteToUDPAddrPort(probePkt, dst)
				}
			}
		}
	} else {
		<-stageCtx.Done()
	}

	// Close all non-winning sockets so reader goroutines exit promptly.
	win := int(winnerIdx.Load())
	for i, sock := range sockets {
		if i != win {
			_ = sock.Close()
		}
	}
	wg.Wait()
}

func (pm *punchManager) readCandidatePunchSocket(
	stageCtx context.Context,
	s *punchSession,
	sharedKey key.DiscoShared,
	idx int,
	conn nettype.PacketConn,
	winnerIdx *atomic.Int32,
	cancelStage context.CancelFunc,
) {
	buf := make([]byte, 512)
	for {
		if stageCtx.Err() != nil || s.won.Load() {
			return
		}
		_ = conn.SetReadDeadline(time.Now().Add(250 * time.Millisecond))
		n, from, err := conn.ReadFromUDPAddrPort(buf)
		if err != nil {
			if stageCtx.Err() != nil || errors.Is(err, net.ErrClosed) {
				return
			}
			// Ignore timeouts and transient ICMP errors (e.g. ECONNREFUSED from
			// ICMP Port Unreachable while probing a port-restricted peer NAT).
			continue
		}
		pkt := buf[:n]
		srcKeyBytes, ok := disco.Source(pkt)
		if !ok {
			continue
		}
		sender := key.DiscoPublicFromRaw32(mem.B(srcKeyBytes))
		if sender != s.peerDisco {
			continue
		}
		payload, ok := sharedKey.Open(pkt[discoHeaderLen:])
		if !ok {
			continue
		}
		dm, err := disco.Parse(payload)
		if err != nil {
			continue
		}

		var needAck bool
		switch dm := dm.(type) {
		case *disco.PunchProbe:
			if dm.PunchID != s.id {
				continue
			}
			needAck = true
		case *disco.PunchAck:
			if dm.PunchID != s.id {
				continue
			}
		default:
			continue
		}

		// Atomically claim the winning socket!
		if !s.won.CompareAndSwap(false, true) {
			return
		}
		winnerIdx.Store(int32(idx))

		// Clear read deadline before handing socket over for long-lived traffic.
		_ = conn.SetReadDeadline(time.Time{})

		if needAck {
			ackPkt := pm.sealPunchPacket(sharedKey, &disco.PunchAck{
				PunchID: s.id,
				Src:     from,
			})
			// Send twice for packet-loss resilience so peer immediately locks onto our mapped port.
			_, _ = conn.WriteToUDPAddrPort(ackPkt, from)
			_, _ = conn.WriteToUDPAddrPort(ackPkt, from)
		}

		pm.c.logf("magicsock: enhanced-punch: HIT! id=%x peer=%v local=%v -> remote=%v (adopted socket #%d)",
			s.id[:4], s.peerKey.ShortString(), conn.LocalAddr(), from, idx)

		// Hot-handover: bind this exact winning UDP socket onto endpoint so
		// WireGuard and Disco heartbeats continue over the punched 5-tuple!
		s.ep.adoptPunchConn(conn, from)

		cancelStage()
		s.cancel()
		return
	}
}

// handlePunchProbeLocked handles a PunchProbe arriving on pconn4 (usually on
// the Cone side when a Symmetric peer's probe makes it through).
//
// c.mu must be held.
func (pm *punchManager) handlePunchProbeLocked(dm *disco.PunchProbe, src epAddr, di *discoInfo) {
	if !hasUDPTransport || src.ap.Addr() == tailcfg.DerpMagicIPAddr || src.vni.IsSet() {
		return
	}

	pm.mu.Lock()
	s := pm.byID[dm.PunchID]
	pm.mu.Unlock()

	if s == nil || s.peerDisco != di.discoKey {
		return
	}

	// Reply with PunchAck directly from pconn4 to the exact mapped source port.
	ack := &disco.PunchAck{
		PunchID: dm.PunchID,
		Src:     src.ap,
	}
	dstKey := s.peerKey
	dstDisco := di.discoKey
	go func() {
		_, _ = pm.c.sendDiscoMessage(src, dstKey, dstDisco, ack, discoVerboseLog)
		time.Sleep(20 * time.Millisecond)
		_, _ = pm.c.sendDiscoMessage(src, dstKey, dstDisco, ack, discoVerboseLog)
	}()

	if s.won.CompareAndSwap(false, true) {
		pm.c.logf("magicsock: enhanced-punch: HIT via probe! id=%x peer=%v remote=%v",
			s.id[:4], s.peerKey.ShortString(), src.ap)
		pm.promoteDirectEndpointLocked(s.ep, src.ap)
		s.cancel()
	}
}

// handlePunchAckLocked handles a PunchAck arriving on pconn4 (Cone side
// receiving confirmation from the Symmetric peer's winning socket).
//
// c.mu must be held.
func (pm *punchManager) handlePunchAckLocked(dm *disco.PunchAck, src epAddr, di *discoInfo) {
	if !hasUDPTransport || src.ap.Addr() == tailcfg.DerpMagicIPAddr || src.vni.IsSet() {
		return
	}

	pm.mu.Lock()
	s := pm.byID[dm.PunchID]
	pm.mu.Unlock()

	if s == nil || s.peerDisco != di.discoKey {
		return
	}

	if s.won.CompareAndSwap(false, true) {
		pm.c.logf("magicsock: enhanced-punch: HIT via ack! id=%x peer=%v remote=%v",
			s.id[:4], s.peerKey.ShortString(), src.ap)
		pm.promoteDirectEndpointLocked(s.ep, src.ap)
		s.cancel()
	}
}

// promoteDirectEndpointLocked registers remote as a direct endpoint on ep
// (using the standard pconn4 socket) and immediately promotes it to bestAddr.
//
// c.mu must be held; ep.mu must NOT be held.
func (pm *punchManager) promoteDirectEndpointLocked(ep *endpoint, remote netip.AddrPort) {
	ea := epAddr{ap: remote}
	pm.c.peerMap.setNodeKeyForEpAddr(ea, ep.publicKey)

	ep.mu.Lock()
	defer ep.mu.Unlock()

	now := mono.Now()
	if ep.endpointState == nil {
		ep.endpointState = make(map[netip.AddrPort]*endpointState)
	}
	if _, ok := ep.endpointState[remote]; !ok {
		ep.endpointState[remote] = &endpointState{callMeMaybeTime: time.Now()}
	}
	if ep.isCallMeMaybeEP == nil {
		ep.isCallMeMaybeEP = make(map[netip.AddrPort]bool)
	}
	ep.isCallMeMaybeEP[remote] = true

	ep.setBestAddrLocked(addrQuality{
		epAddr:  ea,
		latency: 10 * time.Millisecond,
	})
	ep.bestAddrAt = now
	ep.trustBestAddrUntil = now.Add(trustUDPAddrDuration)
	ep.firstDirectFailAt = 0

	// Fire a regular disco.Ping so RTT, MTU, and heartbeat state converge cleanly.
	ep.startDiscoPingLocked(ea, now, pingDiscovery, 0, nil)
	if ep.heartBeatTimer == nil && !ep.heartbeatDisabled {
		ep.heartBeatTimer = time.AfterFunc(heartbeatInterval, ep.heartbeat)
	}
}

// monitorFirewall implements UU Remote's PunchCheckFireWall circuit breaker:
// periodically checks connectivity to well-known DNS IPs while punching and
// stops punching immediately if an enterprise firewall begins blocking outbound
// traffic.
func (pm *punchManager) monitorFirewall(s *punchSession) {
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()
	var failures int
	for {
		select {
		case <-s.ctx.Done():
			return
		case <-ticker.C:
			if s.won.Load() {
				return
			}
			okAny := false
			for _, target := range defaultFirewallCheckTargets {
				d := net.Dialer{Timeout: 600 * time.Millisecond}
				conn, err := d.DialContext(s.ctx, "tcp4", target)
				if err == nil {
					_ = conn.Close()
					okAny = true
					break
				}
			}
			if okAny {
				failures = 0
				continue
			}
			failures++
			if failures >= 2 {
				pm.c.logf("magicsock: enhanced-punch: id=%x firewall disruption detected, stopping punch", s.id[:4])
				pm.markFirewallBlocked()
				s.cancel()
				return
			}
		}
	}
}

func (pm *punchManager) sealPunchPacket(sharedKey key.DiscoShared, m disco.Message) []byte {
	pkt := make([]byte, 0, 128)
	pkt = append(pkt, disco.Magic...)
	pkt = pm.c.discoAtomic.Public().AppendTo(pkt)
	box := sharedKey.Seal(m.AppendMarshal(nil))
	pkt = append(pkt, box...)
	return pkt
}

// predictedPorts generates a focused window of ports around base + delta for
// LinearSymmetric NAT traversal.
func predictedPorts(base uint16, delta int16, back, forward int) []uint16 {
	center := int(base) + int(delta)
	out := make([]uint16, 0, back+forward+1)
	seen := make(map[uint16]bool, back+forward+1)
	add := func(p int) {
		// Wrap within ephemeral/non-privileged port space [1024, 65535].
		const span = 65535 - 1024 + 1
		w := ((p - 1024) % span)
		if w < 0 {
			w += span
		}
		port := uint16(1024 + w)
		if !seen[port] {
			seen[port] = true
			out = append(out, port)
		}
	}
	// Spiral outward from predicted center so the closest guesses fire first.
	add(center)
	for step := 1; step <= max(back, forward); step++ {
		if step <= forward {
			add(center + step)
		}
		if step <= back {
			add(center - step)
		}
	}
	return out
}

// birthdayPorts generates count unique ports in [1024, 65535]:
// 30% biased toward a neighborhood around basePort (±4096) to accelerate
// multi-pool CGNAT/enterprise gateways, and 70% uniformly distributed across
// the full high-port space for true random symmetric NATs.
func birthdayPorts(base uint16, count int) []uint16 {
	const (
		minPort = 1024
		maxPort = 65535
		span    = maxPort - minPort + 1
	)
	count = min(count, span)
	out := make([]uint16, 0, count)
	seen := make(map[uint16]bool, count)

	// 30% near basePort (±4096) if basePort is valid.
	localBudget := 0
	if base >= minPort {
		localBudget = count * 3 / 10
		const halfWindow = 4096
		lo := max(int(base)-halfWindow, minPort)
		hi := min(int(base)+halfWindow, maxPort)
		window := hi - lo + 1
		for len(out) < localBudget && len(out) < window {
			p := uint16(lo + mathrand.IntN(window))
			if !seen[p] {
				seen[p] = true
				out = append(out, p)
			}
		}
	}

	// Remaining 70% uniform random across [1024, 65535].
	for len(out) < count {
		p := uint16(minPort + mathrand.IntN(span))
		if !seen[p] {
			seen[p] = true
			out = append(out, p)
		}
	}
	return out
}

// diagonalLinearPorts generates count target ports for BothLinearSymmetric
// traversal: flow index k targets a random port within ±halfBand steps of
// base + (k+1)*step. Because both sides advance sequentially along their own
// port space, concentrating guesses along the diagonal raises E[hits] from 1
// to count/(2*halfBand).
func diagonalLinearPorts(base uint16, step int16, count, halfBand int) []uint16 {
	const (
		minPort = 1024
		maxPort = 65535
		span    = maxPort - minPort + 1
	)
	s := int(step)
	if s <= 0 {
		s = 1
	}
	out := make([]uint16, 0, count)
	for k := range count {
		offset := mathrand.IntN(2*halfBand+1) - halfBand
		raw := int(base) + (k+1+offset)*s
		w := (raw - minPort) % span
		if w < 0 {
			w += span
		}
		out = append(out, uint16(minPort+w))
	}
	return out
}

// pbaBirthdayPorts generates count target ports for Symmetric<->Symmetric
// traversal, optimizing for real-world ISP CGNAT Port Block Allocation
// (RFC 6888, typically 512-1024 port blocks):
//   - 45% in the aligned 512-port block containing base ([base&^511, +511])
//   - 40% in base ± 512 (handles unaligned 512-1024 port pools)
//   - 15% in base ± 2048 / uniform [1024, 65535]
//
// Duplicates across different local sockets are intentional because each
// (socket, dstPort) tuple creates an independent NAT4 mapping.
func pbaBirthdayPorts(base uint16, count int) []uint16 {
	const (
		minPort = 1024
		maxPort = 65535
		span    = maxPort - minPort + 1
	)
	out := make([]uint16, 0, count)
	if base >= minPort {
		// 45% in aligned 512-port block containing base.
		alignedLo := max(int(base&^511), minPort)
		alignedHi := min(alignedLo+511, maxPort)
		alignedSpan := alignedHi - alignedLo + 1
		b1 := count * 45 / 100
		for len(out) < b1 {
			out = append(out, uint16(alignedLo+mathrand.IntN(alignedSpan)))
		}
		// 40% in base ± 512 (covers unaligned 512-1024 port ranges).
		lo := max(int(base)-512, minPort)
		hi := min(int(base)+512, maxPort)
		win := hi - lo + 1
		b2 := count * 85 / 100
		for len(out) < b2 {
			out = append(out, uint16(lo+mathrand.IntN(win)))
		}
	}
	// Remaining 15% uniform random across [1024, 65535].
	for len(out) < count {
		out = append(out, uint16(minPort+mathrand.IntN(span)))
	}
	return out
}

// listenPunchSocket binds an ephemeral IPv4 UDP socket respecting Tailscale's
// netns (routing-loop prevention) and testOnlyPacketListener.
func (c *Conn) listenPunchSocket(ctx context.Context) (nettype.PacketConn, error) {
	if c.testOnlyPacketListener != nil {
		return nettype.MakePacketListenerWithNetIP(c.testOnlyPacketListener).ListenPacket(ctx, "udp4", ":0")
	}
	pc, err := netns.Listener(c.logf, c.netMon).ListenPacket(ctx, "udp4", ":0")
	if err != nil {
		return nil, err
	}
	npc, ok := pc.(nettype.PacketConn)
	if !ok {
		_ = pc.Close()
		return nil, fmt.Errorf("magicsock: punch socket %T does not implement nettype.PacketConn", pc)
	}
	trySetUDPSocketOptions(npc, c.logf)
	return npc, nil
}

// adoptPunchConn installs a winning punched UDP socket onto de, promotes
// remote to bestAddr, and starts a dedicated reader loop feeding WireGuard
// packets into wireguard-go via Conn.punchRecvCh.
//
// Neither c.mu nor de.mu may be held.
func (de *endpoint) adoptPunchConn(conn nettype.PacketConn, remote netip.AddrPort) {
	ea := epAddr{ap: remote}

	de.c.mu.Lock()
	if de.c.closed {
		de.c.mu.Unlock()
		_ = conn.Close()
		return
	}
	de.c.peerMap.setNodeKeyForEpAddr(ea, de.publicKey)
	de.c.mu.Unlock()

	rctx, cancel := context.WithCancel(de.c.connCtx)

	de.mu.Lock()
	if de.expired {
		de.mu.Unlock()
		cancel()
		_ = conn.Close()
		return
	}
	de.clearPunchConnLocked()
	de.punchConn = conn
	de.punchAddr = ea
	de.punchCancel = cancel

	now := mono.Now()
	if de.endpointState == nil {
		de.endpointState = make(map[netip.AddrPort]*endpointState)
	}
	if _, ok := de.endpointState[remote]; !ok {
		de.endpointState[remote] = &endpointState{callMeMaybeTime: time.Now()}
	}
	if de.isCallMeMaybeEP == nil {
		de.isCallMeMaybeEP = make(map[netip.AddrPort]bool)
	}
	de.isCallMeMaybeEP[remote] = true

	de.setBestAddrLocked(addrQuality{
		epAddr:  ea,
		latency: 10 * time.Millisecond,
	})
	de.bestAddrAt = now
	de.trustBestAddrUntil = now.Add(trustUDPAddrDuration)
	de.firstDirectFailAt = 0

	// Fire a regular disco.Ping through the adopted socket to confirm RTT and
	// engage standard heartbeat keepalives.
	de.startDiscoPingLocked(ea, now, pingDiscovery, 0, nil)
	if de.heartBeatTimer == nil && !de.heartbeatDisabled {
		de.heartBeatTimer = time.AfterFunc(heartbeatInterval, de.heartbeat)
	}
	de.mu.Unlock()

	go de.readPunchConnLoop(rctx, conn)
}

// clearPunchConnLocked closes any adopted punch UDP socket on de.
//
// de.mu must be held.
func (de *endpoint) clearPunchConnLocked() {
	if de.punchCancel != nil {
		de.punchCancel()
		de.punchCancel = nil
	}
	if de.punchConn != nil {
		_ = de.punchConn.Close()
		de.punchConn = nil
		de.punchAddr = epAddr{}
	}
}

// punchConnFor returns de's adopted punch socket if it matches target.
func (de *endpoint) punchConnFor(target epAddr) nettype.PacketConn {
	de.mu.Lock()
	defer de.mu.Unlock()
	if de.punchConn != nil && de.punchAddr == target {
		return de.punchConn
	}
	return nil
}

// readPunchConnLoop reads UDP packets from an adopted punch socket, routing
// disco messages to handleDiscoMessage and WireGuard packets to wireguard-go
// via Conn.punchRecvCh.
func (de *endpoint) readPunchConnLoop(ctx context.Context, pconn nettype.PacketConn) {
	for {
		if ctx.Err() != nil {
			return
		}
		bufPtr := punchBufPool.Get().(*[]byte)
		buf := *bufPtr
		n, src, err := pconn.ReadFromUDPAddrPort(buf)
		if err != nil {
			punchBufPool.Put(bufPtr)
			if ctx.Err() != nil || errors.Is(err, net.ErrClosed) {
				return
			}
			select {
			case <-ctx.Done():
				return
			case <-time.After(50 * time.Millisecond):
				continue
			}
		}
		if n == 0 {
			punchBufPool.Put(bufPtr)
			continue
		}

		pkt := buf[:n]
		ea := epAddr{ap: src}
		pt, _ := packetLooksLike(pkt)
		switch pt {
		case packetLooksLikeDisco:
			de.c.handleDiscoMessage(pkt, ea, false, key.NodePublic{}, discoRXPathUDP)
			punchBufPool.Put(bufPtr)
			continue
		case packetLooksLikeSTUNBinding:
			if buildfeatures.HasNATTraversal {
				de.c.netChecker.ReceiveSTUNPacket(pkt, src)
			}
			punchBufPool.Put(bufPtr)
			continue
		}

		if !de.c.havePrivateKey.Load() {
			punchBufPool.Put(bufPtr)
			continue
		}

		now := mono.Now()
		de.lastRecvUDPAny.Store(now)
		de.noteRecvActivity(ea, now)
		de.c.metrics.inboundPacketsIPv4Total.Add(1)
		de.c.metrics.inboundBytesIPv4Total.Add(int64(n))

		res := punchReadResult{
			ep:  de,
			buf: buf,
			n:   n,
			src: src,
			release: func() {
				punchBufPool.Put(bufPtr)
			},
		}
		select {
		case de.c.punchRecvCh <- res:
		case <-ctx.Done():
			res.release()
			return
		default:
			// Drop if wireguard-go reader is backed up; never block socket reads.
			res.release()
		}
	}
}

// wantEnhancedPunchLocked reports whether de should trigger UU-style enhanced
// hole punching now.
//
// de.mu must be held.
func (de *endpoint) wantEnhancedPunchLocked(now mono.Time) bool {
	if !buildfeatures.HasNATTraversal || !hasUDPTransport || !enhancedPunchEnabled() {
		return false
	}
	if de.isWireguardOnly || de.expired || !de.derpAddr.IsValid() {
		return false
	}
	if de.bestAddr.isDirect() && now.Before(de.trustBestAddrUntil) {
		return false
	}
	if de.firstDirectFailAt.IsZero() {
		de.firstDirectFailAt = now
		return false
	}
	if now.Sub(de.firstDirectFailAt) < enhancedPunchInitialDelay {
		return false
	}
	if !de.lastEnhancedPunch.IsZero() && now.Sub(de.lastEnhancedPunch) < enhancedPunchCooldown {
		return false
	}
	return true
}

// mkReceivePunchFunc returns a [conn.ReceiveFunc] that delivers WireGuard
// packets read from endpoints' adopted punch UDP sockets into wireguard-go.
func (c *connBind) mkReceivePunchFunc() conn.ReceiveFunc {
	healthItem := c.health.ReceiveFuncStats(receivePunchName)
	if !buildfeatures.HasHealth || healthItem == nil {
		return c.receivePunch
	}
	return func(slab []byte, packets []conn.ReceivedPacket) (int, error) {
		healthItem.Enter()
		defer healthItem.Exit()
		return c.receivePunch(slab, packets)
	}
}

func (c *connBind) receivePunch(slab []byte, packets []conn.ReceivedPacket) (int, error) {
	for {
		select {
		case <-c.donec:
			return 0, net.ErrClosed
		case pr := <-c.punchRecvCh:
			if c.isClosed() {
				if pr.release != nil {
					pr.release()
				}
				return 0, net.ErrClosed
			}
			if pr.n == 0 || pr.ep == nil {
				if pr.release != nil {
					pr.release()
				}
				continue
			}
			if pr.n > len(slab) {
				pr.release()
				continue
			}
			n := copy(slab, pr.buf[:pr.n])
			pr.release()
			packets[0].Size = n
			packets[0].Offset = 0
			packets[0].Endpoint = pr.ep
			return 1, nil
		}
	}
}
