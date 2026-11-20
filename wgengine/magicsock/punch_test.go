// Copyright (c) Tailscale Inc & contributors
// SPDX-License-Identifier: BSD-3-Clause

package magicsock

import (
	"context"
	"errors"
	"fmt"
	mathrand "math/rand/v2"
	"net"
	"net/netip"
	"sync"
	"testing"
	"time"

	"tailscale.com/disco"
	"tailscale.com/net/stun"
	"tailscale.com/tailcfg"
	"tailscale.com/tstest"
	"tailscale.com/types/logger"
	"tailscale.com/types/netmap"
	"tailscale.com/types/nettype"
	"tailscale.com/types/opt"
)

func TestClassifyNATSamples(t *testing.T) {
	tests := []struct {
		name          string
		samples       []netip.AddrPort
		mappingVaries opt.Bool
		wantType      disco.NATType
		wantDelta     int16
	}{
		{
			name: "cone_explicit",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("27.18.240.102:17210"),
				netip.MustParseAddrPort("27.18.240.102:17210"),
			},
			mappingVaries: opt.NewBool(false),
			wantType:      disco.NATCone,
		},
		{
			name: "cone_from_identical_samples",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("27.18.240.102:17210"),
				netip.MustParseAddrPort("27.18.240.102:17210"),
			},
			wantType: disco.NATCone,
		},
		{
			name: "linear_symmetric_step_1",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("59.173.186.5:48630"),
				netip.MustParseAddrPort("59.173.186.5:48631"),
				netip.MustParseAddrPort("59.173.186.5:48632"),
			},
			mappingVaries: opt.NewBool(true),
			wantType:      disco.NATLinearSymmetric,
			wantDelta:     1,
		},
		{
			name: "linear_symmetric_step_2",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("221.235.68.226:30430"),
				netip.MustParseAddrPort("221.235.68.226:30432"),
				netip.MustParseAddrPort("221.235.68.226:30434"),
			},
			wantType:  disco.NATLinearSymmetric,
			wantDelta: 2,
		},
		{
			name: "random_multi_pool_symmetric",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("221.235.68.226:28948"),
				netip.MustParseAddrPort("221.235.68.226:30445"),
				netip.MustParseAddrPort("221.235.68.226:28943"),
			},
			mappingVaries: opt.NewBool(true),
			wantType:      disco.NATRandomSymmetric,
		},
		{
			name: "single_sample_unknown",
			samples: []netip.AddrPort{
				netip.MustParseAddrPort("221.235.68.226:28154"),
			},
			wantType: disco.NATUnknown,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotType, _, gotDelta := classifyNATSamples(tt.samples, tt.mappingVaries)
			if gotType != tt.wantType {
				t.Errorf("natType = %v, want %v", gotType, tt.wantType)
			}
			if gotDelta != tt.wantDelta {
				t.Errorf("portDelta = %d, want %d", gotDelta, tt.wantDelta)
			}
		})
	}
}

func TestPredictedAndBirthdayPorts(t *testing.T) {
	pred := predictedPorts(30000, 2, 10, 20)
	if len(pred) != 31 {
		t.Fatalf("predictedPorts len = %d, want 31", len(pred))
	}
	if pred[0] != 30002 {
		t.Errorf("predictedPorts[0] = %d, want 30002", pred[0])
	}
	seen := make(map[uint16]bool)
	for _, p := range pred {
		if p < 1024 {
			t.Errorf("privileged port %d in predictedPorts", p)
		}
		if seen[p] {
			t.Errorf("duplicate port %d in predictedPorts", p)
		}
		seen[p] = true
	}

	bday := birthdayPorts(30000, 1200)
	if len(bday) != 1200 {
		t.Fatalf("birthdayPorts len = %d, want 1200", len(bday))
	}
	seen = make(map[uint16]bool)
	nearCount := 0
	for _, p := range bday {
		if p < 1024 {
			t.Errorf("privileged port %d in birthdayPorts", p)
		}
		if seen[p] {
			t.Errorf("duplicate port %d in birthdayPorts", p)
		}
		seen[p] = true
		if p >= 30000-4096 && p <= 30000+4096 {
			nearCount++
		}
	}
	if nearCount < 300 {
		t.Errorf("expected at least 300 ports near basePort 30000, got %d", nearCount)
	}
}

// --- In-memory NAT4 (Symmetric) <-> NAT3 (Port-Restricted Cone) simulator ---

type simPacket struct {
	data []byte
	src  netip.AddrPort
}

type simNATMode int

const (
	simNATPortRestrictedCone simNATMode = iota // NAT3: fixed public port per local port, strict 5-tuple inbound filter
	simNATLinearSymmetric                      // NAT4 Linear: +step public port per new destination 5-tuple
	simNATRandomSymmetric                      // NAT4 Random/Multi-pool: random public port per new destination 5-tuple
)

type simNATRouter struct {
	mu       sync.Mutex
	world    *simWorld
	pubIP    netip.Addr
	lanIP    netip.Addr
	mode     simNATMode
	step     uint16
	nextPort uint16
	poolLo   uint16
	poolHi   uint16

	// localPort -> socket
	sockets map[uint16]*simUDPConn
	// Cone mode: localPort -> pubPort
	coneMap map[uint16]uint16
	// Cone inbound filter: (localPort, remotePubAddr) -> allowed
	coneAllowed map[simFiveTuple]bool
	// Symmetric mode: (localPort, remotePubAddr) -> pubPort
	symOut map[simFiveTuple]uint16
	// Symmetric inbound reverse: (pubPort, remotePubAddr) -> localPort
	symIn map[simFiveTuple]uint16
	// Reverse pubPort -> localPort for Cone
	coneRev map[uint16]uint16
}

type simFiveTuple struct {
	port uint16
	peer netip.AddrPort
}

type simWorld struct {
	mu      sync.Mutex
	routers map[netip.Addr]*simNATRouter
	// stunServers responds to STUN binding requests on these public addresses.
	stunAddrs map[netip.AddrPort]bool
}

func newSimWorld() *simWorld {
	return &simWorld{
		routers:   make(map[netip.Addr]*simNATRouter),
		stunAddrs: make(map[netip.AddrPort]bool),
	}
}

func (w *simWorld) addRouter(r *simNATRouter) {
	w.mu.Lock()
	defer w.mu.Unlock()
	r.world = w
	r.sockets = make(map[uint16]*simUDPConn)
	r.coneMap = make(map[uint16]uint16)
	r.coneRev = make(map[uint16]uint16)
	r.coneAllowed = make(map[simFiveTuple]bool)
	r.symOut = make(map[simFiveTuple]uint16)
	r.symIn = make(map[simFiveTuple]uint16)
	w.routers[r.pubIP] = r
}

func (w *simWorld) route(fromPub netip.AddrPort, dst netip.AddrPort, payload []byte) {
	w.mu.Lock()
	isSTUN := w.stunAddrs[dst]
	targetRouter := w.routers[dst.Addr()]
	srcRouter := w.routers[fromPub.Addr()]
	w.mu.Unlock()

	if isSTUN && srcRouter != nil {
		if txid, err := stun.ParseBindingRequest(payload); err == nil {
			resp := stun.Response(txid, fromPub)
			srcRouter.deliverInbound(dst, fromPub.Port(), resp)
		}
		return
	}
	if targetRouter != nil {
		targetRouter.deliverInbound(fromPub, dst.Port(), payload)
	}
}

func (r *simNATRouter) allocPublicPortLocked() uint16 {
	if r.mode == simNATRandomSymmetric {
		span := int(r.poolHi - r.poolLo + 1)
		for range 1000 {
			p := r.poolLo + uint16(mathrand.IntN(span))
			// Avoid reusing an already-allocated port on this router if possible.
			used := false
			for _, existing := range r.symOut {
				if existing == p {
					used = true
					break
				}
			}
			if !used {
				return p
			}
		}
		return r.poolLo + uint16(mathrand.IntN(span))
	}
	p := r.nextPort
	r.nextPort += max(r.step, 1)
	if r.nextPort < 1024 {
		r.nextPort = 20000
	}
	return p
}

func (r *simNATRouter) sendOutbound(localPort uint16, dst netip.AddrPort, payload []byte) {
	r.mu.Lock()
	var pubPort uint16
	switch r.mode {
	case simNATPortRestrictedCone:
		var ok bool
		pubPort, ok = r.coneMap[localPort]
		if !ok {
			pubPort = r.allocPublicPortLocked()
			r.coneMap[localPort] = pubPort
			r.coneRev[pubPort] = localPort
		}
		r.coneAllowed[simFiveTuple{port: localPort, peer: dst}] = true
	case simNATLinearSymmetric, simNATRandomSymmetric:
		key := simFiveTuple{port: localPort, peer: dst}
		var ok bool
		pubPort, ok = r.symOut[key]
		if !ok {
			pubPort = r.allocPublicPortLocked()
			r.symOut[key] = pubPort
			r.symIn[simFiveTuple{port: pubPort, peer: dst}] = localPort
		}
	}
	pubIP := r.pubIP
	r.mu.Unlock()

	cp := append([]byte(nil), payload...)
	r.world.route(netip.AddrPortFrom(pubIP, pubPort), dst, cp)
}

func (r *simNATRouter) deliverInbound(src netip.AddrPort, dstPubPort uint16, payload []byte) {
	r.mu.Lock()
	var sock *simUDPConn
	switch r.mode {
	case simNATPortRestrictedCone:
		if localPort, ok := r.coneRev[dstPubPort]; ok {
			// Port-Restricted Cone strictly requires prior outbound packet to exact src IP:Port!
			if r.coneAllowed[simFiveTuple{port: localPort, peer: src}] {
				sock = r.sockets[localPort]
			}
		}
	case simNATLinearSymmetric, simNATRandomSymmetric:
		if localPort, ok := r.symIn[simFiveTuple{port: dstPubPort, peer: src}]; ok {
			sock = r.sockets[localPort]
		}
	}
	r.mu.Unlock()

	if sock != nil {
		sock.enqueue(simPacket{data: payload, src: src})
	}
}

func (r *simNATRouter) ListenPacket(ctx context.Context, network, address string) (net.PacketConn, error) {
	if network == "udp6" {
		return nil, errors.New("ipv6 disabled in simNATRouter")
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	port := uint16(40000 + len(r.sockets))
	for r.sockets[port] != nil {
		port++
	}
	c := &simUDPConn{
		router:    r,
		localAddr: netip.AddrPortFrom(r.lanIP, port),
		rxCh:      make(chan simPacket, 256),
		closedCh:  make(chan struct{}),
	}
	r.sockets[port] = c
	return c, nil
}

type simUDPConn struct {
	router    *simNATRouter
	localAddr netip.AddrPort
	rxCh      chan simPacket
	closedCh  chan struct{}
	closeOnce sync.Once
	mu        sync.Mutex
	deadline  time.Time
}

func (c *simUDPConn) enqueue(p simPacket) {
	select {
	case <-c.closedCh:
	case c.rxCh <- p:
	default:
	}
}

func (c *simUDPConn) ReadFromUDPAddrPort(b []byte) (int, netip.AddrPort, error) {
	c.mu.Lock()
	dl := c.deadline
	c.mu.Unlock()

	var timerC <-chan time.Time
	var timer *time.Timer
	if !dl.IsZero() {
		d := time.Until(dl)
		if d <= 0 {
			return 0, netip.AddrPort{}, simTimeoutErr{}
		}
		timer = time.NewTimer(d)
		defer timer.Stop()
		timerC = timer.C
	}

	select {
	case <-c.closedCh:
		return 0, netip.AddrPort{}, net.ErrClosed
	case <-timerC:
		return 0, netip.AddrPort{}, simTimeoutErr{}
	case p := <-c.rxCh:
		n := copy(b, p.data)
		return n, p.src, nil
	}
}

func (c *simUDPConn) ReadFrom(p []byte) (int, net.Addr, error) {
	n, src, err := c.ReadFromUDPAddrPort(p)
	if err != nil {
		return 0, nil, err
	}
	return n, net.UDPAddrFromAddrPort(src), nil
}

func (c *simUDPConn) WriteToUDPAddrPort(b []byte, addr netip.AddrPort) (int, error) {
	select {
	case <-c.closedCh:
		return 0, net.ErrClosed
	default:
	}
	c.router.sendOutbound(c.localAddr.Port(), addr, b)
	return len(b), nil
}

func (c *simUDPConn) WriteTo(p []byte, addr net.Addr) (int, error) {
	ua, ok := addr.(*net.UDPAddr)
	if !ok {
		return 0, fmt.Errorf("unexpected addr %T", addr)
	}
	ap := ua.AddrPort()
	return c.WriteToUDPAddrPort(p, netip.AddrPortFrom(ap.Addr().Unmap(), ap.Port()))
}

func (c *simUDPConn) Close() error {
	c.closeOnce.Do(func() {
		close(c.closedCh)
		c.router.mu.Lock()
		delete(c.router.sockets, c.localAddr.Port())
		c.router.mu.Unlock()
	})
	return nil
}

func (c *simUDPConn) LocalAddr() net.Addr                { return net.UDPAddrFromAddrPort(c.localAddr) }
func (c *simUDPConn) SetDeadline(t time.Time) error      { return c.SetReadDeadline(t) }
func (c *simUDPConn) SetWriteDeadline(t time.Time) error { return nil }
func (c *simUDPConn) SetReadDeadline(t time.Time) error {
	c.mu.Lock()
	c.deadline = t
	c.mu.Unlock()
	return nil
}

type simTimeoutErr struct{}

func (simTimeoutErr) Error() string   { return "i/o timeout" }
func (simTimeoutErr) Timeout() bool   { return true }
func (simTimeoutErr) Temporary() bool { return true }

var _ nettype.PacketConn = (*simUDPConn)(nil)

func runEnhancedPunchNATScenario(t *testing.T, modeA simNATMode, natTypeA disco.NATType, stepA uint16, modeB simNATMode, natTypeB disco.NATType, stepB uint16, poolSize uint16) {
	t.Helper()

	tstest.Replace(t, &enhancedPunchInitialDelay, 150*time.Millisecond)
	tstest.Replace(t, &enhancedPunchCooldown, 1*time.Second)
	tstest.Replace(t, &enhancedPunchLinearWait, 1200*time.Millisecond)
	tstest.Replace(t, &enhancedPunchBirthdayWait, 4*time.Second)

	world := newSimWorld()
	stun1 := netip.MustParseAddrPort("198.51.100.1:3478")
	world.stunAddrs[stun1] = true

	if poolSize == 0 {
		poolSize = 4096
	}

	// Node A NAT
	natA := &simNATRouter{
		pubIP:    netip.MustParseAddr("203.0.113.10"),
		lanIP:    netip.MustParseAddr("10.172.17.201"),
		mode:     modeA,
		step:     stepA,
		nextPort: 30000,
		poolLo:   28000,
		poolHi:   28000 + poolSize - 1,
	}
	// Node B NAT
	natB := &simNATRouter{
		pubIP:    netip.MustParseAddr("198.51.100.20"),
		lanIP:    netip.MustParseAddr("192.168.5.12"),
		mode:     modeB,
		step:     stepB,
		nextPort: 59047,
		poolLo:   30000,
		poolHi:   30000 + poolSize - 1,
	}
	world.addRouter(natA)
	world.addRouter(natB)

	// Shared DERP server (over localhost TCP; STUN goes through simWorld).
	derpMap, derpCleanup := runDERPAndStun(t, logger.Discard, localhostListener{}, netip.MustParseAddr("127.0.0.1"))
	t.Cleanup(derpCleanup)
	// Point STUN to our simulated STUN server so each node discovers its simulated NAT public IP:port.
	derpMap.Regions[1].Nodes[0].STUNTestIP = stun1.Addr().String()
	derpMap.Regions[1].Nodes[0].STUNPort = int(stun1.Port())

	logfA := logger.WithPrefix(t.Logf, "nodeA: ")
	logfB := logger.WithPrefix(t.Logf, "nodeB: ")

	msA := newMagicStack(t, logfA, natA, derpMap)
	t.Cleanup(msA.Close)
	msB := newMagicStack(t, logfB, natB, derpMap)
	t.Cleanup(msB.Close)

	// Provide each node's classified NAT profile (as multi-STUN netcheck would produce).
	pubA := netip.AddrPortFrom(natA.pubIP, 30000)
	if repA := msA.conn.lastNetCheckReport.Load(); repA != nil && repA.GlobalV4.IsValid() {
		pubA = repA.GlobalV4
	}
	pubB := netip.AddrPortFrom(natB.pubIP, 59047)
	if repB := msB.conn.lastNetCheckReport.Load(); repB != nil && repB.GlobalV4.IsValid() {
		pubB = repB.GlobalV4
	}

	msA.conn.punchMgr.mu.Lock()
	msA.conn.punchMgr.testNATOverride = &natProfile{
		natType:    natTypeA,
		publicAddr: pubA,
		portDelta:  int16(stepA),
		updatedAt:  time.Now(),
	}
	msA.conn.punchMgr.mu.Unlock()

	msB.conn.punchMgr.mu.Lock()
	msB.conn.punchMgr.testNATOverride = &natProfile{
		natType:    natTypeB,
		publicAddr: pubB,
		portDelta:  int16(stepB),
		updatedAt:  time.Now(),
	}
	msB.conn.punchMgr.mu.Unlock()

	// Wire both peers into each other's NetworkMap (only their STUN public addresses + DERP home).
	ipA := netip.MustParseAddr("100.64.0.1")
	ipB := netip.MustParseAddr("100.64.0.2")
	nmA := &netmap.NetworkMap{
		SelfNode: (&tailcfg.Node{
			ID:        1,
			Key:       msA.privateKey.Public(),
			Addresses: []netip.Prefix{netip.PrefixFrom(ipA, 32)},
			HomeDERP:  1,
		}).View(),
		Peers: []tailcfg.NodeView{
			(&tailcfg.Node{
				ID:         2,
				Key:        msB.privateKey.Public(),
				DiscoKey:   msB.conn.DiscoPublicKey(),
				Addresses:  []netip.Prefix{netip.PrefixFrom(ipB, 32)},
				AllowedIPs: []netip.Prefix{netip.PrefixFrom(ipB, 32)},
				Endpoints:  []netip.AddrPort{pubB},
				HomeDERP:   1,
			}).View(),
		},
		DERPMap: derpMap,
	}
	nmB := &netmap.NetworkMap{
		SelfNode: (&tailcfg.Node{
			ID:        2,
			Key:       msB.privateKey.Public(),
			Addresses: []netip.Prefix{netip.PrefixFrom(ipB, 32)},
			HomeDERP:  1,
		}).View(),
		Peers: []tailcfg.NodeView{
			(&tailcfg.Node{
				ID:         1,
				Key:        msA.privateKey.Public(),
				DiscoKey:   msA.conn.DiscoPublicKey(),
				Addresses:  []netip.Prefix{netip.PrefixFrom(ipA, 32)},
				AllowedIPs: []netip.Prefix{netip.PrefixFrom(ipA, 32)},
				Endpoints:  []netip.AddrPort{pubA},
				HomeDERP:   1,
			}).View(),
		},
		DERPMap: derpMap,
	}
	msA.conn.SetNetworkMap(nmA.SelfNode, nmA.Peers)
	if err := msA.Reconfig(wgCfgOf(msA.privateKey, nmA), nmA.Peers); err != nil {
		t.Fatalf("msA.Reconfig: %v", err)
	}
	msB.conn.SetNetworkMap(nmB.SelfNode, nmB.Peers)
	if err := msB.Reconfig(wgCfgOf(msB.privateKey, nmB), nmB.Peers); err != nil {
		t.Fatalf("msB.Reconfig: %v", err)
	}

	// Kick off WireGuard traffic from A -> B; initially flows over DERP because
	// NAT4 <-> NAT3 blocks standard CallMeMaybe.
	sendPingPacket := func(src, dst netip.Addr) []byte {
		pkt := make([]byte, 28)
		pkt[0] = 0x45 // IPv4, IHL=5
		pkt[2] = 0
		pkt[3] = byte(len(pkt))
		pkt[8] = 64 // TTL
		pkt[9] = 17 // UDP
		copy(pkt[12:16], src.AsSlice())
		copy(pkt[16:20], dst.AsSlice())
		// IPv4 header checksum
		var sum uint32
		for i := 0; i < 20; i += 2 {
			sum += uint32(pkt[i])<<8 | uint32(pkt[i+1])
		}
		for sum>>16 != 0 {
			sum = (sum & 0xffff) + (sum >> 16)
		}
		cs := ^uint16(sum)
		pkt[10] = byte(cs >> 8)
		pkt[11] = byte(cs)
		// UDP header (8 bytes)
		pkt[20], pkt[21] = 0x04, 0xd2 // sport 1234
		pkt[22], pkt[23] = 0x04, 0xd2 // dport 1234
		pkt[24], pkt[25] = 0x00, 0x08 // len 8
		return pkt
	}

	// Drive traffic from A -> B (single initiator avoids WireGuard simultaneous-handshake glare)
	// until both peers achieve direct UDP connectivity via enhanced hole punching.
	deadline := time.Now().Add(10 * time.Second)
	var directA, directB bool
	for time.Now().Before(deadline) {
		msA.tun.Outbound <- sendPingPacket(ipA, ipB)
		// Drain inbound TUN channels so wireguard-go never blocks.
		for {
			select {
			case <-msA.tun.Inbound:
			case <-msB.tun.Inbound:
			default:
				goto checked
			}
		}
	checked:
		epA, _ := msA.conn.peerMap.endpointForNodeKey(msB.privateKey.Public())
		epB, _ := msB.conn.peerMap.endpointForNodeKey(msA.privateKey.Public())
		if epA != nil && epB != nil {
			epA.mu.Lock()
			directA = epA.bestAddr.isDirect()
			hasPunchConnA := epA.punchConn != nil
			epA.mu.Unlock()

			epB.mu.Lock()
			directB = epB.bestAddr.isDirect()
			epB.mu.Unlock()

			if directA && directB && (modeA != simNATRandomSymmetric || hasPunchConnA) {
				break
			}
		}
		time.Sleep(80 * time.Millisecond)
	}

	if !directA || !directB {
		t.Fatalf("enhanced punch did not establish direct NAT4<->NAT3 connection: directA=%v directB=%v", directA, directB)
	}

	// Verify real WireGuard data now flows DIRECTLY over UDP (not DERP) in BOTH directions!
	beforeV4InA := msA.conn.metrics.inboundPacketsIPv4Total.Value()
	beforeV4InB := msB.conn.metrics.inboundPacketsIPv4Total.Value()

	for range 5 {
		msA.tun.Outbound <- sendPingPacket(ipA, ipB)
		msB.tun.Outbound <- sendPingPacket(ipB, ipA)
		time.Sleep(30 * time.Millisecond)
	}

	// Confirm packets arrived on both TUNs directly via IPv4 UDP.
	waitDeadline := time.Now().Add(2 * time.Second)
	gotDirectA, gotDirectB := false, false
	for time.Now().Before(waitDeadline) {
		select {
		case <-msA.tun.Inbound:
		case <-msB.tun.Inbound:
		default:
		}
		if msA.conn.metrics.inboundPacketsIPv4Total.Value() > beforeV4InA {
			gotDirectA = true
		}
		if msB.conn.metrics.inboundPacketsIPv4Total.Value() > beforeV4InB {
			gotDirectB = true
		}
		if gotDirectA && gotDirectB {
			break
		}
		time.Sleep(20 * time.Millisecond)
	}
	if !gotDirectA || !gotDirectB {
		t.Fatalf("expected direct IPv4 WireGuard packets after punch handover: gotDirectA=%v gotDirectB=%v", gotDirectA, gotDirectB)
	}
}

func TestEnhancedPunchRandomSymmetricToPortRestrictedCone(t *testing.T) {
	runEnhancedPunchNATScenario(t, simNATRandomSymmetric, disco.NATRandomSymmetric, 0, simNATPortRestrictedCone, disco.NATCone, 1, 4096)
}

func TestEnhancedPunchLinearSymmetricToPortRestrictedCone(t *testing.T) {
	runEnhancedPunchNATScenario(t, simNATLinearSymmetric, disco.NATLinearSymmetric, 2, simNATPortRestrictedCone, disco.NATCone, 1, 4096)
}

func TestEnhancedPunchBothLinearSymmetric(t *testing.T) {
	runEnhancedPunchNATScenario(t, simNATLinearSymmetric, disco.NATLinearSymmetric, 1, simNATLinearSymmetric, disco.NATLinearSymmetric, 1, 4096)
}

func TestEnhancedPunchBothPBASymmetric(t *testing.T) {
	// Simulates two ISP CGNAT NAT4 gateways using 512-port PBA blocks (RFC 6888).
	runEnhancedPunchNATScenario(t, simNATRandomSymmetric, disco.NATRandomSymmetric, 0, simNATRandomSymmetric, disco.NATRandomSymmetric, 0, 512)
}
