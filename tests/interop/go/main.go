// Test-only authenticated QUIC-v1 peer; never linked into the ASM runtime.
package main

import (
	"context"
	"crypto/rand"
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"net"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"

	libp2p "github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/network"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	quic "github.com/libp2p/go-libp2p/p2p/transport/quic"
	ma "github.com/multiformats/go-multiaddr"
)

var outputMu sync.Mutex

func event(kind string, fields map[string]any) {
	outputMu.Lock()
	defer outputMu.Unlock()
	fields["event"] = kind
	if err := json.NewEncoder(os.Stdout).Encode(fields); err != nil {
		slog.Error("test peer output failed")
	}
}

func localQUIC(value string) (ma.Multiaddr, error) {
	address, err := ma.NewMultiaddr(value)
	if err != nil {
		return nil, fmt.Errorf("invalid multiaddress")
	}
	ip, err := address.ValueForProtocol(ma.P_IP4)
	if err != nil {
		ip, err = address.ValueForProtocol(ma.P_IP6)
	}
	if err != nil || !net.ParseIP(ip).IsLoopback() {
		return nil, fmt.Errorf("test peers require a loopback address")
	}
	if _, err := address.ValueForProtocol(ma.P_UDP); err != nil {
		return nil, fmt.Errorf("UDP is required")
	}
	if _, err := address.ValueForProtocol(ma.P_QUIC_V1); err != nil {
		return nil, fmt.Errorf("QUIC v1 is required")
	}
	protocols := address.Protocols()
	if len(protocols) < 3 || len(protocols) > 4 ||
		(protocols[0].Code != ma.P_IP4 && protocols[0].Code != ma.P_IP6) ||
		protocols[1].Code != ma.P_UDP || protocols[2].Code != ma.P_QUIC_V1 ||
		(len(protocols) == 4 && protocols[3].Code != ma.P_P2P) {
		return nil, fmt.Errorf("invalid test address structure")
	}
	return address, nil
}

func pingPeer(ctx context.Context, node host.Host, id peer.ID, count int) {
	pingCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	results := ping.Ping(pingCtx, node, id)
	for i := 1; i <= count; i++ {
		select {
		case <-ctx.Done():
			return
		case result, ok := <-results:
			if !ok || result.Error != nil {
				event("error", map[string]any{"reason": "ping failed", "peer": id.String()})
				return
			}
			event("ping", map[string]any{"peer": id.String(), "round": i})
		}
	}
	event("done", map[string]any{"peer": id.String(), "count": count})
}

func run(ctx context.Context, listen, target, keyType string, count int) error {
	address, err := localQUIC(listen)
	if err != nil {
		return err
	}
	var remote *peer.AddrInfo
	if target != "" {
		destination, err := localQUIC(target)
		if err != nil {
			return err
		}
		remote, err = peer.AddrInfoFromP2pAddr(destination)
		if err != nil {
			return fmt.Errorf("target requires an expected Peer ID")
		}
	}
	algorithm := crypto.Ed25519
	if keyType == "secp256k1" {
		algorithm = crypto.Secp256k1
	} else if keyType != "ed25519" {
		return fmt.Errorf("unsupported identity type")
	}
	key, _, err := crypto.GenerateKeyPairWithReader(algorithm, -1, rand.Reader)
	if err != nil {
		return fmt.Errorf("identity generation failed")
	}
	node, err := libp2p.New(libp2p.Identity(key), libp2p.NoTransports,
		libp2p.Transport(quic.NewTransport), libp2p.ListenAddrs(address))
	if err != nil {
		return fmt.Errorf("QUIC listener failed")
	}
	defer node.Close()
	return serve(ctx, node, remote, count)
}

func serve(ctx context.Context, node host.Host, remote *peer.AddrInfo, count int) error {
	var started sync.Map
	node.Network().Notify(&network.NotifyBundle{ConnectedF: func(_ network.Network, conn network.Conn) {
		id := conn.RemotePeer()
		event("connected", map[string]any{"peer": id.String()})
		if _, loaded := started.LoadOrStore(id, true); !loaded {
			go pingPeer(ctx, node, id, count)
		}
	}})
	addresses, err := peer.AddrInfoToP2pAddrs(&peer.AddrInfo{ID: node.ID(), Addrs: node.Addrs()})
	if err != nil || len(addresses) == 0 {
		return fmt.Errorf("QUIC address unavailable")
	}
	event("ready", map[string]any{"peer": node.ID().String(), "address": addresses[0].String(),
		"implementation": "go-libp2p", "version": "v0.51.0"})
	if remote != nil {
		if err := node.Connect(ctx, *remote); err != nil {
			return fmt.Errorf("authenticated QUIC dial failed")
		}
	}
	<-ctx.Done()
	event("closed", map[string]any{})
	return nil
}

func main() {
	listen := flag.String("listen", "/ip4/127.0.0.1/udp/0/quic-v1", "loopback QUIC listen multiaddress")
	target := flag.String("target", "", "loopback QUIC multiaddress with expected /p2p/ ID")
	identity := flag.String("identity", "ed25519", "ed25519 or secp256k1")
	count := flag.Int("count", 3, "outbound Ping rounds per connected peer")
	lifetime := flag.Duration("lifetime", 30*time.Second, "bounded peer lifetime")
	flag.Parse()
	if *count < 1 || *count > 32 || *lifetime <= 0 || *lifetime > time.Minute || flag.NArg() != 0 {
		slog.Error("invalid test peer arguments")
		os.Exit(2)
	}
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
	defer stop()
	ctx, cancel := context.WithTimeout(ctx, *lifetime)
	defer cancel()
	if err := run(ctx, *listen, *target, *identity, *count); err != nil {
		slog.Error(err.Error())
		os.Exit(1)
	}
}
