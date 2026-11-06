package main

import "testing"

func TestShouldRejectNonLoopbackOrNonQUICAddresses(t *testing.T) {
	for _, address := range []string{
		"/ip4/0.0.0.0/udp/0/quic-v1",
		"/ip4/192.0.2.1/udp/1/quic-v1",
		"/ip4/127.0.0.1/tcp/1",
		"/dns4/localhost/udp/1/quic-v1",
		"/ip6/::/udp/1/quic-v1",
		"/ip4/127.0.0.1/udp/1/quic-v1/p2p-circuit",
		"/ip4/127.0.0.1/ip4/192.0.2.1/udp/1/quic-v1",
	} {
		if _, err := localQUIC(address); err == nil {
			t.Fatalf("should reject %s", address)
		}
	}
}

func TestShouldAcceptLoopbackQUICAddresses(t *testing.T) {
	for _, address := range []string{"/ip4/127.0.0.1/udp/0/quic-v1", "/ip6/::1/udp/1/quic-v1"} {
		if _, err := localQUIC(address); err != nil {
			t.Fatalf("should accept %s", address)
		}
	}
}
