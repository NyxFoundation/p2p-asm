// Test-only protobuf and Peer ID oracle using the pinned interop module.
package main

import (
	"bufio"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"

	"github.com/libp2p/go-libp2p/core/crypto"
	pb "github.com/libp2p/go-libp2p/core/crypto/pb"
	"github.com/libp2p/go-libp2p/core/peer"
	"google.golang.org/protobuf/proto"
)

type result struct {
	OK bool `json:"ok"`
	Kind int `json:"kind"`
	Data string `json:"data"`
	PeerID string `json:"peerId"`
}

func inspect(data []byte) result {
	var key pb.PublicKey
	if err := proto.Unmarshal(data, &key); err != nil || key.Type == nil {
		return result{}
	}
	kind := int(key.GetType())
	if (kind != 1 && kind != 2) || len(key.Data) != 31+kind {
		return result{}
	}
	r := result{OK: true, Kind: kind, Data: hex.EncodeToString(key.Data)}
	pub, err := crypto.UnmarshalPublicKey(data)
	if err == nil {
		id, err := peer.IDFromPublicKey(pub)
		if err == nil {
			r.PeerID = hex.EncodeToString([]byte(id))
		}
	}
	return r
}

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	encoder := json.NewEncoder(os.Stdout)
	for scanner.Scan() {
		data, err := hex.DecodeString(scanner.Text())
		if err != nil { panic("invalid oracle fixture") }
		if err := encoder.Encode(inspect(data)); err != nil { panic("oracle output failed") }
	}
	if scanner.Err() != nil {
		fmt.Fprintln(os.Stderr, "oracle input failed")
		os.Exit(1)
	}
}
