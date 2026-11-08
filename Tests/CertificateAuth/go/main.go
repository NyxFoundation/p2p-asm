// Test-only real TLS counterpart. All production signing/authentication requests
// made by the ASM endpoint go through bridge.py's actual RV64/model/QEMU paths.
package main

import (
	"bytes"
	"crypto"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"

	ic "github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/peer"
	libp2ptls "github.com/libp2p/go-libp2p/p2p/security/tls"
)

type input struct {
	DER, Seed, Peer, HostSeed, Directory, Bridge, Prefix, Qemu string
	HostKind, Role int
}

type request struct {
	Operation string `json:"operation"`
	Label string `json:"label"`
	DER string `json:"der"`
	Seed string `json:"seed,omitempty"`
	Digest string `json:"digest,omitempty"`
	Signature string `json:"signature,omitempty"`
	Expected string `json:"expected,omitempty"`
	Role int `json:"role"`
	UTCNs int64 `json:"utcNs"`
	Prefix string `json:"prefix"`
	Qemu string `json:"qemu"`
}

func decode(value string) ([]byte, error) { return hex.DecodeString(value) }

func invoke(in input, r request) ([]byte, error) {
	r.Prefix, r.Qemu = in.Prefix, in.Qemu
	encoded, err := json.Marshal(r)
	if err != nil { return nil, err }
	path := filepath.Join(in.Directory, r.Label+".json")
	if err := os.WriteFile(path, encoded, 0600); err != nil { return nil, err }
	command := exec.Command("python3", in.Bridge, path)
	command.Stderr = os.Stderr
	output, err := command.Output()
	if err != nil { return nil, fmt.Errorf("actual ASM %s: %w", r.Operation, err) }
	return hex.DecodeString(strings.TrimSpace(string(output)))
}

type asmSigner struct { in input; public ed25519.PublicKey }
func (s asmSigner) Public() crypto.PublicKey { return s.public }
func (s asmSigner) Sign(_ io.Reader, message []byte, opts crypto.SignerOpts) ([]byte, error) {
	if opts.HashFunc() != 0 || len(message) != 130 { return nil, errors.New("unexpected Ed25519 TLS input") }
	context := "TLS 1.3, server CertificateVerify"
	if s.in.Role == 2 { context = "TLS 1.3, client CertificateVerify" }
	want := append(bytes.Repeat([]byte{32}, 64), []byte(context)...)
	want = append(want, 0)
	if !bytes.Equal(message[:98], want) { return nil, errors.New("TLS context mismatch") }
	return invoke(s.in, request{Operation:"cv-sign", Label:"asm-sign", DER:s.in.DER,
		Seed:s.in.Seed, Digest:hex.EncodeToString(message[98:]), Role:s.in.Role})
}

type captureSigner struct { key ed25519.PrivateKey; in input; der []byte; request *request }
func (s captureSigner) Public() crypto.PublicKey { return s.key.Public() }
func (s captureSigner) Sign(random io.Reader, message []byte, opts crypto.SignerOpts) ([]byte, error) {
	if len(message) != 130 || opts.HashFunc() != 0 { return nil, errors.New("unexpected counterpart TLS input") }
	signature, err := s.key.Sign(random, message, opts)
	if err != nil { return nil, err }
	role := 3-s.in.Role
	context := "TLS 1.3, server CertificateVerify"
	if role == 2 { context = "TLS 1.3, client CertificateVerify" }
	want := append(append(bytes.Repeat([]byte{32},64), []byte(context)...),0)
	if !bytes.Equal(message[:98],want) { return nil, errors.New("counterpart TLS context mismatch") }
	*s.request = request{Operation:"cv-verify", Label:"counterpart-cv", DER:hex.EncodeToString(s.der),
		Digest:hex.EncodeToString(message[98:]), Signature:hex.EncodeToString(signature), Role:role}
	return signature, nil
}

func identity(in input) (ic.PrivKey, error) {
	seed, err := decode(in.HostSeed)
	if err != nil { return nil, err }
	if in.HostKind == 1 { return ic.UnmarshalEd25519PrivateKey(ed25519.NewKeyFromSeed(seed)) }
	return ic.UnmarshalSecp256k1PrivateKey(seed)
}

func counterpartCertificate(host ic.PrivKey) ([]byte, ed25519.PrivateKey, error) {
	public, secret, err := ed25519.GenerateKey(rand.Reader)
	if err != nil { return nil, nil, err }
	extension, err := libp2ptls.GenerateSignedExtension(host, public)
	if err != nil { return nil, nil, err }
	template := &x509.Certificate{SerialNumber:big.NewInt(1),
		Subject:pkix.Name{CommonName:"go-counterpart"}, NotBefore:time.Now().Add(-time.Hour),
		NotAfter:time.Now().Add(time.Hour), ExtraExtensions:[]pkix.Extension{extension}}
	der, err := x509.CreateCertificate(rand.Reader,template,template,public,secret)
	return der,secret,err
}

func configs(in input, captured *request) (*tls.Config, *tls.Config, error) {
	host, err := identity(in)
	if err != nil { return nil,nil,err }
	id, err := peer.IDFromPrivateKey(host)
	if err != nil { return nil,nil,err }
	real, err := libp2ptls.NewIdentity(host)
	if err != nil { return nil,nil,err }
	asmID, err := decode(in.Peer)
	if err != nil { return nil,nil,err }
	remote, _ := real.ConfigForPeer(peer.ID(asmID))
	der, secret, err := counterpartCertificate(host)
	if err != nil { return nil,nil,err }
	remote.Certificates = []tls.Certificate{{Certificate:[][]byte{der},
		PrivateKey:captureSigner{secret,in,der,captured}}}
	raw, err := decode(in.DER)
	if err != nil { return nil,nil,err }
	parsed, err := x509.ParseCertificate(raw)
	if err != nil { return nil,nil,err }
	if err := parsed.CheckSignature(parsed.SignatureAlgorithm,parsed.RawTBSCertificate,parsed.Signature); err != nil {
		return nil,nil,err
	}
	public, ok := parsed.PublicKey.(ed25519.PublicKey)
	if !ok { return nil,nil,errors.New("ASM certificate is not Ed25519") }
	local := &tls.Config{MinVersion:tls.VersionTLS13,MaxVersion:tls.VersionTLS13,
		NextProtos:[]string{"libp2p"},InsecureSkipVerify:true,ClientAuth:tls.RequireAnyClientCert,
		Certificates:[]tls.Certificate{{Certificate:[][]byte{raw},PrivateKey:asmSigner{in,public}}}}
	local.VerifyPeerCertificate = func(raw [][]byte, _ [][]*x509.Certificate) error {
		if len(raw) != 1 { return errors.New("expected exactly one certificate") }
		expected := ""
		if in.Role == 2 { expected = hex.EncodeToString([]byte(id)) }
		actual, err := invoke(in,request{Operation:"auth",Label:"counterpart-auth",DER:hex.EncodeToString(raw[0]),
			Role:3-in.Role,Expected:expected,UTCNs:time.Now().UnixNano()})
		if err != nil { return err }
		if !bytes.Equal(actual,[]byte(id)) { return errors.New("authenticated peer mismatch") }
		return nil
	}
	return local,remote,nil
}

func handshake(in input) error {
	var captured request
	local,remote,err := configs(in,&captured)
	if err != nil { return err }
	a,b := net.Pipe()
	defer a.Close(); defer b.Close()
	deadline := time.Now().Add(15*time.Minute)
	if err := a.SetDeadline(deadline); err != nil { return err }
	if err := b.SetDeadline(deadline); err != nil { return err }
	var first,second *tls.Conn
	if in.Role == 1 { first,second = tls.Server(a,local),tls.Client(b,remote) } else {
		first,second = tls.Client(a,local),tls.Server(b,remote)
	}
	errors := make(chan error,2)
	go func(){ errors <- first.Handshake() }()
	go func(){ errors <- second.Handshake() }()
	for i:=0;i<2;i++ { if err:= <-errors; err != nil { return err } }
	if !first.ConnectionState().HandshakeComplete || !second.ConnectionState().HandshakeComplete {
		return fmt.Errorf("TLS handshake did not complete")
	}
	if first.ConnectionState().NegotiatedProtocol != "libp2p" { return fmt.Errorf("ALPN mismatch") }
	if captured.Operation == "" { return fmt.Errorf("missing counterpart CertificateVerify") }
	if _,err := invoke(in,captured); err != nil { return err }
	return os.WriteFile(filepath.Join(in.Directory,"handshake-complete.txt"),
		[]byte("real go-libp2p TLS 1.3; ASM issue/auth/CV sign/CV verify; both Finished; ALPN libp2p\n"),0600)
}

func main() {
	if len(os.Args)!=2 { panic("usage: certificate-counterpart input.json") }
	raw,err:=os.ReadFile(os.Args[1]); if err!=nil { panic(err) }
	var in input
	if err=json.Unmarshal(raw,&in);err!=nil { panic(err) }
	if err=handshake(in);err!=nil { panic(err) }
	fmt.Println("PASS real TLS counterpart, actual ASM authentication and CertificateVerify")
}
