// Test-only Go crypto/tls QUICConn oracle. No runtime production dependency.
package main

import (
	"bytes"
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"time"
)

type recorder struct{ Reads []string }

func (r *recorder) Read(p []byte) (int, error) {
	n, err := rand.Read(p)
	r.Reads = append(r.Reads, hex.EncodeToString(p[:n]))
	return n, err
}

type event struct {
	Endpoint, Kind, Level, Data string
	Suite                       uint16
}
type trace struct {
	Name                       string
	Events                     []event
	ClientRandom, ServerRandom []string
	KeyLog                     string
}
type endpoint struct {
	name   string
	conn   *tls.QUICConn
	random *recorder
}

func certificate() (tls.Certificate, error) {
	pub, key, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return tls.Certificate{}, err
	}
	template := &x509.Certificate{SerialNumber: big.NewInt(1),
		Subject: pkix.Name{CommonName: "test-only"}, NotBefore: time.Unix(0, 0),
		NotAfter: time.Unix(4102444800, 0), KeyUsage: x509.KeyUsageDigitalSignature}
	der, err := x509.CreateCertificate(rand.Reader, template, template, pub, key)
	return tls.Certificate{Certificate: [][]byte{der}, PrivateKey: key}, err
}

func endpoints(retry bool, log *bytes.Buffer) (endpoint, endpoint, error) {
	cert, err := certificate()
	if err != nil {
		return endpoint{}, endpoint{}, err
	}
	cr, sr := &recorder{}, &recorder{}
	// InsecureSkipVerify is deliberately test-only: production identity belongs to main.
	cc := &tls.Config{MinVersion: tls.VersionTLS13, InsecureSkipVerify: true,
		NextProtos: []string{"libp2p"}, Certificates: []tls.Certificate{cert}, Rand: cr,
		CurvePreferences: []tls.CurveID{tls.X25519, tls.CurveP256}, KeyLogWriter: log}
	sc := &tls.Config{MinVersion: tls.VersionTLS13, NextProtos: []string{"libp2p"},
		Certificates: []tls.Certificate{cert}, ClientAuth: tls.RequireAnyClientCert, Rand: sr,
		CurvePreferences: []tls.CurveID{tls.X25519}, KeyLogWriter: log}
	if retry {
		sc.CurvePreferences = []tls.CurveID{tls.CurveP256}
	}
	client := tls.QUICClient(&tls.QUICConfig{TLSConfig: cc})
	server := tls.QUICServer(&tls.QUICConfig{TLSConfig: sc})
	client.SetTransportParameters([]byte{0, 0})
	server.SetTransportParameters([]byte{0, 0})
	return endpoint{"client", client, cr}, endpoint{"server", server, sr}, nil
}

func drain(from, to endpoint, result *trace) (bool, error) {
	progress := false
	for {
		e := from.conn.NextEvent()
		if e.Kind == tls.QUICNoEvent {
			return progress, nil
		}
		progress = true
		data := append([]byte{}, e.Data...)
		kind := fmt.Sprint(int(e.Kind))
		switch e.Kind {
		case tls.QUICWriteData:
			kind = "write"
		case tls.QUICSetReadSecret:
			kind = "read-secret"
		case tls.QUICSetWriteSecret:
			kind = "write-secret"
		}
		result.Events = append(result.Events, event{from.name, kind, e.Level.String(), hex.EncodeToString(data), e.Suite})
		if e.Kind != tls.QUICWriteData {
			continue
		}
		// Deliberately fragment crypto streams; no TLS record envelope.
		for pos := 0; pos < len(data); {
			n := 1 + (pos % 37)
			if n > len(data)-pos {
				n = len(data) - pos
			}
			if err := to.conn.HandleData(e.Level, data[pos:pos+n]); err != nil {
				return false, err
			}
			pos += n
		}
	}
}

func run(retry bool) (trace, error) {
	var log bytes.Buffer
	client, server, err := endpoints(retry, &log)
	if err != nil {
		return trace{}, err
	}
	defer client.conn.Close()
	defer server.conn.Close()
	result := trace{Name: "mutual-auth"}
	if retry {
		result.Name = "mutual-auth-hrr"
	}
	if err := client.conn.Start(context.Background()); err != nil {
		return result, err
	}
	if err := server.conn.Start(context.Background()); err != nil {
		return result, err
	}
	for round := 0; round < 20; round++ {
		a, err := drain(client, server, &result)
		if err != nil {
			return result, err
		}
		b, err := drain(server, client, &result)
		if err != nil {
			return result, err
		}
		if !a && !b {
			break
		}
	}
	if !client.conn.ConnectionState().HandshakeComplete || !server.conn.ConnectionState().HandshakeComplete {
		return result, fmt.Errorf("incomplete handshake")
	}
	if client.conn.ConnectionState().CipherSuite != tls.TLS_AES_128_GCM_SHA256 {
		return result, fmt.Errorf("unexpected cipher")
	}
	if len(server.conn.ConnectionState().PeerCertificates) != 1 {
		return result, fmt.Errorf("missing mutual authentication")
	}
	if err := server.conn.SendSessionTicket(tls.QUICSessionTicketOptions{}); err != nil {
		return result, err
	}
	if _, err := drain(server, client, &result); err != nil {
		return result, err
	}
	result.ClientRandom, result.ServerRandom = client.random.Reads, server.random.Reads
	result.KeyLog = log.String()
	return result, nil
}

func main() {
	results := []trace{}
	for _, retry := range []bool{false, true} {
		result, err := run(retry)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		results = append(results, result)
	}
	if err := json.NewEncoder(os.Stdout).Encode(results); err != nil {
		panic(err)
	}
}
