"""Cross-check Go raw QUIC TLS flights/secrets using Python cryptography only in tests."""
import json
import os
from pathlib import Path
import struct
from cryptography.hazmat.primitives.asymmetric import ec, x25519
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat
from build import OUT, ROOT, run
from codec_oracle import decode, HRR
from schedule_oracle import H, oracle


def generate():
    OUT.mkdir(parents=True, exist_ok=True)
    go = os.environ.get('TLS_TEST_GO', 'go')
    env = dict(os.environ, GOTOOLCHAIN='go1.24.1', GOCACHE=str(OUT/'gocache'))
    version = run([go, 'version'], env=env).strip()
    assert version.startswith('go version go1.24.1 '), version
    traces = json.loads(run([go, '-C', str(ROOT/'Tests/Tls/go'), 'run', '.'], env=env))
    (OUT/'go-traces.json').write_text(json.dumps(traces, indent=2)+'\n')
    return traces


def messages(trace):
    result = []
    for e in trace['Events']:
        if e['Kind'] != 'write': continue
        data = bytes.fromhex(e['Data'])
        offset = 0
        while offset < len(data):
            size = int.from_bytes(data[offset+1:offset+4], 'big')+4
            assert size >= 4 and offset+size <= len(data)
            result.append((e['Endpoint'], data[offset:offset+size]))
            offset += size
    return result


def secret(trace, endpoint, level):
    values = {bytes.fromhex(e['Data']) for e in trace['Events'] if e['Kind'] == 'write-secret'
              and e['Endpoint'] == endpoint and e['Level'] == level}
    assert len(values) == 1
    return values.pop()


def shared(trace, server_message):
    w = struct.unpack('<64Q', decode(server_message))
    group = w[54]
    offset, size = w[56:58] if group == 29 else w[58:60]
    peer_bytes = server_message[offset:offset+size]
    for data in trace['ServerRandom']:
        candidate = bytes.fromhex(data)
        if len(candidate) != 32: continue
        if group == 29:
            private = x25519.X25519PrivateKey.from_private_bytes(candidate)
            public = private.public_key().public_bytes(Encoding.Raw, PublicFormat.Raw)
        else:
            candidate = candidate[:1]+bytes([candidate[1]^0x42])+candidate[2:]
            private = ec.derive_private_key(int.from_bytes(candidate, 'big'), ec.SECP256R1())
            public = private.public_key().public_bytes(Encoding.X962, PublicFormat.UncompressedPoint)
        if public != peer_bytes: continue
        client = [m for who,m in messages(trace) if who == 'client' and m[0] == 1][-1]
        view = struct.unpack('<64Q', decode(client))
        start, n = view[56:58] if group == 29 else view[58:60]
        peer = client[start:start+n]
        if group == 29: return private.exchange(x25519.X25519PublicKey.from_public_bytes(peer))
        return private.exchange(ec.ECDH(), ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), peer))
    raise AssertionError('Go ephemeral public key has no matching recorded test RNG read')


def verified(traces):
    result = {k: [] for k in ('handshake','application','finished','hash','messageHash')}
    for trace in traces:
        name = 'go-'+trace['Name']
        transcript, hs = b'', None
        for who, message in messages(trace):
            decode(message)
            kind = message[0]
            if kind == 4: continue
            if kind == 2 and message[6:38] == HRR:
                result['messageHash'].append((name+'-ch1', transcript, b''))
                transcript = b'\xfe\0\0\x20'+H(transcript)
            if kind == 20:
                traffic = secret(trace, who, 'Handshake')
                assert oracle('finished',traffic,H(transcript))[32:] == message[4:]
                result['finished'].append((name+'-'+who,traffic,H(transcript)))
            transcript += message
            if kind == 2 and message[6:38] != HRR:
                ecdhe = shared(trace, message)
                hs = oracle('handshake',ecdhe,H(transcript))
                assert hs[96:128] == secret(trace,'client','Handshake')
                assert hs[128:160] == secret(trace,'server','Handshake')
                result['handshake'].append((name,ecdhe,H(transcript)))
                result['hash'].append((name+'-hello',transcript,b''))
            if kind == 20 and who == 'server':
                app = oracle('application',hs[-32:],H(transcript))
                assert app == secret(trace,'client','Application')+secret(trace,'server','Application')
                result['application'].append((name,hs[-32:],H(transcript)))
                result['hash'].append((name+'-server-finished',transcript,b''))
        assert sum(1 for _,m in messages(trace) if m[0] == 11) == 2
        assert any(m[0] == 13 for _,m in messages(trace))
    return result


def load():
    return json.loads((OUT/'go-traces.json').read_text())


if __name__ == '__main__':
    print({k:len(v) for k,v in verified(generate()).items()})
