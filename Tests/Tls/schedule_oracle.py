"""Independent hashlib/hmac, and published RFC 8448 TLS (not QUIC packet) traces."""
import hashlib
import hmac
import json
from pathlib import Path

H = lambda data: hashlib.sha256(data).digest()
M = lambda key, data: hmac.new(key, data, hashlib.sha256).digest()


def expand(secret, label, context):
    label = b'tls13 ' + label.encode('ascii')
    info = b'\x00\x20' + bytes([len(label)]) + label + bytes([len(context)]) + context
    return M(secret, info + b'\x01')


def oracle(kind, a, b):
    if kind == 'hash':
        return H(a)
    if kind == 'messageHash':
        return b'\xfe\0\0\x20' + H(a)
    if kind == 'finished':
        key = expand(a, 'finished', b'')
        return key + M(key, b)
    if kind == 'application':
        return expand(a, 'c ap traffic', b) + expand(a, 's ap traffic', b)
    early = M(bytes(32), bytes(32))
    derived = expand(early, 'derived', H(b''))
    hs = M(derived, a)
    chs, shs = expand(hs, 'c hs traffic', b), expand(hs, 's hs traffic', b)
    derived_hs = expand(hs, 'derived', H(b''))
    return early + derived + hs + chs + shs + derived_hs + M(derived_hs, bytes(32))


def published():
    records = json.loads(Path(__file__).with_name('rfc8448.json').read_text())
    result = {k: [] for k in ('handshake', 'application', 'finished', 'hash', 'messageHash')}
    for section, rows in records.items():
        value = lambda action, field: next(bytes.fromhex(r['hex']) for r in rows
                                           if action in r['action'] and r['field'] == field)
        a = value('extract secret "handshake"', 'IKM')
        b = value('"tls13 c hs traffic"', 'hash')
        expected = b''.join(value(action, field) for action, field in [
            ('extract secret "early"', 'secret'), ('for handshake "tls13 derived"', 'expanded'),
            ('extract secret "handshake"', 'secret'), ('"tls13 c hs traffic"', 'expanded'),
            ('"tls13 s hs traffic"', 'expanded'), ('for master "tls13 derived"', 'expanded'),
            ('extract secret "master"', 'secret')])
        assert oracle('handshake', a, b) == expected
        result['handshake'].append((f'rfc8448-{section}', a, b))
        digest = value('"tls13 c ap traffic"', 'hash')
        assert oracle('application', expected[-32:], digest) == (
            value('"tls13 c ap traffic"', 'expanded') + value('"tls13 s ap traffic"', 'expanded'))
        result['application'].append((f'rfc8448-{section}', expected[-32:], digest))
        transcript = b''
        for row in rows:
            msg = bytes.fromhex(row['hex'])
            if row['field'] not in ('ClientHello', 'ServerHello', 'HelloRetryRequest',
                                    'EncryptedExtensions', 'CertificateRequest', 'Certificate',
                                    'CertificateVerify', 'Finished'):
                continue
            if row['field'] == 'ServerHello' and msg[6:38] == bytes.fromhex(
                    'cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c'):
                result['messageHash'].append((f'rfc8448-{section}-ch1', transcript, b''))
                transcript = b'\xfe\0\0\x20' + H(transcript)
            if row['field'] == 'Finished':
                endpoint = 'server' if '{server}' in row['action'] else 'client'
                key = expected[128:160] if endpoint == 'server' else expected[96:128]
                got = oracle('finished', key, H(transcript))
                assert got == value('{' + endpoint + '}  calculate finished', 'expanded') + msg[4:]
                result['finished'].append((f'rfc8448-{section}-{endpoint}', key, H(transcript)))
            transcript += msg
            if row['field'] == 'ServerHello' and msg[6:38] != bytes.fromhex(
                    'cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c'):
                assert H(transcript) == b
                result['hash'].append((f'rfc8448-{section}-hello', transcript, b''))
            if row['field'] == 'Finished' and '{server}' in row['action']:
                assert H(transcript) == digest
                result['hash'].append((f'rfc8448-{section}-server-finished', transcript, b''))
    return result
