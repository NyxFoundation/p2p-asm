"""Independent Python hashlib/hmac and OpenSSL-backed cryptography oracle."""
import hmac
import struct
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from vectors import *

SALT = hx('38762cf7f55934b34d179ae6a4c80cadccbb7f0a')
RETRY_KEY = hx('be0c690b9f66575a1d766b54e368c84e')
RETRY_NONCE = hx('461599d35d632bf2239825bb')

def expand(secret, label, n):
    label = b'tls13 ' + label.encode('ascii')
    info = n.to_bytes(2, 'big') + bytes([len(label)]) + label + b'\0'
    return hmac.digest(secret, info+b'\1', 'sha256')[:n]

def keys(secret):
    return expand(secret, 'quic key', 16)+expand(secret, 'quic iv', 12)+expand(secret, 'quic hp', 16)

def initial(cid):
    secret = hmac.digest(SALT, cid, 'sha256')
    client, server = (expand(secret, label, 32) for label in ('client in', 'server in'))
    return secret+client+server+keys(client)+keys(server)

def nonce(iv, pn):
    return (int.from_bytes(iv, 'big') ^ pn).to_bytes(12, 'big')

def reconstruct(expected, truncated, count):
    if expected > 2**62 or not 1 <= count <= 4 or truncated >= 1 << (8*count):
        raise ValueError('PN metadata')
    window = 1 << (8*count)
    candidate = (expected & ~(window-1)) | truncated
    if candidate <= expected-window//2 and candidate < 2**62-window:
        candidate += window
    elif candidate > expected+window//2 and candidate >= window:
        candidate -= window
    if candidate >= 2**62:
        raise ValueError('PN exhaustion')
    return candidate

def hp(key, sample):
    enc = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return (enc.update(sample)+enc.finalize())[:5]

def protect(k, packet, offset, pn):
    count = (packet[0] & 3)+1
    header = packet[:offset] + pn.to_bytes(8, 'big')[-count:]
    body = AESGCM(k[:16]).encrypt(nonce(k[16:28], pn), packet[offset+count:], header)
    result = bytearray(header+body)
    mask = hp(k[28:], result[offset+4:offset+20])
    result[0] ^= mask[0] & (15 if result[0] & 128 else 31)
    for i in range(count):
        result[offset+i] ^= mask[1+i]
    return bytes(result)

def unprotect(k, packet, offset, expected):
    mask = hp(k[28:], packet[offset+4:offset+20])
    first = packet[0] ^ (mask[0] & (15 if packet[0] & 128 else 31))
    count = (first & 3)+1
    header = bytearray(packet[:offset+count])
    header[0] = first
    for i in range(count):
        header[offset+i] ^= mask[1+i]
    pn = reconstruct(expected, int.from_bytes(header[offset:], 'big'), count)
    plain = AESGCM(k[:16]).decrypt(nonce(k[16:28], pn), packet[len(header):], bytes(header))
    return struct.pack('<QQ', pn, len(header))+header+plain

def oracle(kind, c):
    if kind == 'initial': return initial(c.a)
    if kind == 'keys': return keys(c.a)
    if kind == 'update':
        secret = expand(c.a, 'quic ku', 32)
        return secret+keys(secret)[:28]
    if kind == 'nonce': return nonce(c.a, c.pn)
    if kind == 'number': return struct.pack('<Q', reconstruct(c.pn, c.off, c.hlen))
    if kind == 'seal': return protect(c.a, c.b, c.off, c.pn)
    if kind == 'open': return unprotect(c.a, c.b, c.off, c.pn)
    retry = c.b[:-16] if kind == 'retrycheck' else c.b
    tag = AESGCM(RETRY_KEY).encrypt(RETRY_NONCE, b'', bytes([len(c.a)])+c.a+retry)
    if kind == 'retrycheck':
        if not hmac.compare_digest(tag, c.b[-16:]): raise ValueError('Retry tag')
        return b''
    return tag

def published():
    assert initial(CID) == INITIAL+CLIENT_SECRET+SERVER_SECRET+CLIENT_KEYS+SERVER_KEYS
    for i,(k,h,p,packet,pn,count) in enumerate((
        (CLIENT_KEYS,CLIENT_HEADER,CLIENT_PAYLOAD,CLIENT_PACKET,2,4),
        (SERVER_KEYS,SERVER_HEADER,SERVER_PAYLOAD,SERVER_PACKET,1,2))):
        off = len(h)-count
        assert protect(k,h+p,off,pn) == packet
        assert packet[off+4:off+20] == SAMPLES[i]
        assert hp(k[28:], SAMPLES[i]) == MASKS[i]
        assert unprotect(k,packet,off,pn) == struct.pack('<QQ',pn,len(h))+h+p
    assert AESGCM(RETRY_KEY).encrypt(RETRY_NONCE,b'',bytes([8])+CID+RETRY[:-16]) == RETRY[-16:]
