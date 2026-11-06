"""ASM-core chain fixture: Initial keys, protected packet, wire, TLS ClientHello.

Python protects a real QUIC v1 Initial packet and computes every intermediate
the chain of lowered RV64 programs must produce. Key derivation follows
RFC 9001 exactly and is cross-checked against cryptography 49 HKDF; AES-GCM and
header protection use cryptography AES primitives. No Lean runtime runs here.
"""
import hashlib
import hmac
import json
from pathlib import Path
import struct

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

BASE = 0x210000
STACK_BASE = 0x280000
STACK_SIZE = 0x4000
SP0 = STACK_BASE + STACK_SIZE
REGION_SIZE = 0x9000

OFF = {
    "dcid": 0x000, "kdfOut": 0x020, "packet": 0x100, "unpOut": 0x500,
    "packetDesc": 0x900, "frameDesc": 0x980, "tlsDesc": 0xB00, "tlsOut": 0xB40,
    "kdfDesc": 0x600, "unpDesc": 0x640, "shaTable": 0x8300,
    "kdfWork": 0x1200, "unpWork": 0x1800, "packetWork": 0x3900,
    "frameWork": 0x3B00, "tlsWork": 0x4000,
}

SALT = bytes.fromhex("38762cf7f55934b34d179ae6a4c80cadccbb7f0a")

SHA_TABLE = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]
assert len(SHA_TABLE) == 64


def hmac_sha256(key, message):
    return hmac.new(key, message, hashlib.sha256).digest()


def hkdf_extract(salt, ikm):
    return hmac_sha256(salt, ikm)


def hkdf_expand(prk, info, size):
    okm, block, counter = b"", b"", 1
    while len(okm) < size:
        block = hmac_sha256(prk, block + info + bytes((counter,)))
        okm += block
        counter += 1
    return okm[:size]


def expand_label(secret, label, context, size):
    text = ("tls13 " + label).encode()
    hlabel = struct.pack(">HB", size, len(text)) + text + struct.pack(">B", len(context))
    return hkdf_expand(secret, hlabel + context, size)


def varint(value):
    if value < 0x40:
        return bytes((value,))
    if value < 0x4000:
        return struct.pack(">H", value + 0x4000)
    if value < 0x40000000:
        return struct.pack(">I", value + 0x80000000)
    return struct.pack(">Q", value + 0xC0000000)


def u8(v):
    return bytes((v,))


def u16(v):
    return struct.pack(">H", v)


def u24(v):
    return struct.pack(">I", v)[1:]


def vec_u8(payload):
    assert len(payload) < 256
    return u8(len(payload)) + payload


# (kind, payload) in the fixed extension order used by every offset below.
# Vector widths follow the codec: supported_versions uses a uint8 list,
# groups/signatures/key_share/ALPN use uint16 list lengths.
_EXT_SHARE = b"\x00\x1d" + u16(32) + bytes(range(0x10, 0x30))
_EXT_SIGS = bytes((0x04, 0x03, 0x08, 0x04, 0x08, 0x07))
ALPN = u16(7) + b"\x06libp2p"
EXTENSIONS = [
    (43, vec_u8(b"\x03\x04")),
    (10, u16(4) + b"\x00\x1d\x00\x17"),
    (51, u16(len(_EXT_SHARE)) + _EXT_SHARE),
    (13, u16(len(_EXT_SIGS)) + _EXT_SIGS),
    (16, ALPN),
    (57, b"\x01\x75\x30"),
]


def build_client_hello():
    payload = b"".join(u16(kind) + u16(len(data)) + data for kind, data in EXTENSIONS)
    body = (b"\x03\x03" + b"\x42" * 32 + b"\x00"
            + u16(2) + b"\x13\x01" + vec_u8(b"\x00") + u16(len(payload)) + payload)
    return u8(1) + u24(len(body)) + body


def tls_words(ch):
    """ClientHello view words relative to the CRYPTO data (= ch itself)."""
    extensions_offset = 47
    w = [0] * 64
    w[0], w[1], w[2], w[3] = 1, len(ch), 0, 8
    w[4], w[5] = 0x0303, 0x1301
    w[12], w[13] = 6, 32
    w[14], w[15] = 39, 0              # session id payload present, empty
    w[16], w[17] = 41, 2              # offered suites payload
    w[18], w[19] = 44, 1              # compression payload
    w[20], w[21] = extensions_offset, len(ch) - extensions_offset
    ext = extensions_offset
    for kind, data in EXTENSIONS:
        payload_at = ext + 4
        if kind == 43:
            w[22], w[23] = payload_at + 1, len(data) - 1
        elif kind == 10:
            w[24], w[25] = payload_at + 2, len(data) - 2
        elif kind == 51:
            w[26], w[27] = payload_at, len(data)
            w[56], w[57] = payload_at + 6, 32   # x25519 share bytes
        elif kind == 13:
            w[28], w[29] = payload_at + 2, len(data) - 2
        elif kind == 16:
            w[32], w[33] = payload_at, len(data)
        elif kind == 57:
            w[34], w[35] = payload_at, len(data)
        ext = payload_at + len(data)
    assert ext == len(ch), (ext, len(ch))
    w[11] = 1                            # share count
    w[60], w[61], w[62], w[63] = 11, 3, 1, 1  # 0304 offered via supported_versions
    return w


def aes_ecb(key, block):
    return Cipher(algorithms.AES(key), modes.ECB()).encryptor().update(block)


def key_material(secret):
    return (expand_label(secret, "quic key", b"", 16)
            + expand_label(secret, "quic iv", b"", 12)
            + expand_label(secret, "quic hp", b"", 16))


def derivations(dcid):
    initial = hkdf_extract(SALT, dcid)
    client_in = expand_label(initial, "client in", b"", 32)
    server_in = expand_label(initial, "server in", b"", 32)
    return initial, client_in, server_in, key_material(client_in), key_material(server_in)


def protect(dcid, ch, pn=2):
    """Return (masked packet, pn offset, unmasked flat packet)."""
    _, _, _, client_keys, _ = derivations(dcid)
    key, iv, hp = client_keys[:16], client_keys[16:28], client_keys[28:44]

    payload = b"\x06" + varint(0) + varint(len(ch)) + ch
    length = len(payload) + 4 + 16
    length_field = varint(length)
    pn_offset = 1 + 4 + 1 + len(dcid) + 1 + 1 + len(length_field)
    header = (b"\xc3" + b"\x00\x00\x00\x01" + u8(len(dcid)) + dcid
              + u8(0) + varint(0) + length_field + pn.to_bytes(4, "big"))
    assert len(header) == pn_offset + 4, (len(header), pn_offset)

    nonce = bytes(a ^ b for a, b in zip(iv, pn.to_bytes(12, "big")))
    ciphertext = AESGCM(key).encrypt(nonce, payload, header)
    flat = header + ciphertext
    mask = aes_ecb(hp, flat[pn_offset + 4:pn_offset + 20])
    masked = bytearray(flat)
    masked[0] ^= mask[0] & 0x0F
    for i in range(4):
        masked[pn_offset + i] ^= mask[1 + i]
    return bytes(masked), pn_offset, bytes(flat)


def le64(n):
    return struct.pack("<Q", n)


def le64_words(words):
    return b"".join(le64(v) for v in words)


def unprotect_expected(flat, pn_offset, ch):
    """LE64 PN || LE64 header length || unmasked header || frames payload."""
    header_length = pn_offset + 4
    frame = b"\x06" + varint(0) + varint(len(ch)) + ch
    body = le64(2) + le64(header_length) + flat[:header_length] + frame
    assert len(body) == len(flat)
    return bytes(body)


def packet_desc(protected, pn_offset):
    w = [0] * 16
    w[0], w[1] = len(protected), 1  # long packets consume their bounded portion
    w[2] = protected[0]          # the raw (masked) first byte, unauthenticated
    w[3] = int.from_bytes(protected[1:5], "big")
    n = protected[5]             # destination CID length
    assert 8 + n + 2 == pn_offset  # scid len + token len + length varint
    w[4], w[5] = 6, n
    w[6], w[7] = 7 + n, 0        # source CID present, empty
    w[8], w[9] = 8 + n, 0        # token present, empty
    w[10], w[11] = pn_offset, len(protected) - pn_offset
    return le64_words(w)


def frame_desc(payload_len, data_length):
    w = [0] * 16
    w[0], w[1] = payload_len, 6
    w[2] = 0
    w[3] = payload_len - data_length
    w[4] = data_length
    return le64_words(w)


def main():
    dcid = bytes.fromhex("a16277350c89412d")

    # RFC 9001 crosscheck of the expanded label against cryptography HKDF.
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives import hashes
    initial, client_in, _, _, _ = derivations(dcid)
    assert hkdf_extract(SALT, dcid) == initial
    text = b"tls13 client in"
    info = struct.pack(">HB", 32, len(text)) + text + b"\x00"
    assert HKDF(algorithm=hashes.SHA256(), length=32, salt=SALT, info=info).derive(dcid) \
        == client_in, "HKDF label mismatch"

    ch = build_client_hello()
    protected, pn_offset, flat = protect(dcid, ch)
    kdf_out = b"".join(derivations(dcid))
    header_length = pn_offset + 4
    frame_len = len(protected) - header_length - 16
    unp_out = unprotect_expected(flat, pn_offset, ch)
    pd = packet_desc(protected, pn_offset)
    crypto_data_offset = 4  # type varint(1) + offset varint(1) + length varint(2)
    assert frame_len - len(ch) == crypto_data_offset
    fd = frame_desc(frame_len, len(ch))
    tw = tls_words(ch)

    region = bytearray(b"\xA5" * REGION_SIZE)

    def put(offset, data):
        region[offset:offset + len(data)] = data

    put(OFF["dcid"], dcid)
    put(OFF["packet"], protected)
    put(OFF["kdfDesc"], le64_words([
        BASE + OFF["dcid"], len(dcid), BASE + OFF["kdfOut"], 184,
        BASE + OFF["kdfWork"], 1280, BASE + OFF["shaTable"]]))
    put(OFF["unpDesc"], le64_words([
        BASE + OFF["kdfOut"] + 96, BASE + OFF["packet"], len(protected),
        pn_offset, 0, BASE + OFF["unpOut"], len(protected),
        BASE + OFF["unpWork"], 1616 + len(protected), 2**36 - 32, 0]))
    put(OFF["tlsDesc"], le64_words([
        BASE + OFF["unpOut"] + 16 + header_length + crypto_data_offset, len(ch),
        BASE + OFF["tlsOut"], 512,
        BASE + OFF["tlsWork"], 16896, 65536, 1]))
    put(OFF["shaTable"], le64_words(SHA_TABLE))

    def stage(name, args, aux, outputs, stack_count):
        return {"name": name, "args": args, "status": 0, "aux": aux,
                "outputs": [{"addr": a, "bytes": list(b)} for a, b in outputs],
                "stackClear": [SP0 - stack_count, stack_count]}

    # packetParse runs on the original datagram: header protection masks only
    # authenticated bits the parser never inspects, and the unprotect output
    # publishes its first 16 bytes as PN/headerLength metadata.
    stages = [
        stage("kdf", [BASE + OFF["kdfDesc"]], [],
              [(BASE + OFF["kdfOut"], kdf_out)], 528),
        stage("packet",
              [BASE + OFF["packet"], len(protected), BASE + OFF["packetDesc"], 128,
               BASE + OFF["packetWork"], 256, 8, 0],
              [[11, 0], [12, len(protected)]],
              [(BASE + OFF["packetDesc"], pd)], 256),
        stage("open", [BASE + OFF["unpDesc"]], [],
              [(BASE + OFF["unpOut"], unp_out)], 240),
        stage("frame",
              [BASE + OFF["unpOut"] + 16 + header_length, frame_len,
               BASE + OFF["frameDesc"], 128, BASE + OFF["frameWork"], 256, 0, 16],
              [[11, 0], [12, frame_len]],
              [(BASE + OFF["frameDesc"], fd)], 256),
        stage("tls", [BASE + OFF["tlsDesc"]], [],
              [(BASE + OFF["tlsOut"], le64_words(tw))], 240),
    ]

    final = bytearray(region)

    def zero(offset, count):
        final[offset:offset + count] = bytes(count)

    for offset, data, size in [
        (OFF["kdfOut"], kdf_out, len(kdf_out)),
        (OFF["unpOut"], unp_out, len(unp_out)),
        (OFF["packetDesc"], pd, len(pd)), (OFF["frameDesc"], fd, len(fd)),
        (OFF["tlsOut"], le64_words(tw), 512)]:
        final[offset:offset + len(data)] = data
    zero(OFF["kdfWork"], 1280)
    zero(OFF["unpWork"], 1616 + len(protected))
    zero(OFF["packetWork"], 128)
    zero(OFF["frameWork"], 128)
    zero(OFF["tlsWork"], 16896)
    stack = bytearray(b"\xA5" * STACK_SIZE)
    stack[STACK_SIZE - 528:] = bytes(528)

    case = {
        "base": BASE, "stackBase": STACK_BASE, "stackSize": STACK_SIZE, "sp0": SP0,
        "regionSize": REGION_SIZE,
        "initialRegs": [0] + [0x80000 if i == 1 else SP0 if i == 2 else
                              0x33000 if i == 3 else 0x44000 if i == 4 else
                              0x7000000000000 + i * 0x11101 for i in range(1, 32)],
        "region": list(region), "stack": list(stack),
        "stages": stages,
        "expectRegion": list(final), "expectStack": list(stack),
        "dcid": list(dcid), "clientHello": list(ch),
    }
    out = Path(__file__).resolve().parent / "case.json"
    out.write_text(json.dumps(case))
    print(f"case written: region {len(region)} B, packet {len(protected)} B, "
          f"clientHello {len(ch)} B, {len(stages)} stages")
    return case


def build_case():
    """Public entry for Tests/Pipeline/check.py."""
    return main()


if __name__ == "__main__":
    build_case()
