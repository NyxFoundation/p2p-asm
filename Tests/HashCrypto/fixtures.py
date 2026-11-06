"""Public vectors and Python hashlib/hmac oracles; no implementation is imported."""

from dataclasses import dataclass, replace
import hashlib
import hmac
import random
import re
import struct

from build import ROOT


@dataclass(frozen=True)
class Case:
    name: str
    a: bytes = b""
    b: bytes = b""
    length: int = 0
    status: int = 0
    declared_a: int | None = None
    declared_b: int | None = None
    capacity: int | None = None
    trace: bool = False
    bad_pointer: bool = False
    bad_alignment: bool = False
    bad_range: str = ""
    published: bytes = b""


def mac(key, data):
    return hmac.digest(key, data, "sha256")


def oracle(kind, case):
    if kind == "length512":
        return (case.length*8).to_bytes(16, "big")
    if kind in ("sha256", "sha512"):
        return hashlib.new(kind, case.a).digest()
    if kind in ("hmac", "extract"):
        return mac(case.a, case.b)
    if kind == "tls":
        label = b"tls13 " + case.a
        return (case.length.to_bytes(2, "big") + bytes([len(label)]) + label
                + bytes([len(case.b)]) + case.b)
    previous, output = b"", b""
    for counter in range(1, (case.length + 31) // 32 + 1):
        previous = mac(case.a, previous + case.b + bytes([counter]))
        output += previous
    return output[:case.length]


def required(kind, case):
    if kind == "length512":
        return 0
    if kind == "sha256":
        return 704
    if kind == "sha512":
        return 960
    if kind in ("hmac", "extract"):
        return max(896, 864 + len(case.b))
    if kind == "tls" or case.length == 0:
        return 0
    message = len(case.b) + 1 + (32 if case.length > 32 else 0)
    return ((32 + message + 7) & ~7) + max(896, 864 + message)


def tables(kind):
    name = "SHA512" if kind == "sha512" else "SHA256"
    text = (ROOT / f"Libp2pAsm/Spec/Crypto/{name}.lean").read_text()
    table = text.split("def roundConstants", 1)[1].split("#v[", 1)[1].split("]", 1)[0]
    return b"".join(struct.pack("<Q", int(x, 16)) for x in re.findall(r"0x[0-9a-f]+", table))


def sha_cases(kind, rng):
    # Read the existing published CAVP data, not the spec implementation.
    source = (ROOT / f"Tests/Crypto/{kind.upper()}Vectors.lean").read_text()
    records = re.findall(r'⟨"([^"]+)", (\d+),\s*(.*?)⟩', source, re.S)
    result = []
    for name, size, content in records:
        strings = re.findall(r'"([0-9a-f]*)"', content)
        joined = bytes.fromhex("".join(strings))
        width = 32 if kind == "sha256" else 64
        message, digest = joined[:-width], joined[-width:]
        assert len(message) == int(size)
        result.append(Case(name, message, published=digest))
    for size in [0, 1, 3, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129, 255, 256, 257, 4097]:
        result.append(Case(f"boundary-{size}", rng.randbytes(size), trace=size in (0, 56, 112, 128)))
    if kind == "sha256":
        result += [Case("bit-overflow", declared_a=1 << 61, status=1),
                   Case("bit-overflow-max", declared_a=(1 << 64)-1, status=1)]
    else:
        # Length is allowed; a nonwrapping backing range is a separate requirement.
        result += [Case("64-bit-length-range", b"a", declared_a=(1 << 64)-1, status=4)]
    return result


def hmac_cases(rng):
    published = [
        (b"\x0b"*20, b"Hi There", "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
        (b"Jefe", b"what do ya want for nothing?", "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
        (b"\xaa"*20, b"\xdd"*50, "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
        (bytes(range(1, 26)), b"\xcd"*50, "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"),
        (b"\x0c"*20, b"Test With Truncation", "a3b6167473100ee06e0c796c2955552b"),
        (b"\xaa"*131, b"Test Using Larger Than Block-Size Key - Hash Key First", "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
        (b"\xaa"*131, b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.", "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"),
    ]
    result = [Case(f"RFC4231-{i+1}", a, b, published=bytes.fromhex(d))
              for i, (a, b, d) in enumerate(published)]
    result.append(Case("NIST-block-key", bytes(range(64)), b"Sample message for keylen=blocklen",
                       published=bytes.fromhex("8bb9a1db9806f20df7f77b82138c7914d174d59e13dc4d0169c9057b133e1d62")))
    result += [Case(f"key-{k}-message-{m}", rng.randbytes(k), rng.randbytes(m),
                    trace=(k, m) in ((0, 0), (64, 64), (131, 112)))
               for k, m in [(0, 0), (0, 1), (1, 0), (63, 55), (64, 56), (64, 64),
                            (65, 63), (131, 112), (4097, 257), (32, 4097)]]
    result += [Case("key-overflow", declared_a=1 << 61, status=1),
               Case("message-overflow", declared_b=(1 << 61)-64, status=1)]
    return result


def rfc5869():
    return [
        (b"\x0b"*22, bytes(range(13)), bytes(range(0xf0, 0xfa)), 42,
         "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
         "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"),
        (bytes(range(80)), bytes(range(0x60, 0xb0)), bytes(range(0xb0, 0x100)), 82,
         "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244",
         "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87"),
        (b"\x0b"*22, b"", b"", 42,
         "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
         "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"),
    ]


def kdf_cases(kind, rng):
    if kind == "extract":
        result = [Case(f"RFC5869-A.{i+1}", salt, ikm, published=bytes.fromhex(prk))
                  for i, (ikm, salt, _, _, prk, _) in enumerate(rfc5869())]
        result += [Case("default-zero-salt", bytes(32), b"\x0b"*22, trace=True),
                   Case("empty-ikm-salt", trace=True),
                   Case("long-salt", rng.randbytes(4097), rng.randbytes(129))]
        return result
    result = [Case(f"RFC5869-A.{i+1}", bytes.fromhex(prk), info, n, published=bytes.fromhex(okm))
              for i, (_, _, info, n, prk, okm) in enumerate(rfc5869())]
    key = bytes.fromhex(rfc5869()[0][4])
    result += [Case(f"output-{n}", key, b"info", n, trace=n in (0, 33, 65))
               for n in (0, 1, 31, 32, 33, 64, 65, 8160)]
    result += [Case(f"PRK-{n}", rng.randbytes(n), rng.randbytes(17), 65, trace=n == 65)
               for n in (33, 64, 65, 131, 4097)]
    result += [Case("long-info", key, rng.randbytes(4097), 65),
               Case("short-PRK", bytes(31), length=1, status=3),
               Case("short-PRK-zero-output", length=0, status=3),
               Case("long-output", key, length=8161, status=2),
               Case("max-output-field", key, length=(1 << 64)-1, status=2),
               Case("key-overflow", key, length=1, declared_a=1 << 61, status=1),
               Case("info-overflow-first", key, length=32, declared_b=(1 << 61)-65, status=1),
               Case("info-overflow-next", key, length=33, declared_b=(1 << 61)-97, status=1),
               Case("zero-output-no-access", key, length=0, declared_a=(1 << 64)-1,
                    declared_b=(1 << 64)-1, capacity=0)]
    return result


def tls_cases(rng):
    return [Case("derived", b"derived", bytes(32), 32, trace=True),
            Case("minimum-label-empty-context", b"x", length=0, trace=True),
            Case("empty-label", length=0, status=8),
            Case("empty-label-nonempty-context", b"", b"context", 32, status=8),
            Case("empty-label-before-capacity-access", capacity=0, bad_pointer=True, status=8),
            Case("uint16-max", b"x", b"y", 65535),
            Case("maximum-fields", rng.randbytes(249), rng.randbytes(255), 8161, trace=True),
            Case("uint16-overflow", length=65536, status=2),
            Case("label-overflow", b"x"*250, status=6),
            Case("context-overflow", b"y", b"z"*256, status=7),
            Case("label-max-field", declared_a=(1 << 64)-1, status=6),
            Case("context-max-field", b"x", declared_b=(1 << 64)-1, status=7)]


def all_cases(kind):
    rng = random.Random(0x536861)
    if kind == "length512":
        return [Case(f"bit-length-{n}", length=n, trace=True)
                for n in (0, 1, (1 << 61)-1, 1 << 61, 1 << 63, (1 << 64)-1)]
    if kind.startswith("sha"):
        result = sha_cases(kind, rng)
    elif kind == "hmac":
        result = hmac_cases(rng)
    elif kind in ("extract", "expand"):
        result = kdf_cases(kind, rng)
    else:
        result = tls_cases(rng)
    sample = Case("capacity", b"a"*32, b"b"*32, 33)
    need = len(oracle(kind, sample)) if kind == "tls" else required(kind, sample)
    result += [replace(sample, name="exact-capacity", capacity=need, trace=True),
               replace(sample, name="insufficient-capacity", capacity=need-1, status=5),
               replace(sample, name="zero-capacity", capacity=0, status=5),
               replace(sample, name="pointer-wrap", bad_pointer=True, status=4)]
    result += [replace(sample, name="output-range", bad_range="output", status=4)]
    if kind in ("hmac", "extract", "expand", "tls"):
        result.append(replace(sample, name="second-input-range", bad_range="second", status=4))
    if kind != "tls":
        result += [replace(sample, name="workspace-range", bad_range="workspace", status=4),
                   replace(sample, name="constants-range", bad_range="constants", status=4)]
        result.append(replace(sample, name="workspace-alignment", bad_alignment=True, status=4))
    return [replace(c, trace=True) if c.status else c for c in result]
