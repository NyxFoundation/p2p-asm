"""RFC4055/5480/5758/8410 AlgorithmIdentifier grammar, independent of Lean."""
from dataclasses import dataclass
import random
import struct

MAX, INPUT = 2**64-1, 0x100008
CALLER = (5, 6, 7, *range(10, 18), *range(28, 32))


def tlv(tag, data):
    assert len(data) < 128
    return bytes((tag, len(data)))+data


def base128(n):
    digits = [n & 127]
    while n >= 128:
        n >>= 7
        digits.insert(0, 128 | (n & 127))
    return bytes(digits)


def oid(text):
    arcs = list(map(int, text.split(".")))
    return tlv(6, b"".join(base128(n) for n in [40*arcs[0]+arcs[1], *arcs[2:]]))


def algorithm(name, params=b""):
    return tlv(48, oid(name)+params)


def known(kind):
    ed = algorithm("1.3.101.112")
    rsa = "1.2.840.113549.1.1."
    if kind == "public":
        return {ed: 1, algorithm("1.2.840.10045.2.1", oid("1.2.840.10045.3.1.7")): 2,
                algorithm(rsa+"1"): 3, algorithm(rsa+"1", b"\x05\0"): 3}
    result = {ed: 1, algorithm("1.2.840.10045.4.3.2"): 2,
              algorithm(rsa+"11"): 3, algorithm(rsa+"11", b"\x05\0"): 3}
    for hash_null in (b"", b"\x05\0"):
        for mask_null in (b"", b"\x05\0"):
            for trailer in (b"", b"\xa3\x03\x02\x01\x01"):
                sha = "2.16.840.1.101.3.4.2.1"
                params = (tlv(160, algorithm(sha, hash_null))+
                          tlv(161, algorithm(rsa+"8", algorithm(sha, mask_null)))+
                          b"\xa2\x03\x02\x01\x20"+trailer)
                result[algorithm(rsa+"10", tlv(48, params))] = 4
    return result


@dataclass(frozen=True)
class Case:
    name: str
    data: bytes
    alignment: int = 0
    pointer: int | None = None


def cases(kind):
    patterns = list(known(kind))
    result = [Case(f"known-{i}", b) for i, b in enumerate(patterns)]
    for j, raw in enumerate(patterns):
        result += [Case(f"prefix-{j}-{i}", raw[:i]) for i in range(len(raw))]
        result += [Case(f"mutate-{j}-{i}", raw[:i]+bytes((raw[i] ^ 1,))+raw[i+1:])
                   for i in range(len(raw))]
    result += [Case(f"suffix-{j}", raw+b"\x05\0") for j, raw in enumerate(patterns)]
    rng = random.Random(4055)
    result += [Case(f"random-{i}", rng.randbytes(rng.randrange(0, 96))) for i in range(50)]
    result += [Case("unaligned", patterns[0], alignment=1),
               Case("wrapping", patterns[0], pointer=MAX),
               Case("unused-unmapped", b"x", pointer=MAX)]
    return result


def write_case(path, kind, case):
    regs = [0]+[0x7251000000000000+i*0x11101 for i in range(1, 32)]
    regs[1:4] = [0x80000, 0x6001a0, 0x700000]
    ptr = case.pointer if case.pointer is not None else INPUT+case.alignment
    regs[10:12] = [ptr, len(case.data)]
    regions = [b"\xa5"*(8+case.alignment)+case.data+b"\x5a"*8,
               b"\x61"*32, b"\xa7"*64, b"\x82"*32, b"\x9c"*32, b"\xc4"*432]
    before = struct.pack("<32Q", *regs)+b"".join(regions)
    value = known(kind).get(case.data, 0)
    status = 4 if ptr+len(case.data) > 2**64 else 0 if value else 8
    after_regs = [0 if i in CALLER else r for i, r in enumerate(regs)]
    after_regs[10:12] = [status, value if status == 0 else 0]
    after = struct.pack("<32Q", *after_regs)+b"".join(regions)
    path.mkdir(parents=True, exist_ok=True)
    for name, data in (("before.bin", before), ("expected.bin", after),
                       ("sizes.bin", struct.pack("<6Q", *map(len, regions))),
                       ("a.bin", case.data), ("b.bin", b""),
                       ("meta.bin", struct.pack("<2Q", *after_regs[10:12]))):
        (path/name).write_bytes(data)
