"""Independent arithmetic fixtures; all byte strings and seeds are test-only."""
from dataclasses import dataclass
import random
import struct

MAX = 2**64 - 1
INPUT, OUTPUT = 0x100009, 0x300009
CALLER = (5, 6, 7, *range(10, 18), *range(28, 32))


def supported(tag):
    return tag < 256 and tag & 31 != 31 and tag not in (0, 32)


def header(tag, length):
    if length < 128:
        return bytes((tag, length))
    value = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes((tag, 128 + len(value))) + value


def decode(data):
    if not data:
        return 1, ()
    if not supported(data[0]):
        return 6, ()
    if len(data) < 2:
        return 1, ()
    first = data[1]
    if first == 128:
        return 7, ()
    if first == 255:
        return 8, ()
    count = first & 127 if first >= 128 else 0
    if count > 8:
        return 2, ()
    if len(data) < 2 + count:
        return 1, ()
    if count and data[2] == 0:
        return 3, ()
    length = int.from_bytes(data[2:2+count], "big") if count else first
    if count and length < 128:
        return 3, ()
    total = 2 + count + length
    if total > len(data):
        return 1, ()
    return 0, (data[0], 2 + count, length, total)


@dataclass(frozen=True)
class Case:
    name: str
    data: bytes = b""
    tag: int = 4
    length: int = 0
    capacity: int = 16
    pointer: int | None = None
    available: int | None = None


def decode_cases():
    result = [Case(f"tag-{t}", bytes((t, 0))) for t in range(256)]
    for n in (0, 1, 2, 126, 127, 128, 129, 255, 256, 257, 1024):
        data = header(0x30, n) + bytes((85,)) * n
        result.append(Case(f"length-{n}", data + b"trailing"))
        result.extend(Case(f"prefix-{n}-{i}", data[:i]) for i in range(len(header(0x30, n))))
        if n:
            result.append(Case(f"content-short-{n}", data[:-1]))
    malformed = (b"", b"\x04", b"\x04\x80", b"\x04\xff", b"\x04\x89",
                 b"\x04\x81\x7f", b"\x04\x82\x00\x80",
                 b"\x04\x88" + b"\xff"*8, b"\x04\x88\x80" + b"\x00"*7)
    result.extend(Case(f"malformed-{i}", d) for i, d in enumerate(malformed))
    rng = random.Random(0x690)
    result.extend(Case(f"random-{i}", rng.randbytes(rng.randrange(1, 21))) for i in range(80))
    return result + [Case("empty-invalid-pointer", pointer=MAX),
                     Case("wrap", pointer=MAX, available=2),
                     Case("wrap-large", pointer=INPUT, available=MAX)]


def encode_cases():
    lengths = (0, 1, 127, 128, 255, 256, 65535, 65536,
               2**32-1, 2**32, 2**56-1, 2**56, MAX)
    result = [Case(f"length-{n}-cap-{cap}", length=n, capacity=cap)
              for n in lengths for cap in (0, 1, 2, 3, 4, 7, 8, 9, 10, 16)]
    result += [Case(f"tag-{t}", tag=t) for t in (0, 32, 31, 63, 128, 160, 163, 254, 255, 256, MAX)]
    return result + [Case("wrap-short", pointer=MAX),
                     Case("wrap-long", pointer=MAX-8, length=MAX),
                     Case("tag-first", tag=256, capacity=0, pointer=MAX)]


def expectation(kind, c):
    if kind == "decode":
        ptr = INPUT if c.pointer is None else c.pointer
        size = len(c.data) if c.available is None else c.available
        if size and ptr + size > 2**64:
            return 4, (), b"", 0
        status, fields = decode(c.data)
        count = (c.data[1] & 127) if len(c.data) > 1 and 128 < c.data[1] < 137 else 0
        return status, fields, b"", min(len(c.data), 2 + count)
    if not supported(c.tag):
        return 6, (), b"", 0
    value = header(c.tag, c.length)
    ptr = OUTPUT if c.pointer is None else c.pointer
    if c.capacity < len(value):
        return 5, (), b"", 0
    if ptr + len(value) > 2**64:
        return 4, (), b"", 0
    return 0, (len(value),), value, len(value)


def fixture(kind, c):
    regs = [0] + [0xabcdef0000000000+i*0x11001 for i in range(1, 32)]
    regs[1], regs[2], regs[3] = 0x80000, 0x600020, 0x700000
    if kind == "decode":
        regs[10:12] = [INPUT if c.pointer is None else c.pointer,
                       len(c.data) if c.available is None else c.available]
    else:
        regs[10:14] = [c.tag, c.length, OUTPUT if c.pointer is None else c.pointer, c.capacity]
    regions = [bytes((0xa5,))*9+c.data+bytes((0x5a,))*9,
               bytes((0x61,))*32, bytes((0xa7,))*40, bytes((0x82,))*32,
               bytes((0x9c,))*32, bytes((0xc4,))*64]
    before = struct.pack("<32Q", *regs) + b"".join(regions)
    status, fields, output, access = expectation(kind, c)
    after_regs = [0 if i in CALLER else r for i, r in enumerate(regs)]
    after_regs[10] = status
    after_regs[11:11+len(fields)] = fields
    after_regions = regions[:]
    if output:
        after_regions[2] = regions[2][:9]+output+regions[2][9+len(output):]
    after = struct.pack("<32Q", *after_regs) + b"".join(after_regions)
    return before, after, struct.pack("<6Q", *map(len, regions)), status, access


def write_case(path, kind, c):
    path.mkdir(parents=True, exist_ok=True)
    before, after, sizes, status, access = fixture(kind, c)
    for name, data in (("before.bin", before), ("expected.bin", after), ("sizes.bin", sizes),
                       ("a.bin", c.data), ("b.bin", b""), ("meta.bin", struct.pack("<2Q", status, access))):
        (path/name).write_bytes(data)
