"""Independent wire/arithmetic fixtures for public data, never production keys."""
from dataclasses import dataclass, replace
import random
import struct

MAX = 2**64-1
INPUT, OUTPUT, WORK, SP = 0x100008, 0x300008, 0x400008, 0x6001a0
CALLER = (5, 6, 7, *range(10, 18), *range(28, 32))
ED = bytes.fromhex("1ed1e8fae2c4a144b8be8fd4b47bf3d3b34b871c3cacf6010f0e42d474fce27e")
SECP = bytes.fromhex("037777e994e452c21604f91de093ce415f5432f701dd8cd1a7a6fea0e630bfca99")


class ParseError(Exception):
    def __init__(self, code):
        self.code = code


def uvar(data, pos):
    result = 0
    for i in range(10):
        if pos+i >= len(data):
            raise ParseError(1)
        byte = data[pos+i]
        if i == 9 and byte > 1:
            raise ParseError(2)
        result |= (byte & 127) << (7*i)
        if byte < 128:
            return result, pos+i+1
    raise ParseError(2)


def parse(data):
    pos, groups, kind, view = 0, [], None, None
    while pos < len(data):
        tag, pos = uvar(data, pos)
        field, wire = tag >> 3, tag & 7
        if not 0 < field < 2**29:
            raise ParseError(6)
        if wire == 0:
            n, pos = uvar(data, pos)
            if not groups and field == 1:
                kind = n
        elif wire in (1, 5):
            pos += 8 if wire == 1 else 4
        elif wire == 2:
            size, pos = uvar(data, pos)
            if not groups and field == 2:
                view = pos, size
            pos += size
        elif wire == 3:
            groups.append(field)
        elif wire == 4:
            if not groups or groups.pop() != field:
                raise ParseError(6)
        else:
            raise ParseError(6)
        if pos > len(data):
            raise ParseError(1)
    if groups:
        raise ParseError(1)
    if kind is None or view is None:
        raise ParseError(7)
    if kind not in (1, 2):
        raise ParseError(8)
    if view[1] != kind+31:
        raise ParseError(9)
    return kind, *view


def canonical(kind, key):
    return bytes((8, kind, 18, len(key))) + key


def peer_id(kind, key):
    data = canonical(kind, key)
    return bytes((0, len(data))) + data


def varint(n):
    result = bytearray()
    while n >= 128:
        result.append((n & 127) | 128)
        n >>= 7
    return bytes(result + bytes((n,)))


@dataclass(frozen=True)
class Case:
    name: str
    data: bytes = b""
    kind: int = 1
    available: int | None = None
    input: int = INPUT
    output: int = OUTPUT
    capacity: int = 48
    work: int = WORK
    work_capacity: int | None = None
    stack: int = SP


def parse_cases():
    valid = canonical(1, ED)
    inputs = [valid, canonical(2, SECP), bytes((18, 32))+ED+bytes((8, 1)),
              bytes((8, 2))+valid, bytes((18, 0))+valid,
              valid+bytes((10, 0)), valid+bytes((16, 99)),
              bytes((0x1b, 8, 2, 18, 0, 0x1c))+valid,
              bytes((0x88, 0, 0x81, 0, 18, 0xa0, 0))+ED,
              bytes((25,))+b"fixed008"+bytes((37,))+b"four"+valid,
              bytes((0x1a, 3, 1, 2, 3))+valid,
              varint((2**29-1)*8)+b"\0"+valid]
    inputs += [bytes((0x1b,))*n+bytes((0x1c,))*n+valid for n in (1, 2, 16, 256)]
    cases = [Case(f"valid-{i}", b) for i, b in enumerate(inputs)]
    cases += [Case(f"prefix-{i}", valid[:i]) for i in range(len(valid))]
    invalid = [b"\0", b"\x1e", b"\x1f", b"\x1c", b"\x1b\x24",
               b"\x1b"+valid, b"\x08\x03\x12\x20"+ED,
               b"\x08\x01\x12\x1f"+ED[:31], b"\x12\x20"+ED,
               b"\x08\x01\x12"+varint(MAX), varint(2**32)+b"\0",
               b"\x08"+b"\xff"*10, b"\x08"+varint(MAX)+b"\x12\x20"+ED,
               valid+b"\x08\x03", valid+b"\x12\0", b"\x0a\0"+bytes((18, 32))+ED]
    cases += [Case(f"invalid-{i}", b) for i, b in enumerate(invalid)]
    rng = random.Random(0x53594)
    cases += [Case(f"random-{i}", rng.randbytes(rng.randrange(1, 65))) for i in range(50)]
    base = Case("base", valid)
    return cases + [replace(base, name="short-work", work_capacity=8*len(valid)-1),
                    replace(base, name="unaligned-work", work=WORK+1),
                    replace(base, name="input-wrap", input=MAX),
                    replace(base, name="work-wrap", work=MAX-7),
                    replace(base, name="input-work-overlap", work=INPUT),
                    replace(base, name="input-stack-overlap", input=SP-16),
                    replace(base, name="work-stack-overlap", work=SP-16),
                    replace(base, name="stack-short", stack=16),
                    replace(base, name="stack-unaligned", stack=SP+1),
                    Case("work-overflow", available=2**61),
                    Case("empty-unmapped", input=MAX, work=MAX, stack=MAX)]


def varint_cases():
    inputs = [varint(n) for n in (0, 1, 127, 128, 2**32-1, 2**63-1, 2**63, MAX)]
    inputs += [b"\x80"*i+b"\0" for i in range(10)]
    inputs += [b"\xff"*i for i in range(11)]
    inputs += [b"\xff"*9+b for b in (b"\x01", b"\x02", b"\x80", b"\xff")]
    return [Case(f"varint-{i}", b) for i, b in enumerate(inputs)] + [
        Case("range", input=MAX, available=2), Case("empty", input=MAX)]


def id_cases():
    result = [Case(f"key-{kind}-cap-{cap}", key, kind=kind, capacity=cap)
              for kind, key in ((1, ED), (2, SECP))
              for cap in (0, 1, 32, 37, 38, 39, 40, 48)]
    return result + [Case("wrong-type", ED, kind=3), Case("huge-type", ED, kind=MAX),
                     Case("wrong-length", ED[:-1]), Case("long-length", ED+b"\0"),
                     Case("input-wrap", ED, input=MAX), Case("output-wrap", ED, output=MAX),
                     Case("overlap", ED, output=INPUT)]


def span(ptr, size):
    return size == 0 or ptr+size <= 2**64


def overlap(a, n, b, m):
    return n != 0 and m != 0 and a < b+m and b < a+n


def expected(kind, c):
    size = len(c.data) if c.available is None else c.available
    work = size*8
    cap = work+16 if c.work_capacity is None else c.work_capacity
    if kind == "publickey":
        early = (2 if size >= 2**61 else 7 if size == 0 else 5 if cap < work else
                 4 if not span(c.input, size) or not span(c.work, work) or c.work % 8
                 or c.stack < 112 or c.stack % 16
                 or overlap(c.input, size, c.work, work)
                 or overlap(c.input, size, c.stack-112, 112)
                 or overlap(c.work, work, c.stack-112, 112) else 0)
        if early:
            return early, (), b"", 0, 0
        try:
            return 0, parse(c.data), b"", work, 112
        except ParseError as e:
            return e.code, (), b"", work, 112
    if kind == "varint":
        if not span(c.input, size):
            return 4, (), b"", 0, 0
        try:
            return 0, uvar(c.data, 0), b"", 0, 0
        except ParseError as e:
            return e.code, (), b"", 0, 0
    early = (8 if c.kind not in (1, 2) else 9 if size != c.kind+31 else
             5 if c.capacity < size+6 else 4 if not span(c.input, size)
             or not span(c.output, size+6) or overlap(c.input, size, c.output, size+6) else 0)
    if early:
        return early, (), b"", 0, 0
    result = peer_id(c.kind, c.data)
    return 0, (len(result),), result, 0, 0


def write_case(path, kind, c):
    size = len(c.data) if c.available is None else c.available
    work_size = 8*len(c.data)
    cap = work_size+16 if c.work_capacity is None else c.work_capacity
    regs = [0]+[0x7251000000000000+i*0x11101 for i in range(1, 32)]
    regs[1:4] = [0x80000, c.stack, 0x700000]
    if kind == "publickey":
        regs[10:14] = [c.input, size, c.work, cap]
    elif kind == "varint":
        regs[10:12] = [c.input, size]
    else:
        regs[10:15] = [c.kind, c.input, size, c.output, c.capacity]
    regions = [b"\xa5"*8+c.data+b"\x5a"*8, b"\x61"*32, b"\xa7"*64,
               b"\x82"*(work_size+32), b"\x9c"*32, b"\xc4"*432]
    before = struct.pack("<32Q", *regs)+b"".join(regions)
    status, fields, output, wiped, depth = expected(kind, c)
    after_regs = [0 if i in CALLER else r for i, r in enumerate(regs)]
    after_regs[10], after_regs[11:11+len(fields)] = status, fields
    after_regions = regions[:]
    if output:
        after_regions[2] = regions[2][:8]+output+regions[2][8+len(output):]
    if wiped:
        after_regions[3] = regions[3][:8]+bytes(wiped)+regions[3][8+wiped:]
    if depth:
        after_regions[5] = regions[5][:416-depth]+bytes(depth)+regions[5][416:]
    after = struct.pack("<32Q", *after_regs)+b"".join(after_regions)
    path.mkdir(parents=True, exist_ok=True)
    for name, data in (("before.bin", before), ("expected.bin", after),
                       ("sizes.bin", struct.pack("<6Q", *map(len, regions))),
                       ("a.bin", c.data), ("b.bin", b""),
                       ("meta.bin", struct.pack("<3Q", status, wiped, depth))):
        (path/name).write_bytes(data)
