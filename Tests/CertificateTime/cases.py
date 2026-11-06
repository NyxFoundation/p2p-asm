"""Independent datetime oracle for public ASN.1 time bytes."""
from dataclasses import dataclass, replace
import datetime as dt
import random
import re
import struct

MAX = 2**64-1
INPUT, OUTPUT = 0x100008, 0x300008
CALLER = (5, 6, 7, *range(10, 18), *range(28, 32))
EPOCH = dt.datetime(1970, 1, 1)


@dataclass(frozen=True)
class Case:
    name: str
    body: bytes = b""
    tag: int = 23
    seconds: int = 0
    before: int = 0
    after: int = 0
    available: int | None = None
    pointer: int | None = None
    capacity: int = 32
    alignment: int = 0
    stack: int = 0x6001a0


def utc_seconds(date):
    delta = date-EPOCH
    return delta.days*86400+delta.seconds


def body(date, width):
    year = f"{date.year % 100:02d}" if width == 2 else f"{date.year:04d}"
    return (year+f"{date.month:02d}{date.day:02d}{date.hour:02d}"
            f"{date.minute:02d}{date.second:02d}Z").encode("ascii")


def dates():
    years = (1, 4, 99, 100, 400, 1582, 1600, 1700, 1800, 1899, 1900, 1949,
             1950, 1969, 1970, 1999, 2000, 2004, 2049, 2050, 2100, 2400, 9999)
    result = [dt.datetime(y, m, d, 23, 59, 59) for y in years
              for m, d in ((1, 1), (2, 28), (3, 1), (12, 31))]
    result += [dt.datetime(y, 2, 29, 1, 2, 3) for y in (4, 400, 1600, 2000, 2004, 2400)]
    rng = random.Random(5280)
    result += [EPOCH+dt.timedelta(seconds=rng.randrange(-62135596800, 253402300800))
               for _ in range(80)]
    return [dt.datetime(1, 1, 1), EPOCH, *result]


def decode_cases():
    result = [Case(f"generalized-{i}", body(date, 4), 24) for i, date in enumerate(dates())]
    result += [Case(f"utc-{i}", body(date, 2)) for i, date in enumerate(dates())
               if 1950 <= date.year <= 2049]
    base = b"000229012345Z"
    result += [Case(f"prefix-{i}", base[:i]) for i in range(len(base))]
    result += [Case(f"mutate-{i}-{b}", base[:i]+bytes((b,))+base[i+1:])
               for i in range(len(base)) for b in (0, 47, 58, 255)]
    invalid = [b"000101000000z", b"000230000000Z", b"010229000000Z",
               b"001301000000Z", b"000001000000Z", b"000100000000Z",
               b"000101240000Z", b"000101006000Z", b"000101000060Z"]
    result += [Case(f"invalid-{i}", b) for i, b in enumerate(invalid)]
    result += [Case("year-zero", b"00000101000000Z", 24),
               Case("century", b"19000229000000Z", 24),
               Case("century2100", b"21000229000000Z", 24)]
    result += [Case(f"tag-{tag}", base, tag) for tag in (0, 22, 25, 255, MAX)]
    result += [Case("range-wrap", base, pointer=MAX),
               Case("huge-length", base, available=MAX, pointer=MAX),
               Case("unaligned", base, alignment=1),
               Case("arbitrary-stack", base, stack=MAX)]
    return result


def encode_cases():
    result = [Case(f"date-{i}", seconds=utc_seconds(date)) for i, date in enumerate(dates())]
    for year in (1, 1949, 1950, 2049, 2050, 9999):
        for capacity in (0, 1, 14, 15, 16, 17, MAX):
            result.append(Case(f"cap-{year}-{capacity}", seconds=utc_seconds(dt.datetime(year, 1, 1)),
                               capacity=capacity))
    result += [Case(f"out-of-range-{n}", seconds=n) for n in (
        -2**63, -62135596801, 253402300800, 2**63-1)]
    return result + [Case("wrap", pointer=MAX), Case("unaligned", alignment=1),
                     Case("arbitrary-stack", stack=MAX)]


def validity_cases():
    result = []
    boundaries = (-2**63, -62135596800, -9223372037, -9223372036, -1, 0, 1,
                  9223372036, 9223372037, 253402300799, 2**63-1)
    for before in boundaries:
        for after in boundaries:
            for now in (-2**63, -1, 0, 1, 2**63-1):
                result.append(Case(f"boundary-{before}-{after}-{now}", seconds=now,
                                   before=before, after=after))
    for sec in (-9223372036, -1, 0, 1, 9223372036):
        for delta in (-1, 0, 1):
            result.append(Case(f"fraction-{sec}-{delta}", seconds=sec*10**9+delta,
                               before=sec, after=sec))
    rng = random.Random(0x128)
    result += [Case(f"random-validity-{i}", seconds=rng.randrange(-2**63, 2**63),
                    before=rng.randrange(-2**63, 2**63), after=rng.randrange(-2**63, 2**63))
               for i in range(80)]
    return result


def decode(tag, data):
    width = 2 if tag == 23 else 4
    if not re.fullmatch(rb"[0-9]{"+str(width+10).encode()+rb"}Z", data):
        raise ValueError("time syntax")
    year = int(data[:width])
    if width == 2:
        year += 2000 if year < 50 else 1900
    fields = [int(data[i:i+2]) for i in range(width, width+10, 2)]
    return utc_seconds(dt.datetime(year, *fields))


def expected(kind, c):
    if kind == "validity":
        status = (6 if c.after < c.before else 7 if c.seconds < c.before*10**9
                  else 8 if c.after*10**9 < c.seconds else 0)
        return status, 0, b""
    ptr = c.pointer if c.pointer is not None else (INPUT if kind == "decode" else OUTPUT)+c.alignment
    if kind == "decode":
        n = len(c.body) if c.available is None else c.available
        if c.tag not in (23, 24):
            return 6, 0, b""
        if n != (13 if c.tag == 23 else 15):
            return 1, 0, b""
        if ptr+n > 2**64:
            return 4, 0, b""
        try:
            return 0, decode(c.tag, c.body) & MAX, b""
        except ValueError:
            return 6, 0, b""
    try:
        date = EPOCH+dt.timedelta(seconds=c.seconds)
    except OverflowError:
        return 6, 0, b""
    utc = 1950 <= date.year <= 2049
    raw = body(date, 2 if utc else 4)
    output = bytes((23 if utc else 24, len(raw)))+raw
    if c.capacity < len(output):
        return 5, 0, b""
    if ptr+len(output) > 2**64:
        return 4, 0, b""
    return 0, len(output), output


def write_case(path, kind, c):
    ptr = c.pointer if c.pointer is not None else (INPUT if kind == "decode" else OUTPUT)+c.alignment
    regs = [0]+[0x7251000000000000+i*0x11101 for i in range(1, 32)]
    regs[1:4] = [0x80000, c.stack, 0x700000]
    if kind == "decode":
        regs[10:13] = [c.tag, ptr, len(c.body) if c.available is None else c.available]
    elif kind == "validity":
        regs[10:13] = [c.before & MAX, c.after & MAX, c.seconds & MAX]
    else:
        regs[10:13] = [c.seconds & MAX, ptr, c.capacity]
    regions = [b"\xa5"*(8+c.alignment)+c.body+b"\x5a"*8,
               b"\x61"*32, b"\xa7"*64, b"\x82"*32, b"\x9c"*32, b"\xc4"*432]
    before = struct.pack("<32Q", *regs)+b"".join(regions)
    status, value, output = expected(kind, c)
    after_regs = [0 if i in CALLER else r for i, r in enumerate(regs)]
    after_regs[10:12] = [status, value]
    after_regions = regions[:]
    if output:
        start = 8+c.alignment
        after_regions[2] = regions[2][:start]+output+regions[2][start+len(output):]
    after = struct.pack("<32Q", *after_regs)+b"".join(after_regions)
    path.mkdir(parents=True, exist_ok=True)
    for name, data in (("before.bin", before), ("expected.bin", after),
                       ("sizes.bin", struct.pack("<6Q", *map(len, regions))),
                       ("a.bin", c.body), ("b.bin", b""),
                       ("meta.bin", struct.pack("<2Q", status, value))):
        (path/name).write_bytes(data)
