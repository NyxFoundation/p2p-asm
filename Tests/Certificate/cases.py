"""Adversarial parser inputs and ABI fixtures with complete expected snapshots."""
from dataclasses import dataclass, replace
import random
import struct
from reference import outcome, patterns, LIBP2P
from fixtures import make, seq, tlv, ext, identity, name, signed
from edges import date_cases, nested_cases

MAX = 2**64-1
CALLER = (5, 6, 7, *range(10, 18), *range(28, 32))


@dataclass(frozen=True)
class Case:
    label: str
    data: bytes
    alignment: int = 0
    updates: tuple = ()
    descriptor: int = 0x500008
    stack: int = 0x6001a0
    resource: bool = False


def grammar_cases():
    b = make()
    result = [Case("synthetic-ed", b)]
    result += [Case("signed-"+label, raw) for label, raw in signed()]
    result += [Case(f"prefix-{i}", b[:i]) for i in range(len(b))]
    result += [Case(f"mutate-{i}", b[:i]+bytes((b[i]^1,))+b[i+1:]) for i in range(len(b))]
    result += [Case("trailing", b+b"\x05\0"), Case("no-identity", make(extensions=[])),
               Case("duplicate-identity", make(extensions=[identity(), identity()])),
               Case("root-extra", make(root_extra=tlv(5, b""))),
               Case("tbs-extra", make(tbs_extra=tlv(5, b"")))]
    for kind, size in ((1, 32), (2, 65), (3, 0)):
        alg = next(raw for raw, k in patterns.known("public").items() if k == kind)
        key = b"\x41"*32 if kind == 1 else b"\x04"+b"\x42"*64 if kind == 2 else seq(
            tlv(2, b"\0"+b"\xa1"*256), tlv(2, b"\x01\x00\x01"))
        signatures = [raw for raw, k in patterns.known("signature").items()
                      if k == kind or kind == 3 and k == 4]
        result += [Case(f"algorithm-{kind}-{i}", make(signature=a, public=alg, key=key))
                   for i, a in enumerate(signatures)]
        result += [Case(f"key-length-{kind}-{n}", make(signature=signatures[0], public=alg,
                       key=key[:n])) for n in (0, 1, max(0, len(key)-1))]
    for i, raw in enumerate((b"", b"\x80", b"\0\x01", b"\0\x80", b"\x7f", b"\0", b"\x01"*21)):
        result.append(Case(f"serial-{i}", make(serial=tlv(2, raw))))
    for version in (b"", b"\0", b"\1", b"\2", b"\3", b"\0\2"):
        result.append(Case("version-"+version.hex(), make(version=tlv(160, tlv(2, version)))))
    return result


def name_cases():
    result = []
    values = {
        12: [b"", b"ascii\0", "日本語🦀".encode(), b"\x80", b"\xc0\x80", b"\xc2\x80",
             b"\xe0\x9f\xbf", b"\xe0\xa0\x80", b"\xed\xa0\x80", b"\xf4\x90\x80\x80",
             b"\xf4\x8f\xbf\xbf", b"\xf0\x80\x80\x80", b"\xf5\x80\x80\x80", b"\xe1"],
        18: [b"", b"0123 ", b"hi", b"\xff"],
        19: [b"", b"AZaz09 '()+,-./:=?", b"@", b"\0", b"\x80"],
        22: [b"", b"\x00\x7f", b"\x80"],
        28: [b"", b"\0", b"\0\x10\xff\xff", b"\0\x11\0\0", b"\0\0\xd8\0"],
        30: [b"", b"\0", b"\0A", b"\xd8\0", b"\xe0\0"],
        20: [b"\xff\x00"],
    }
    for tag, items in values.items():
        result += [Case(f"name-{tag}-{i}", make(subject=name(tag, value)))
                   for i, value in enumerate(items)]
    attrs = sorted([seq(patterns.oid("2.5.4.3"), tlv(12, x)) for x in (b"a", b"b")])
    result += [Case("rdn-sorted", make(subject=seq(tlv(49, b"".join(attrs))))),
               Case("rdn-unsorted", make(subject=seq(tlv(49, b"".join(reversed(attrs)))))),
               Case("rdn-duplicate", make(subject=seq(tlv(49, attrs[0]*2)))),
               Case("rdn-empty", make(subject=seq(tlv(49, b"")))),
               Case("dn-empty", make(issuer=seq(), subject=seq())),
               Case("name-extra", make(subject=seq(tlv(49, seq(
                   patterns.oid("2.5.4.3"), tlv(12, b"a"), tlv(5, b""))))))]
    return result


def extension_cases():
    result = []
    for raw in (b"", b"\x80", b"\x80\0", b"\x81", b"\x81\0", b"\x55\0"):
        result.append(Case("oid-"+raw.hex(), make(extensions=[identity(), ext(raw, b"opaque")])))
    for critical in (None, False, True):
        unknown = ext(b"\x55\x01", b"not ASN.1", critical)
        result += [Case(f"unknown-{critical}", make(extensions=[identity(), unknown])),
                   Case(f"unknown-duplicate-{critical}",
                        make(extensions=[unknown, unknown, identity()]))]
    for raw in (b"", b"\0", b"\1", b"\x07\x80", b"\0\x80", b"\x07\x01",
                b"\x07\x80\x80", b"\x07\0\x80", b"\0\0", b"\x08\x80"):
        result.append(Case("key-usage-"+raw.hex(), make(extensions=[
            identity(), ext(bytes.fromhex("551d0f"), tlv(3, raw), True)])))
    for i, value in enumerate((seq(), seq(tlv(1, b"\0")), seq(tlv(1, b"\xff")),
                              seq(tlv(1, b"\xff"), tlv(2, b"\0")),
                              seq(tlv(1, b"\0"), tlv(2, b"\0")), seq(tlv(2, b"\0")),
                              seq(tlv(1, b"\1")), seq(tlv(1, b"\xff"), tlv(2, b"\x80")))):
        result.append(Case(f"constraints-{i}", make(extensions=[
            identity(), ext(bytes.fromhex("551d13"), value, True)])))
    for i, ids in enumerate(([], ["2.5.29.37.0"], ["1.3.6.1.5.5.7.3.1"],
                            ["1.3.6.1.5.5.7.3.2"], ["1.3.6.1.5.5.7.3.1", "1.3.6.1.5.5.7.3.2"],
                            ["1.2.3.4"], ["2.5.29.37.0", "1.2.3.4"])):
        result.append(Case(f"eku-{i}", make(extensions=[
            identity(), ext(bytes.fromhex("551d25"), seq(*(patterns.oid(x) for x in ids)), True)])))
    for size in (1, 16, 64):
        unknowns = [ext(b"\x55"+bytes((i+1,)), b"opaque") for i in range(size)]
        result += [Case(f"unknown-batch-{size}", make(extensions=unknowns+[identity()])),
                   Case(f"duplicate-batch-{size}", make(extensions=unknowns+[identity(), unknowns[0]]))]
    return result


def semantic_cases():
    result = []
    for i, values in enumerate(((tlv(23, b"500101000000Z"), tlv(24, b"99991231235959Z")),
        (tlv(23, b"000229010203Z"), tlv(23, b"000229010203Z")),
        (tlv(24, b"00010101000000Z"), tlv(23, b"500101000000Z")),
        (tlv(23, b"000230010203Z"), tlv(23, b"010101000000Z")),
        (tlv(23, b"010101000000Z"), tlv(23, b"000101000000Z")),
        (tlv(23, b""),), (tlv(24, b"20000101000000Z"), tlv(23, b"000101000000Z"), tlv(5, b"")))):
        result.append(Case(f"time-{i}", make(validity=seq(*values))))
    result += [Case("signature-not-bits", make(signature_bits=tlv(4, b"sig"))),
               Case("signature-empty", make(signature_bits=tlv(3, b""))),
               Case("signature-unused", make(signature_bits=tlv(3, b"\1sig"))),
               Case("signature-algorithm-mismatch", make(
                   outer_signature=patterns.algorithm("1.2.840.10045.4.3.2")))]
    rng = random.Random(5280001)
    result += [Case(f"random-{i}", rng.randbytes(rng.randrange(0, 512))) for i in range(80)]
    return result


def abi_cases():
    b = make()
    n = len(b)
    work = 512+4*n
    result = [Case("unaligned", b, alignment=1), Case("empty-unmapped", b"", updates=((0, MAX),)),
              Case("input-huge", b, updates=((1, 2**61),)), Case("max-input", b, updates=((1, MAX),)),
              Case("operation-budget-exhausted", b, updates=((7, 1),), resource=True)]
    updates = [(3, x) for x in (0, 1, 167, 168, MAX)]
    updates += [(5, x) for x in (0, work-1, work, MAX)]
    updates += [(6, x) for x in (0, n-1, n, MAX)]+[(7, 0), (7, MAX)]
    updates += [(0, MAX), (2, MAX), (4, MAX-7), (4, 0x400009)]
    updates += [(0, 0x300008), (0, 0x500008), (2, 0x500008), (4, 0x300008),
                (4, 0x100008), (2, 0x600170), (4, 0x600100)]
    result += [Case(f"descriptor-{i}-{v}", b, updates=((i, v),)) for i, v in updates]
    result += [Case(f"descriptor-pointer-{p}", b, descriptor=p) for p in (0x500009, MAX-7)]
    result += [Case(f"stack-{p}", b, stack=p) for p in (0, 128, MAX, 0x600198)]
    return result


def cases():
    return (grammar_cases()+name_cases()+extension_cases()+semantic_cases()+abi_cases()
            + date_cases(Case)+nested_cases(Case))


def metadata(c):
    fields = [0x100008+c.alignment, len(c.data), 0x300008+c.alignment, 168,
              0x400008, 512+4*len(c.data), 16384, 100000]
    for i, value in c.updates:
        fields[i] = value
    return fields


def preflight(c, d):
    span = lambda p, n: n == 0 or p+n <= 2**64
    if c.descriptor % 8 or not span(c.descriptor, 64):
        return 4
    if d[1] >= 2**61:
        return 2
    if d[6] == 0 or d[1] > d[6] or d[7] == 0:
        return 12
    if d[3] < 168 or d[5] < 512+4*d[1]:
        return 5
    if d[4] % 8 or c.stack < 144 or c.stack % 16:
        return 4
    spans = [(c.descriptor, 64), (c.stack-144, 144), (d[0], d[1]),
             (d[2], 168), (d[4], 512+4*d[1])]
    if any(not span(p, n) for p, n in spans):
        return 4
    if any(n and m and a < b+m and b < a+n for i, (a, n) in enumerate(spans)
           for b, m in spans[i+1:]):
        return 4
    return 0


def write_case(path, c):
    d = metadata(c)
    status = preflight(c, d)
    admitted = status == 0
    values = ()
    if admitted:
        status, values = outcome(c.data)
        if c.resource:
            assert status == 0 and d[7] == 1
            status, values = 12, ()
    wipe, depth = (512+4*len(c.data), 144) if admitted else (0, 0)
    regs = [0]+[0x7251000000000000+i*0x11101 for i in range(1, 32)]
    regs[1:4] = [0x80000, c.stack, 0x700000]
    regs[10] = c.descriptor
    regions = [b"\xa5"*(8+c.alignment)+c.data+b"\x5a"*8, b"\x61"*32,
               b"\xa7"*(184+c.alignment), b"\x82"*(528+4*len(c.data)),
               b"\x9c"*8+struct.pack("<8Q", *d)+b"\xc9"*8, b"\xc4"*432]
    after_regs = [0 if i in CALLER else v for i, v in enumerate(regs)]
    after_regs[10] = status
    after = regions[:]
    if status == 0:
        pos = 8+c.alignment
        output = struct.pack("<21Q", *values)
        after[2] = after[2][:pos]+output+after[2][pos+168:]
    if admitted:
        after[3] = after[3][:8]+bytes(wipe)+after[3][8+wipe:]
        after[5] = after[5][:416-depth]+bytes(depth)+after[5][416:]
    path.mkdir(parents=True, exist_ok=True)
    content = {"before.bin": struct.pack("<32Q", *regs)+b"".join(regions),
               "expected.bin": struct.pack("<32Q", *after_regs)+b"".join(after),
               "sizes.bin": struct.pack("<6Q", *map(len, regions)), "a.bin": c.data, "b.bin": b"",
               "meta.bin": struct.pack("<5Q", status, wipe, depth, int(c.resource), c.alignment),
               "label.txt": c.label.encode()}
    for name_, data in content.items():
        (path/name_).write_bytes(data)
