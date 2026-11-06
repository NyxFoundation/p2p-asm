"""Snapshot fixtures are independently constructed here and checked by Lean and QEMU."""
import struct

from fixtures import oracle, required, tables

PRESERVED = (1, 2, 3, 4, 8, 9, *range(18, 28))


def guarded(payload, alignment=0):
    return b"\xa5"*(8+alignment) + payload + b"\x5a"*8


def arguments(kind, case, alignment, need):
    na = len(case.a) if case.declared_a is None else case.declared_a
    nb = len(case.b) if case.declared_b is None else case.declared_b
    a = 0x100008 + alignment if len(case.a) else (1 << 64)-1
    b = 0x200008 + alignment if len(case.b) else (1 << 64)-1
    if case.bad_pointer:
        a = (1 << 64)-2
    out, work, table = 0x300008 + alignment, 0x400008 + case.bad_alignment, 0x500008
    if case.bad_range == "output":
        out = (1 << 64)-2
    elif case.bad_range == "second":
        b = (1 << 64)-2
    elif case.bad_range == "workspace":
        work = (1 << 64)-8
    elif case.bad_range == "constants":
        table = (1 << 64)-8
    if kind == "length512":
        return [case.length, out-112]
    capacity = need+17 if case.capacity is None else case.capacity
    if kind.startswith("sha"):
        return [a, na, out, work, capacity, table]
    if kind in ("hmac", "extract"):
        return [a, na, b, nb, out, work, capacity, table]
    if kind == "expand":
        return [a, na, b, nb, out, case.length, work, capacity]
    return [a, na, b, nb, case.length, out, capacity]


def write_case(directory, kind, case, index):
    directory.mkdir(parents=True, exist_ok=True)
    alignment = index % 8
    result = b"" if case.status else oracle(kind, case)
    if case.published:
        assert result.startswith(case.published), (kind, case.name, "published vector mismatch")
    need = required(kind, case) if case.length < 65536 else 1024
    if kind == "length512":
        need = 0
    if kind == "tls":
        need = 10 + len(case.a) + len(case.b)
    used = need if case.status == 0 and kind not in ("tls", "length512") else 0
    depth = (176 if kind.startswith("sha") else 400 if kind == "expand" else 288)
    depth = 0 if case.status or kind in ("tls", "length512") or (kind == "expand" and case.length == 0) else depth
    registers = [0] + [0x8192a3b4c5d6e700 + 64*index + i for i in range(1, 32)]
    registers[1:4] = [0x80000, 0x6001a0, 0x700000]
    args = arguments(kind, case, alignment, need)
    registers[10:10+len(args)] = args
    stack = bytearray(b"\x69"*432)
    stack[416:424] = struct.pack("<Q", (1 << 64)-8 if case.bad_range == "constants" else 0x500008)
    output_size = max(64, len(result), need+17 if kind == "tls" else 0)
    regions = [guarded(case.a, alignment), guarded(case.b, alignment),
               guarded(b"\xcc"*output_size, alignment), guarded(b"\xcc"*(need+17)),
               guarded(tables(kind)), bytes(stack)]
    before = struct.pack("<32Q", *registers) + b"".join(regions)
    expected_regs = [value if i in PRESERVED else 0 for i, value in enumerate(registers)]
    expected_regs[10] = case.status
    after = list(regions)
    if case.status == 0:
        start = 8+alignment
        after[2] = after[2][:start] + result + after[2][start+len(result):]
    after[3] = after[3][:8] + bytes(used) + after[3][8+used:]
    after[5] = after[5][:416-depth] + bytes(depth) + after[5][416:]
    expected = struct.pack("<32Q", *expected_regs) + b"".join(after)
    for name, data in (("a", case.a), ("b", case.b), ("before", before), ("expected", expected),
                       ("sizes", struct.pack("<6Q", *(len(r) for r in regions))),
                       ("meta", struct.pack("<6Q", case.status, used, depth, case.length,
                                            case.trace, alignment))):
        (directory / f"{name}.bin").write_bytes(data)
    (directory / "name.txt").write_text(case.name)
    return expected
