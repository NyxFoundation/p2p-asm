#!/usr/bin/env python3
"""Compare buffer-reference resolution, including malformed raw ABI fields."""

import argparse
import os
import random
import struct

from check import MASK, ROOT, build_program, run, run_probe
from probe import source


def reference(regions, ref, access, count):
    slot, generation, offset, length = ref
    if access > 1 or count >= (1 << 59):
        return 4, 0, 0
    if slot >= count:
        return 1, 0, 0
    expected_generation, base, capacity, flags = regions[slot]
    if flags > 3:
        return 4, 0, 0
    if not (flags & 1) or generation != expected_generation:
        return 2, 0, 0
    if not capacity or base + capacity > MASK:
        return 4, 0, 0
    if access and not (flags & 2):
        return 5, 0, 0
    if length > capacity or offset > capacity - length:
        return 3, 0, 0
    return 0, base + offset, length


def check_case(args, out, expected, regions, ref, access=0, count=None):
    count = len(regions) if count is None else count
    data = b"".join(struct.pack("<QQQQ", *row) for row in [*regions, ref])
    offset = len(regions) * 32
    arguments = (f"  la a0, payload\n  la a1, payload\n  addi a1, a1, {offset}\n"
                 f"  li a2, {count}\n  li a3, {access}")
    actual = run_probe(args, out, source(arguments, data), expected)
    result = struct.pack("<QQQ", *reference(regions, ref, access, count)) + data
    generator = ROOT / ".lake/build/bin/libp2p-asm-codegen"
    model = bytes.fromhex(run([str(generator), "eval-buffer", data.hex(), str(offset),
                               str(count), str(access)]).strip())
    if actual != result or model != result:
        raise AssertionError(f"Buffer resolution mismatch: {regions}, {ref}, {access}, {count}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    out, expected = build_program(args, "buffer-resolve")
    count = 0
    for base, capacity in ((0, 0), (0, 1), (0x30000, 16), (MASK - 16, 16),
                           (MASK - 15, 16), (MASK, 1)):
        for offset in (0, 1, 8, 16, MASK):
            for length in (0, 1, 8, 16, MASK):
                check_case(args, out, expected, [(7, base, capacity, 3)], (0, 7, offset, length))
                count += 1
    for flags in (0, 1, 2, 3, 4, 7, MASK):
        for access in (0, 1, 2, MASK):
            check_case(args, out, expected, [(7, 0x30000, 16, flags)], (0, 7, 4, 8), access)
            count += 1
    for generation in (0, 6, 7, MASK):
        check_case(args, out, expected, [(7, 0x30000, 16, 3)], (0, generation, 4, 8))
        count += 1
    for slots in (0, 1 << 59, MASK):
        check_case(args, out, expected, [(7, 0x30000, 16, 3)], (0, 7, 4, 8), count=slots)
        count += 1
    rng = random.Random(53594)
    regions = [(7, 0x30000, 16, 3), (MASK, 0x40000, 32, 1), (12, MASK - 255, 255, 3)]
    for _ in range(100):
        slot = rng.randrange(4)
        generation = regions[slot][0] if slot < len(regions) else 0
        ref = (slot, generation, rng.randrange(300), rng.randrange(260))
        check_case(args, out, expected, regions, ref, rng.randrange(2))
        count += 1
    print(f"PASS: should match buffer resolution ASM/model/reference: {count} QEMU cases")


if __name__ == "__main__":
    main()
