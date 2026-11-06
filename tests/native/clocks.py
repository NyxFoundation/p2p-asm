#!/usr/bin/env python3
"""Check clock policy against independent integer arithmetic, Lean and both QEMU paths."""

import argparse
import itertools
import json
import os
import random
import struct

from check import MASK, ROOT, build_program, run, run_probe
from probe import source

BILLION = 1_000_000_000
GUARD = 0xCAFED00D
PRESERVED = ("sp", "gp", "tp", *(f"s{i}" for i in range(12)))


def signed(value):
    return value if value < 1 << 63 else value - (1 << 64)


def reference(state, sample, drift, span):
    mode, previous, seconds, nanos = state
    source_status, before, after, new_seconds, new_nanos = sample
    if not drift or not span or span > drift:
        return 3, state
    if mode > 4 or (mode in (1, 4) and nanos >= BILLION):
        return 4, state
    if mode == 3:
        return 2, state
    if source_status >= 2 or before > after or (mode and before < previous):
        return 2, (3, previous, 0, 0)
    if source_status or after - before > span or new_nanos >= BILLION:
        return 1, (2, after, 0, 0)
    candidate = (4, after, new_seconds, new_nanos)
    if mode == 2:
        return 1, candidate
    wall = (signed(new_seconds) - signed(seconds)) * BILLION + new_nanos - nanos
    if mode and (wall < 0 or abs(wall - (after - previous)) > drift):
        return 1, candidate
    return 0, (1, after, new_seconds, new_nanos)


def driver(data, drift, span):
    setup = "\n".join(f"  li {reg}, {0x10203040 + i}" for i, reg in enumerate(PRESERVED))
    arguments = (f"{setup}\n  la a0, payload\n  addi a1, a0, 40\n"
                 f"  li a2, {drift}\n  li a3, {span}")
    validate = "\n".join(f"  li t5, {0x10203040 + i}\n  bne {reg}, t5, abi_fail"
                         for i, reg in enumerate(PRESERVED))
    program = source(arguments, data).replace(
        "  jal ra, protocol_entry",
        "  jal ra, protocol_entry\nreturned:\n  la t5, returned\n"
        "  bne ra, t5, abi_fail\n" + validate)
    return program.replace('.section .data, "aw", @progbits',
        'abi_fail:\n  li a0, 42\n  li a7, 93\n  ecall\n.section .data, "aw", @progbits')


def cases():
    base = (0, 100, 200, 1794000000, 500000000)
    for mode, status in itertools.product((0, 1, 2, 3, 4, 5, MASK), (0, 1, 2, 3, MASK)):
        yield (mode, 50, base[3], base[4]), (status, *base[1:]), 250000000, 1000000
    epochs = (1 << 63, MASK, 0, 1, 1794000000, (1 << 63) - 1)
    for old, new, ns in itertools.product(epochs, epochs, (0, 1, 499999999, 999999999, BILLION, MASK)):
        yield (1, 0, old, 500000000), (*base[:3], new, ns), 250000000, 1000000
    for drift, mono, seconds in itertools.product(
            (0, 1, 250000000, 1 << 63, MASK), (0, 1, 250000000, 1 << 63, MASK),
            (0, 1, 18446744073, 18446744074, 36893488147, (1 << 63) - 1)):
        yield (1, 0, 0, 0), (0, mono, mono, seconds, 0), drift, 1
    for before in (0, 1, 199, 200, 201, 1000200):
        yield (1, 200, 0, 0), (0, before, *base[2:]), 250000000, 1000000
    yield (4, 0, 0, BILLION), base, 250000000, 1000000
    yield (0, 0, 0, 0), base, 1, 2
    rng = random.Random(53594)
    for _ in range(100):
        sec, ns = rng.getrandbits(64), rng.randrange(BILLION)
        previous = rng.getrandbits(63)
        elapsed = rng.randrange(10 * BILLION)
        seconds, nanos = divmod(signed(sec) * BILLION + ns + elapsed + rng.randrange(-250000001, 250000002), BILLION)
        yield (1, previous, sec, ns), (0, previous + elapsed, previous + elapsed,
                                       seconds & MASK, nanos), 250000000, 1000000


def encoded_program(args, out, expected):
    encoded = out / "encoded"
    encoded.mkdir(exist_ok=True)
    (encoded / "code.bin").write_bytes(expected)
    asm = ('.section .text.protocol, "ax", @progbits\n.global protocol_entry\n'
           f'protocol_entry:\n.incbin {json.dumps(str(encoded / "code.bin"))}\n')
    (encoded / "protocol.S").write_text(asm)
    run([args.prefix + "as", "-march=rv64im", "-mabi=lp64", "-o",
         str(encoded / "protocol.o"), str(encoded / "protocol.S")])
    return encoded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    out, expected = build_program(args, "clock-check")
    encoded = encoded_program(args, out, expected)
    generator = ROOT / ".lake/build/bin/libp2p-asm-codegen"
    count = 0
    for state, sample, drift, span in cases():
        data = struct.pack("<10Q", *state, GUARD, *sample)
        status, next_state = reference(state, sample, drift, span)
        wanted = struct.pack("<13Q", status, 0, 0, *next_state, GUARD, *sample)
        model = bytes.fromhex(run([str(generator), "eval-clock", data.hex(), str(drift), str(span)]).strip())
        for path in (out, encoded):
            actual = run_probe(args, path, driver(data, drift, span), expected)
            if actual != wanted or model != wanted:
                raise AssertionError(f"Clock mismatch: {state}, {sample}, {drift}, {span}")
        count += 1
    print(f"PASS: clock policy {count} cases: Python, Lean, GNU and encoded QEMU; ABI and guards")


if __name__ == "__main__":
    main()
