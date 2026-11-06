#!/usr/bin/env python3
"""Run every modeled instruction through Lean, independent arithmetic, GNU and QEMU."""

import argparse
import os
import random
import struct

from check import MASK, ROOT, build_program, run, run_probe
from probe import source

CANARY = 0x11223344
GUARD = 0xA5A5A5A5A5A5A5A5


def signed(value):
    return value if value < (1 << 63) else value - (1 << 64)


OPERATIONS = {
    "add": lambda a, b: a + b,
    "sub": lambda a, b: a - b,
    "and": lambda a, b: a & b,
    "or": lambda a, b: a | b,
    "xor": lambda a, b: a ^ b,
    "sll": lambda a, b: a << (b & 63),
    "srl": lambda a, b: a >> (b & 63),
    "sra": lambda a, b: signed(a) >> (b & 63),
    "slt": lambda a, b: int(signed(a) < signed(b)),
    "sltu": lambda a, b: int(a < b),
    "addi": lambda a, b: a - 2048,
    "andi": lambda a, b: a & -2048,
    "ori": lambda a, b: MASK,
    "xori": lambda a, b: a ^ MASK,
    "slli": lambda a, b: a << 63,
    "srli": lambda a, b: a >> 63,
    "srai": lambda a, b: signed(a) >> 63,
    "lui": lambda a, b: 0xFFFFFFFF80000000,
    "auipc": lambda a, b: 0xF000,
    "mul": lambda a, b: a * b,
    "mulhu": lambda a, b: (a * b) >> 64,
    "divu": lambda a, b: a // b if b else MASK,
    "remu": lambda a, b: a % b if b else a,
    "lbu": lambda a, b: b & 255,
    "ld": lambda a, b: b,
    "sb": lambda a, b: b & 255,
    "sd": lambda a, b: b,
    "beq": lambda a, b: 2 if a == b else 1,
    "bne": lambda a, b: 2 if a != b else 1,
    "bltu": lambda a, b: 2 if a < b else 1,
    "bgeu": lambda a, b: 2 if a >= b else 1,
    "jal": lambda a, b: 0x10004,
    "jalr": lambda a, b: 0x10004,
}


def check_case(args, name, a, b, out, expected):
    pointer = name in ("lbu", "ld", "sb", "sd")
    lhs = 0x20000 if pointer else 0x10001 if name == "jalr" else a
    data_word = b ^ MASK if name in ("sb", "sd") else b
    data = struct.pack("<QQ", data_word, GUARD)
    arguments = f"  li a0, {lhs}\n  li a1, {b}\n  li s0, {CANARY}"
    actual = run_probe(args, out, source(arguments, data), expected)
    modified = bytearray(data)
    if name == "sb":
        modified[0] = b & 255
    if name == "sd":
        modified[:8] = struct.pack("<Q", b)
    result = OPERATIONS[name](a, b) & MASK
    reference = struct.pack("<QQQ", result, b, CANARY) + modified
    generator = ROOT / ".lake/build/bin/libp2p-asm-isa-probe"
    model = bytes.fromhex(run([str(generator), "eval", name, str(a), str(b)]).strip())
    if actual != reference or model != reference:
        raise AssertionError(f"ISA mismatch: {name}, a={a}, b={b}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    cases = [(0, 0), (1, 0), (0, 1), (1, 1), (MASK, MASK), (MASK, 1),
             (1 << 63, 1), (1, 1 << 63), (MASK, 63), (MASK, 64), (MASK, 65),
             (1 << 63, MASK), (0x01020304050607FF, 255)]
    rng = random.Random(64)
    cases += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(8)]
    for name in OPERATIONS:
        out, expected = build_program(args, name, "libp2p-asm-isa-probe", "isa")
        for a, b in cases:
            check_case(args, name, a, b, out, expected)
    print(f"PASS: should match all {len(OPERATIONS)} modeled instructions: "
          f"{len(OPERATIONS) * len(cases)} QEMU/model/reference cases with guards")


if __name__ == "__main__":
    main()
