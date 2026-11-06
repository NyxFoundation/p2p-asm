#!/usr/bin/env python3
"""Compare Lean emission with GNU encoding and run the resulting ELF in QEMU."""

import argparse
import os
from pathlib import Path
import random
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]
MASK = (1 << 64) - 1


def run(command, *, text=True):
    return subprocess.run(
        command, cwd=ROOT, check=True, capture_output=True, text=text, timeout=30
    ).stdout


def driver(a, b):
    return f"""
.option norvc
.option norelax
.section .text.start, "ax", @progbits
.global _start
_start:
  li a0, {a}
  li a1, {b}
  li s0, 0x11223344
  jal ra, protocol_entry
  la t0, output
  sd a0, 0(t0)
  sd a1, 8(t0)
  sd s0, 16(t0)
  li a0, 1
  mv a1, t0
  li a2, 24
  li a7, 64
  ecall
  li a0, 0
  li a7, 93
  ecall
.section .bss, "aw", @nobits
.balign 8
output:
  .skip 24
"""


def build_program(args, name, executable="libp2p-asm-codegen", group=""):
    out = ROOT / "build" / "native" / group / name
    out.mkdir(parents=True, exist_ok=True)
    generator = ROOT / ".lake" / "build" / "bin" / executable
    assembly = run([str(generator), "asm", name])
    expected = bytes.fromhex(run([str(generator), "hex", name]).strip())
    (out / "protocol.S").write_text(assembly)
    run([args.prefix + "as", "-march=rv64im", "-mabi=lp64",
         "-o", str(out / "protocol.o"), str(out / "protocol.S")])
    return out, expected


def run_probe(args, out, source, expected):
    (out / "driver.S").write_text(source)
    run([args.prefix + "as", "-march=rv64im", "-mabi=lp64",
         "-o", str(out / "driver.o"), str(out / "driver.S")])
    run([args.prefix + "ld", "--no-relax", "-T", str(ROOT / "tests/native/link.ld"),
         "-o", str(out / "probe.elf"), str(out / "protocol.o"), str(out / "driver.o")])
    run([args.prefix + "objcopy", "-O", "binary", "--only-section=.text.protocol",
         str(out / "probe.elf"), str(out / "protocol.bin")])
    actual = (out / "protocol.bin").read_bytes()
    if actual != expected:
        raise AssertionError("GNU encoding differs from Lean encoding")
    return run([args.qemu, str(out / "probe.elf")], text=False)


def check_case(args, name, a, b, out, expected):
    output = run_probe(args, out, driver(a, b), expected)
    result = (a + b) & MASK if name == "add" else min(a, b)
    generator = ROOT / ".lake" / "build" / "bin" / "libp2p-asm-codegen"
    model = bytes.fromhex(run([str(generator), "eval", name, str(a), str(b)]).strip())
    reference = struct.pack("<QQQ", result, b, 0x11223344)
    if output != reference or model != reference:
        raise AssertionError(f"RV64/model/reference or preserved registers differ for {name}: {a}, {b}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    rng = random.Random(9000)
    values = [0, 1, 42, (1 << 63) - 1, 1 << 63, MASK]
    cases = [(a, b) for a in values for b in values]
    cases += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    for name in ("add", "min"):
        out, expected = build_program(args, name)
        for a, b in cases:
            check_case(args, name, a, b, out, expected)
        print(f"PASS: should match model arithmetic and GNU bytes for {name}: {len(cases)} QEMU cases")


if __name__ == "__main__":
    main()
