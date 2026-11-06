#!/usr/bin/env python3
"""Check real SHA-2 RV64 compression against Lean, GNU, QEMU and hashlib."""

import argparse
import os
import struct

from build import OUT, ROOT, build, run
import native
import reference


def suite(args, lean, env, width):
    name = "sha256" if width == 32 else "sha512"
    directory = OUT / name
    directory.mkdir(parents=True, exist_ok=True)
    cases, messages = reference.fixtures(width)
    reference.write_cases(directory, cases)
    print(run([lean, "--run", str(ROOT / "Tests/AsmCrypto/Probe.lean"), name, str(directory)],
              env=env, timeout=300), end="", flush=True)
    constants = b"".join(struct.pack("<Q", k) for k in reference.constants(width))
    assert (directory / "constants.bin").read_bytes() == constants, "fixed table artifact differs"
    native.prepare(args.prefix, directory)
    for case, (state, block) in enumerate(cases):
        before = (directory / f"case-{case}.before.bin").read_bytes()
        offset = 256 + 80 + 2 * width + 16 + case % 8 + 8
        assert before[offset:offset + len(constants)] == constants, "passed immutable table differs"
        expected = native.expected_snapshot(before, reference.compress(state, block, width), width, case)
        assert (directory / f"case-{case}.after.bin").read_bytes() == expected, "model/oracle mismatch"
        native.execute(args, directory, width, case, expected)
    print(f"PASS {name}: {len(cases)} cases on each of GNU and encodeProgram QEMU ELFs; "
          f"{messages} independently padded hashlib messages", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    lean, env = build(["Tests.AsmCrypto.ProofAudit", "Tests.AsmCrypto.Probe"])
    for width in (32, 64):
        suite(args, lean, env, width)


if __name__ == "__main__":
    main()
