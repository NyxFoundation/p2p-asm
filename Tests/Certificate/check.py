#!/usr/bin/env python3
"""Certificate structure: independent parser, Spec, RV64, GNU bytes, two QEMU paths."""
import argparse
import importlib.util
import json
import os
import subprocess
import sys
from build import compile_probe, ROOT
from cases import cases, write_case

# Reuse the existing six-region native harness, not its fixture/reference logic.
sys.path.insert(0, str(ROOT/"Tests/HashCrypto"))
native_spec = importlib.util.spec_from_file_location(
    "certificate_native", ROOT/"Tests/HashCrypto/native.py")
native = importlib.util.module_from_spec(native_spec)
native_spec.loader.exec_module(native)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    p.add_argument("--prefix", default=os.environ.get("RISCV_PREFIX", "riscv64-unknown-elf-"))
    p.add_argument("--match", default="")
    args = p.parse_args()
    fixtures = [c for c in cases() if args.match in c.label]
    assert fixtures, "empty certificate suite"
    directory = ROOT/"build/certificate"/("full" if not args.match else "selected")
    directory.mkdir(parents=True, exist_ok=True)
    for i, c in enumerate(fixtures):
        write_case(directory/f"case-{i}", c)
    (directory/"count.txt").write_text(str(len(fixtures)))
    probe = compile_probe()
    subprocess.run([str(probe), str(directory)], cwd=ROOT, check=True, timeout=1800)
    native.prepare(args.prefix, directory)
    linker = native.linker(directory)
    for i, c in enumerate(fixtures):
        path = directory/f"case-{i}"
        expected = (path/"expected.bin").read_bytes()
        assert (path/"after.bin").read_bytes() == expected, c.label
        native.execute(args, directory, path, expected, linker)
    counts = [int((directory/f"case-{i}"/"count.txt").read_text()) for i in range(len(fixtures))]
    size = len((directory/"encoded.bin").read_bytes())//4
    covered = bytearray(size)
    for i in range(len(fixtures)):
        visits = (directory/f"case-{i}"/"coverage.bin").read_bytes()
        assert len(visits) == size
        for pc, seen in enumerate(visits):
            covered[pc] |= seen
    report = {"cases": len(fixtures), "qemu_executions": 2*len(fixtures),
              "static_instructions": size, "executed_instructions": sum(covered),
              "instruction_coverage": sum(covered)/size,
              "instructions_max": max(counts), "instruction_bound_is_proved": False,
              "certificate_authentication": False, "full_correspondence_proof": False}
    (directory/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"PASS certificate: {len(fixtures)} structural/Spec/footprint/snapshot/GNU/two-QEMU cases")


if __name__ == "__main__":
    main()
