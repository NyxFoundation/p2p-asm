#!/usr/bin/env python3
"""Compare Python Gregorian arithmetic, pure Spec, real RV64IM and QEMU."""
import argparse
import os
from pathlib import Path
import sys
from cases import decode_cases, encode_cases, validity_cases, write_case

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/"Tests/HashCrypto"))
import native
from build import run


def suite(args, kind, cases):
    directory = ROOT/"build/certificate-time"/kind
    directory.mkdir(parents=True, exist_ok=True)
    for i, c in enumerate(cases):
        write_case(directory/f"case-{i}", kind, c)
    (directory/"count.txt").write_text(str(len(cases)))
    output = run([str(ROOT/".lake/build/bin/libp2p-asm-time-probe"), kind, str(directory)])
    (directory/"model.txt").write_text(output)
    native.prepare(args.prefix, directory)
    script = native.linker(directory)
    for i, c in enumerate(cases):
        path = directory/f"case-{i}"
        expected = (path/"expected.bin").read_bytes()
        assert (path/"after.bin").read_bytes() == expected, (kind, c.name)
        native.execute(args, directory, path, expected, script)
    print(f"PASS {kind}: {len(cases)} Spec/model/footprint/GNU/two-QEMU cases", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    print(run(["lake", "build", "libp2p-asm-time-probe"]), end="", flush=True)
    for kind, cases in (("decode", decode_cases()), ("encode", encode_cases()),
                        ("validity", validity_cases())):
        suite(args, kind, cases)


if __name__ == "__main__":
    main()
