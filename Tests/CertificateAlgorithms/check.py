#!/usr/bin/env python3
"""Exact ASN.1 AlgorithmIdentifier grammar through real RV64IM, GNU and QEMU."""
import argparse
import os
from pathlib import Path
import sys
from cases import cases, write_case

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/"Tests/HashCrypto"))
import native
from build import run


def suite(args, kind):
    inputs = cases(kind)
    directory = ROOT/"build/certificate-algorithms"/kind
    directory.mkdir(parents=True, exist_ok=True)
    for i, case in enumerate(inputs):
        write_case(directory/f"case-{i}", kind, case)
    (directory/"count.txt").write_text(str(len(inputs)))
    output = run([str(ROOT/".lake/build/bin/libp2p-asm-algorithms-probe"), kind, str(directory)])
    (directory/"model.txt").write_text(output)
    native.prepare(args.prefix, directory)
    script = native.linker(directory)
    for i, case in enumerate(inputs):
        path = directory/f"case-{i}"
        expected = (path/"expected.bin").read_bytes()
        assert (path/"after.bin").read_bytes() == expected, (kind, case.name)
        native.execute(args, directory, path, expected, script)
    print(f"PASS {kind}: {len(inputs)} Spec/model/footprint/GNU/two-QEMU cases", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    print(run(["lake", "build", "libp2p-asm-algorithms-probe"]), end="", flush=True)
    for kind in ("signature", "public"):
        suite(args, kind)


if __name__ == "__main__":
    main()
