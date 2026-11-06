#!/usr/bin/env python3
"""Spec, actual instructions, independent Python/Go, GNU bytes and both QEMU paths."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from cases import decode_cases, encode_cases, decode, supported, write_case

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "build/der"
sys.path.insert(0, str(ROOT / "Tests/HashCrypto"))
import native
from build import run


def oracle(cases):
    selected = [c for c in cases if c.pointer is None and c.available is None
                and (not c.data or supported(c.data[0]))]
    output = subprocess.run(["go", "run", str(ROOT/"Tests/Der/oracle.go")],
                            input="".join(c.data.hex()+"\n" for c in selected),
                            capture_output=True, text=True, check=True, timeout=120)
    lines = output.stdout.splitlines()
    assert len(lines) == len(selected)
    for c, line in zip(selected, lines):
        status, fields = decode(c.data)
        got = json.loads(line)
        assert got["ok"] == (status == 0), (c.name, got, status)
        if status == 0:
            assert got["fields"] == list(fields), (c.name, got, fields)
    print(f"PASS Go ASN.1 oracle: {len(selected)} header cases", flush=True)


def suite(args, kind, cases):
    directory = OUT/kind
    directory.mkdir(parents=True, exist_ok=True)
    for i, c in enumerate(cases):
        write_case(directory/f"case-{i}", kind, c)
    (directory/"count.txt").write_text(str(len(cases)))
    output = run([str(ROOT/".lake/build/bin/libp2p-asm-der-probe"), kind, str(directory)])
    (directory/"model.txt").write_text(output)
    native.prepare(args.prefix, directory)
    script = native.linker(directory)
    for i, c in enumerate(cases):
        path = directory/f"case-{i}"
        expected = (path/"expected.bin").read_bytes()
        assert (path/"after.bin").read_bytes() == expected, (kind, c.name, "oracle mismatch")
        native.execute(args, directory, path, expected, script)
    print(f"PASS {kind}: {len(cases)} Spec/model/snapshot/footprint/GNU/two-QEMU cases", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    print(run(["lake", "build", "libp2p-asm-der-probe"]), end="", flush=True)
    oracle(decode_cases())
    suite(args, "decode", decode_cases())
    suite(args, "encode", encode_cases())


if __name__ == "__main__":
    main()
