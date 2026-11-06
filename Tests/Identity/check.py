#!/usr/bin/env python3
"""Real RV64 protobuf and Peer ID execution against Spec, Python and go-libp2p."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from cases import (parse_cases, varint_cases, id_cases, parse, peer_id,
                   ParseError, INPUT, write_case)

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/"build/identity"
sys.path.insert(0, str(ROOT/"Tests/HashCrypto"))
import native
from build import run


def oracle(cases):
    selected = [c for c in cases if c.input == INPUT and c.available is None]
    output = subprocess.run(["go", "run", str(ROOT/"Tests/Identity/oracle.go")],
        cwd=ROOT/"tests/interop/go", input="".join(c.data.hex()+"\n" for c in selected),
        capture_output=True, text=True, check=True, timeout=120)
    lines = output.stdout.splitlines()
    assert len(lines) == len(selected)
    for c, line in zip(selected, lines):
        got = json.loads(line)
        try:
            kind, offset, length = parse(c.data)
        except ParseError:
            assert not got["ok"], (c.name, got)
            continue
        key = c.data[offset:offset+length]
        assert got["ok"] and got["kind"] == kind and got["data"] == key.hex(), (c.name, got)
        if got["peerId"]:
            assert got["peerId"] == peer_id(kind, key).hex(), (c.name, got)
    print(f"PASS go-libp2p protobuf/Peer ID oracle: {len(selected)} cases", flush=True)


def suite(args, kind, cases):
    directory = OUT/kind
    directory.mkdir(parents=True, exist_ok=True)
    for i, c in enumerate(cases):
        write_case(directory/f"case-{i}", kind, c)
    (directory/"count.txt").write_text(str(len(cases)))
    output = run([str(ROOT/".lake/build/bin/libp2p-asm-identity-probe"), kind, str(directory)])
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
    print(run(["lake", "build", "libp2p-asm-identity-probe"]), end="", flush=True)
    oracle(parse_cases())
    for kind, cases in (("varint", varint_cases()), ("publickey", parse_cases()), ("peerid", id_cases())):
        suite(args, kind, cases)


if __name__ == "__main__":
    main()
