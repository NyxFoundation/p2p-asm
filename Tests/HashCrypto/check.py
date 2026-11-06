#!/usr/bin/env python3
"""Model/spec/Python, GNU byte equality and both QEMU encoding paths."""
import argparse
import hashlib
import os

from build import OUT, ROOT, build, run
from fixtures import all_cases
from cases import write_case
import native


def suite(args, kind):
    directory = OUT / kind
    directory.mkdir(parents=True, exist_ok=True)
    cases = all_cases(kind)
    for i, case in enumerate(cases):
        write_case(directory / f"case-{i}", kind, case, i)
    (directory / "count.txt").write_text(str(len(cases)))
    output = run([str(ROOT / ".lake/build/bin/libp2p-asm-hash-probe"), kind, str(directory)],
                 timeout=3600)
    print(output, end="", flush=True)
    (directory / "model.txt").write_text(output)
    if kind in ("sha256", "sha512"):
        pinned = {"sha256": "c1b23252c841d98336099a8a3a54b353ca087f39f8da1c29ec1a599e736a1c88",
                  "sha512": "49bf4324ea2e565bbf129f8d10b32523c29c7e103136277825bab280329125e6"}
        assert hashlib.sha256((directory / "compression.bin").read_bytes()).hexdigest() == pinned[kind]
    native.prepare(args.prefix, directory)
    script = native.linker(directory)
    for i, case in enumerate(cases):
        path = directory / f"case-{i}"
        expected = (path / "expected.bin").read_bytes()
        assert (path / "after.bin").read_bytes() == expected, (kind, case.name, "Python mismatch")
        native.execute(args, directory, path, expected, script)
    print(f"PASS {kind}: {len(cases)} cases; Python, GNU bytes, GNU/QEMU and encoded/QEMU", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    parser.add_argument("--only", choices=("sha256", "sha512", "hmac", "extract", "expand", "tls", "length512"))
    args = parser.parse_args()
    build(["Tests.HashCrypto.ProofAudit", "Tests.HashCrypto.Probe"])
    print(run(["lake", "build", "libp2p-asm-hash-probe"], timeout=300), end="", flush=True)
    kinds = [args.only] if args.only else ["sha256", "sha512", "hmac", "extract", "expand", "tls", "length512"]
    for kind in kinds:
        suite(args, kind)


if __name__ == "__main__":
    main()
