#!/usr/bin/env python3
"""Run scalar x86-64 emission, instruction, ABI, codec, and snapshot tests on Linux."""

import argparse
import ctypes
import importlib.util
import platform
import random
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

from support import BIN, GENERATOR, MASK, ROOT, Registers, bind, compile_source, generate, run


def references():
    sys.path.insert(0, str(ROOT / "tests/native"))
    import isa
    spec = importlib.util.spec_from_file_location("rv_codecs", ROOT / "tests/native/codecs.py")
    codecs = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(codecs)
    sys.path.pop(0)
    return isa, codecs


def cli(directory):
    for args in (["--target", "x86", "asm", "add"], ["--target", "x86_64", "hex", "add"],
                 ["--target", "x86_64", "asm", "unknown"], ["binary", "add"]):
        result = subprocess.run([str(GENERATOR), *args], capture_output=True, timeout=30)
        assert result.returncode == 2 and result.stderr and not result.stdout, args
    for format in ("asm", "hex"):
        assert run([GENERATOR, format, "add"]) == run([GENERATOR, "--target", "rv64", format, "add"])
    routines = run([GENERATOR, "--help"]).split("Routines: ", 1)[1]
    names = [name.strip() for name in routines.replace("Protocol leaves: ", "").replace(".", ",").split(",")]
    for name in filter(None, names):
        generate(directory, name)
    print(f"PASS: should assemble and link all {len(list(filter(None, names)))} public routines as PIC", flush=True)
    run(["gcc", "-Wall", "-Wextra", "-Werror", "-fPIE", "-pie", "-Iinclude",
         "Examples/X64.c", directory / "quic-decode.S", "-o", directory / "example"])
    run([directory / "example"])
    print("PASS: should run the documented C consumer and retain the default RV64 target", flush=True)


def arithmetic(directory):
    for name in ("add", "min"):
        function = bind(directory / f"{name}.so")
        for a in (0, 1, (1 << 63) - 1, 1 << 63, MASK):
            for b in (0, 1, (1 << 63) - 1, 1 << 63, MASK):
                registers = Registers()
                registers[8], registers[10], registers[11] = 0x11223344, a, b
                assert function(registers) == 0
                expected = (a + b) & MASK if name == "add" else min(a, b)
                assert registers[10] == expected
                assert registers[11] == b and registers[8] == 0x11223344
    print("PASS: should execute arithmetic through the System V C ABI", flush=True)


def isa_case(function, name, a, b, reference):
    data = (ctypes.c_uint64 * 2)(b ^ MASK if name in ("sb", "sd") else b, reference.GUARD)
    registers = Registers()
    registers[8], registers[11] = reference.CANARY, b
    registers[10] = ctypes.addressof(data) if name in ("lbu", "ld", "sb", "sd") else (
        0x10001 if name == "jalr" else a)
    assert function(registers) == 0, (name, a, b)
    actual = struct.pack("<3Q", *registers[10:13]) + bytes(data)
    model = bytes.fromhex(run([BIN / "libp2p-asm-isa-probe", "eval", name, str(a), str(b)]))
    assert actual == model, (name, a, b, actual.hex(), model.hex())
    assert registers[10] == reference.OPERATIONS[name](a, b) & MASK
    assert registers[0] == 0 and registers[8] == reference.CANARY


def instructions(directory, reference):
    values = (0, 1, 63, 64, 65, (1 << 63) - 1, 1 << 63, MASK)
    rng = random.Random(64)
    cases = [(a, b) for a in values for b in values]
    cases += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(8)]
    folder = directory / "isa"
    folder.mkdir()
    for name in reference.OPERATIONS:
        function = bind(generate(folder, name, BIN / "libp2p-asm-isa-probe"))
        for a, b in cases:
            isa_case(function, name, a, b, reference)
    print(f"PASS: should match all 33 ISA operations, RV64 semantics and Python: {33 * len(cases)} cases", flush=True)


def control_flow(directory):
    folder = directory / "control"
    folder.mkdir()
    run([BIN / "libp2p-asm-x64-probe", "emit-fixtures", folder])
    functions = {path.stem: bind(compile_source(folder, path.stem)) for path in folder.glob("*.S")}
    registers = Registers(*([MASK] * 32))
    registers[1] = 0
    assert functions["zero"](registers) == 0 and registers[0] == 0 and registers[10] == 0
    for sentinel in (0, 0x80000, 0x80001, MASK - 1):
        registers = Registers()
        registers[1], registers[10] = sentinel, 41
        assert functions["nested"](registers) == 0 and registers[10] == 42
        assert registers[1] == sentinel
    for address, status in ((0x10005, 0), (0x10002, 1), (0x1000C, 1), (MASK, 1), (1 << 63, 1)):
        registers = Registers()
        registers[10] = address
        assert functions["indirect"](registers) == status
        assert registers[10] == 0x10004
        assert registers[11] == (42 if status == 0 else 0)
    registers = Registers()
    registers[1] = 0x10004
    assert functions["indirect"](registers) == 1
    assert functions["fallthrough"](Registers()) == 1
    assert functions["endjump"](Registers()) == 1
    aliasing(functions)
    print("PASS: should preserve x0, aliases, signed offsets, nested links and reject invalid PCs", flush=True)


def aliasing(functions):
    for a, b in ((MASK, 3), (1 << 63, 65), (0, 0), (17, 8)):
        registers = Registers()
        registers[10], registers[11] = a, b
        shifted = (a << ((a - b) & 63)) & MASK
        high = (a * shifted) >> 64
        assert functions["alias"](registers) == 0
        assert registers[10] == high
        assert registers[11] == (high // shifted if shifted else MASK)
    data = (ctypes.c_uint64 * 4)(0xFEDCBA9876543210, 0, 0, MASK)
    registers = Registers()
    registers[10], registers[11] = ctypes.addressof(data) + 8, ctypes.addressof(data) + 24
    assert functions["offset"](registers) == 0
    assert list(data) == [0xFEDCBA9876543210, 0, 0xFEDCBA9876543210, MASK]
    assert registers[10:12] == [0xFEDCBA9876543210, 0xFE]


def codec_case(function, name, argument, limit, data, offset=0):
    buffer = (ctypes.c_uint8 * max(1, len(data)))(*data)
    registers = Registers()
    if name.endswith("encode"):
        registers[10:13] = [argument, ctypes.addressof(buffer) + offset, limit]
        input_text = str(argument)
    else:
        registers[10:13] = [ctypes.addressof(buffer), limit, 0]
        input_text = data.hex()
    assert function(registers) == 0
    actual = struct.pack("<3Q", *registers[10:13]) + bytes(buffer)[:len(data)]
    model = bytes.fromhex(run([GENERATOR, "eval-codec", name, input_text, str(limit)]))
    assert actual == model, (name, input_text, limit)


def codecs(directory, reference):
    values = [0, 1, 63, 64, 127, 128, 16383, 16384, (1 << 30) - 1, 1 << 30,
              (1 << 56) - 1, 1 << 56, (1 << 62) - 1, 1 << 62, (1 << 63) - 1, 1 << 63, MASK]
    count = 0
    for kind in ("quic", "uvarint"):
        encode = bind(directory / f"{kind}-encode.so")
        decode = bind(directory / f"{kind}-decode.so")
        for value in values:
            for capacity in (0, 1, 2, 3, 4, 7, 8, 9):
                codec_case(encode, f"{kind}-encode", value, capacity, b"\xAA" * (capacity + 2), 1)
                count += 1
            status, encoded = reference.encode_reference(kind, value)
            if status:
                continue
            for length in range(len(encoded) + 1):
                codec_case(decode, f"{kind}-decode", 0, length, encoded)
                count += 1
        for data in (b"", b"\x80\x00", b"\x81\x00", b"\x80" * 9, b"\xFF" * 10):
            codec_case(decode, f"{kind}-decode", 0, len(data), data)
            count += 1
    print(f"PASS: should match varint results, rejection paths and guard bytes: {count} cases", flush=True)


def snapshots(directory):
    runner = directory / "runner"
    run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIE", "-pie", "-Iinclude",
         "Tests/X64/Runner.c", "-ldl", "-o", runner])
    for group in ("QuicWire", "Streams", "HashCrypto"):
        subprocess.run([sys.executable, str(ROOT / "Tests/X64/snapshots.py"), group,
                        str(directory), str(runner)], cwd=ROOT, check=True, timeout=1800)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-snapshots", action="store_true")
    args = parser.parse_args()
    if sys.platform != "linux" or platform.machine() not in ("x86_64", "AMD64"):
        parser.error("native tests require Linux x86-64")
    run(["lake", "build", "libp2p-asm-codegen", "libp2p-asm-isa-probe",
         "libp2p-asm-x64-probe", "libp2p-asm-hash-probe"])
    isa, codec = references()
    with tempfile.TemporaryDirectory(prefix="p2p-x64-") as temporary:
        directory = Path(temporary)
        cli(directory)
        arithmetic(directory)
        instructions(directory, isa)
        control_flow(directory)
        codecs(directory, codec)
        if not args.skip_snapshots:
            snapshots(directory)


if __name__ == "__main__":
    main()
