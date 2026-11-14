"""Shared native build and System V ABI checks."""

import ctypes
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BIN = ROOT / ".lake/build/bin"
GENERATOR = BIN / "libp2p-asm-codegen"
MASK = (1 << 64) - 1
Registers = ctypes.c_uint64 * 32


def run(command, *, binary=False, timeout=300):
    result = subprocess.run([str(arg) for arg in command], cwd=ROOT, check=True,
                            capture_output=True, text=not binary, timeout=timeout)
    return result.stdout


def compile_source(directory, name):
    library = directory / f"{name}.so"
    run(["gcc", "-shared", "-fPIC", "-Wl,-z,text", "-Wl,-z,noexecstack",
         directory / f"{name}.S", ROOT / "Tests/X64/Abi.S", "-o", library])
    return library


def generate(directory, name, generator=GENERATOR):
    source = directory / f"{name}.S"
    source.write_text(run([generator, "--target", "x86_64", "asm", name]))
    return compile_source(directory, name)


def bind(library):
    loaded = ctypes.CDLL(str(library))
    checked = loaded.checked_call
    checked.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.c_void_p]
    checked.restype = ctypes.c_uint64
    entry = ctypes.cast(loaded.protocol_entry, ctypes.c_void_p)
    return lambda registers: checked(registers, entry)
