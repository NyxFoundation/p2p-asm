#!/usr/bin/env python3
"""Exercise both varint codecs as emitted machine code, including failure paths."""

import argparse
import os
import random
import struct

from check import ROOT, build_program, run, run_probe
from probe import source


def encode_reference(kind, value):
    maximum = 1 << (62 if kind == "quic" else 63)
    if value >= maximum:
        return 2, b""
    if kind == "quic":
        for tag, width in enumerate((1, 2, 4, 8)):
            if value < (1 << (8 * width - 2)):
                return 0, (value | (tag << (8 * width - 2))).to_bytes(width, "big")
    output = bytearray()
    while True:
        low = value & 127
        value >>= 7
        output.append(low | (128 if value else 0))
        if not value:
            return 0, bytes(output)


def decode_reference(kind, data):
    if not data:
        return 1, 0, 0
    if kind == "quic":
        width = 1 << (data[0] >> 6)
        if len(data) < width:
            return 1, 0, 0
        value = int.from_bytes(data[:width], "big") & ((1 << (8 * width - 2)) - 1)
        return 0, value, width
    value = 0
    for index in range(9):
        if index == len(data):
            return 1, 0, 0
        byte = data[index]
        value |= (byte & 127) << (7 * index)
        if byte < 128:
            return (3, 0, 0) if index and byte == 0 else (0, value, index + 1)
    return 2, 0, 0


def check_encoder(args, kind, value, capacity, out, expected):
    status, encoded = encode_reference(kind, value)
    if not status and len(encoded) > capacity:
        status, encoded = 1, b""
    data = bytes([0xAA]) * (capacity + 2)
    arguments = f"  li a0, {value}\n  la a1, payload\n  addi a1, a1, 1\n  li a2, {capacity}"
    actual = run_probe(args, out, source(arguments, data), expected)
    modified = b"\xAA" + encoded + bytes([0xAA]) * (capacity + 1 - len(encoded))
    reference = struct.pack("<QQQ", status, len(encoded), 0) + modified
    generator = ROOT / ".lake/build/bin/libp2p-asm-codegen"
    model = bytes.fromhex(run([str(generator), "eval-codec", f"{kind}-encode",
                               str(value), str(capacity)]).strip())
    if actual != reference or model != reference:
        raise AssertionError(f"Encoder mismatch: {kind}, value={value}, capacity={capacity}")


def check_decoder(args, kind, data, length, out, expected):
    arguments = f"  la a0, payload\n  li a1, {length}\n  li a2, 0"
    actual = run_probe(args, out, source(arguments, data), expected)
    reference = struct.pack("<QQQ", *decode_reference(kind, data[:length])) + data
    generator = ROOT / ".lake/build/bin/libp2p-asm-codegen"
    model = bytes.fromhex(run([str(generator), "eval-codec", f"{kind}-decode",
                               data.hex(), str(length)]).strip())
    if actual != reference or model != reference:
        raise AssertionError(f"Decoder mismatch: {kind}, bytes={data.hex()}, length={length}")


def run_kind(args, kind, values):
    enc_out, enc_expected = build_program(args, f"{kind}-encode")
    dec_out, dec_expected = build_program(args, f"{kind}-decode")
    count = 0
    for value in values:
        for capacity in (0, 1, 2, 3, 4, 7, 8, 9):
            check_encoder(args, kind, value, capacity, enc_out, enc_expected)
            count += 1
        status, encoded = encode_reference(kind, value)
        if status:
            continue
        for length in range(len(encoded)):
            check_decoder(args, kind, encoded, length, dec_out, dec_expected)
            count += 1
        check_decoder(args, kind, encoded + b"\xAA\xBB", len(encoded) + 2, dec_out, dec_expected)
        count += 1
    malformed = [b"", b"\x40\x00", b"\x80\x00", b"\x81\x00",
                 b"\x80" * 9, b"\xFF" * 10, b"\xC0" + b"\x00" * 7]
    for data in malformed:
        check_decoder(args, kind, data, len(data), dec_out, dec_expected)
        count += 1
    print(f"PASS: should match {kind} ASM/model/reference and guard bytes: {count} QEMU cases")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", default=os.environ.get("QEMU_RISCV64", "qemu-riscv64"))
    parser.add_argument("--prefix", default="riscv64-unknown-elf-")
    args = parser.parse_args()
    values = [0, 1, 63, 64, 127, 128, 255, 256, 16383, 16384,
              (1 << 30) - 1, 1 << 30, (1 << 56) - 1, 1 << 56,
              (1 << 62) - 1, 1 << 62, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]
    rng = random.Random(9001)
    values += [rng.getrandbits(64) for _ in range(32)]
    for kind in ("quic", "uvarint"):
        run_kind(args, kind, values)


if __name__ == "__main__":
    main()
