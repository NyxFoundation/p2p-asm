"""Independent test-only integer compression and padding; hashlib checks digests."""

import hashlib
import random
import re
import struct

from build import ROOT

INITIAL = {
    32: (0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
         0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19),
    64: (0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
         0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
         0x1f83d9abfb41bd6b, 0x5be0cd19137e2179),
}


def constants(width):
    name = "SHA256" if width == 32 else "SHA512"
    source = (ROOT / f"Libp2pAsm/Spec/Crypto/{name}.lean").read_text()
    table = source.split("def roundConstants", 1)[1].split("#v[", 1)[1].split("]", 1)[0]
    values = tuple(int(value, 16) for value in re.findall(r"0x[0-9a-f]+", table))
    assert len(values) == (64 if width == 32 else 80)
    assert all(0 <= value < 1 << width for value in values)
    return values


def rotate(value, amount, width):
    return ((value >> amount) | (value << (width - amount))) & ((1 << width) - 1)


def sigma(value, amounts, width, small=False):
    first, second, third = amounts
    end = value >> third if small else rotate(value, third, width)
    return rotate(value, first, width) ^ rotate(value, second, width) ^ end


def compress(state, block, width):
    mask = (1 << width) - 1
    step = width // 8
    words = [int.from_bytes(block[i:i + step], "big") for i in range(0, len(block), step)]
    small0, small1 = ((7, 18, 3), (17, 19, 10)) if width == 32 else ((1, 8, 7), (19, 61, 6))
    big0, big1 = ((2, 13, 22), (6, 11, 25)) if width == 32 else ((28, 34, 39), (14, 18, 41))
    table = constants(width)
    for index in range(16, len(table)):
        words.append((words[index - 16] + sigma(words[index - 15], small0, width, True)
                      + words[index - 7] + sigma(words[index - 2], small1, width, True)) & mask)
    initial = tuple(word & mask for word in state)
    a, b, c, d, e, f, g, h = initial
    for constant, word in zip(table, words, strict=True):
        t1 = (h + sigma(e, big1, width) + ((e & f) ^ (~e & g)) + constant + word) & mask
        t2 = (sigma(a, big0, width) + ((a & b) ^ (a & c) ^ (b & c))) & mask
        a, b, c, d, e, f, g, h = (t1 + t2) & mask, a, b, c, (d + t1) & mask, e, f, g
    return tuple((x + y) & mask for x, y in zip(initial, (a, b, c, d, e, f, g, h), strict=True))


def padded(message, width):
    size, length_size = 2 * width, width // 4
    zeros = (-len(message) - 1 - length_size) % size
    return message + b"\x80" + bytes(zeros) + (8 * len(message)).to_bytes(length_size, "big")


def fixtures(width):
    rng = random.Random(0x5a2000 + width)
    size = 2 * width
    cases = [(tuple(rng.getrandbits(64) for _ in range(8)), rng.randbytes(size))
             for _ in range(24)]
    cases += [(tuple([value] * 8), bytes([byte]) * size)
              for value, byte in [(0, 0), ((1 << 64) - 1, 255), (1 << 63, 128), (1, 1)]]
    messages = [b"", b"a", b"abc"] + [rng.randbytes(n) for n in
                (55, 56, 63, 64, 65, 111, 112, 127, 128, 129, 255, 256, 257, 1024)]
    for message in messages:
        state = INITIAL[width]
        data = padded(message, width)
        for offset in range(0, len(data), size):
            block = data[offset:offset + size]
            cases.append((state, block))
            state = compress(state, block, width)
        digest = b"".join(word.to_bytes(width // 8, "big") for word in state)
        oracle = hashlib.sha256 if width == 32 else hashlib.sha512
        assert digest == oracle(message).digest(), "independent padding/compression differs from hashlib"
    return cases, len(messages)


def write_cases(directory, cases):
    (directory / "cases.bin").write_bytes(b"".join(struct.pack("<8Q", *s) + b for s, b in cases))
