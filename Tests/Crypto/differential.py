"""Optional test-only comparison; official published vectors live in the Lean suite.

Run after `lake build Tests/Crypto/Differential.lean`:
    python3 Tests/Crypto/differential.py
Uses only Python's standard library; never imported by production or Lean specs.
"""

import hashlib
import hmac
from pathlib import Path
import subprocess


def fixture(length: int, seed: int) -> bytes:
    return bytes((i * 37 + seed * 17 + i // 7) % 256 for i in range(length))


def expand(prk: bytes, info: bytes, length: int) -> bytes:
    previous = b""
    output = bytearray()
    for counter in range(1, (length + 31) // 32 + 1):
        previous = hmac.digest(prk, previous + info + bytes([counter]), "sha256")
        output.extend(previous)
    return bytes(output[:length])


def expected_rows() -> dict[str, bytes]:
    expected = {}
    for length in (*range(261), 511, 512, 513, 1024, 4097):
        for name in ("sha256", "sha512"):
            expected[f"{name}:{length}"] = hashlib.new(name, fixture(length, 1)).digest()
    for key_length in (0, 1, 31, 32, 63, 64, 65, 127, 128, 131):
        for message_length in (0, 1, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129):
            expected[f"hmac:{key_length}:{message_length}"] = hmac.digest(
                fixture(key_length, 2), fixture(message_length, 3), "sha256"
            )
    for prk_length in (32, 33, 64, 65, 131):
        for length in (0, 1, 31, 32, 33, 63, 64, 65, 82, 8160):
            expected[f"expand:{prk_length}:{length}"] = expand(
                fixture(prk_length, 4), fixture(17, 5), length
            )
    for salt_length in (0, 1, 32, 64, 65, 131):
        expected[f"extract:{salt_length}"] = hmac.digest(
            fixture(salt_length, 6), fixture(257, 7), "sha256"
        )
    expected["extract-default"] = hmac.digest(bytes(32), fixture(257, 7), "sha256")
    return expected


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "Tests/Crypto/Differential.lean"],
        cwd=root, check=True, text=True, capture_output=True, timeout=180,
    )
    expected = expected_rows()
    seen = set()
    for row in result.stdout.splitlines():
        label, digest = row.rsplit(":", 1)
        if label not in expected or label in seen:
            raise AssertionError(f"Unexpected or duplicate case: {label}")
        if bytes.fromhex(digest) != expected[label]:
            raise AssertionError(f"Differential mismatch: {label}")
        seen.add(label)
    if seen != expected.keys():
        raise AssertionError(f"Missing differential cases: {expected.keys() - seen}")
    print(f"PASS: {len(seen)} supplemental hashlib/hmac differential cases")


if __name__ == "__main__":
    main()
