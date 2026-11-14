"""Reuse existing fixtures and Lean models; compare every register and data byte."""

import json
from pathlib import Path
import struct
import sys

from support import BIN, ROOT, run


def execute(runner, library, before, expected, regions):
    arguments = [f"{base:x}:{size}:{int(writable)}" for base, size, writable in regions]
    actual = run([runner, library, before, *arguments], binary=True)
    wanted = expected.read_bytes()
    if actual != wanted:
        offset = next((i for i, (a, b) in enumerate(zip(actual, wanted)) if a != b), min(len(actual), len(wanted)))
        raise AssertionError(f"{before.name}: snapshot differs at byte {offset}")


def protocol_suite(group, kind, routine, fixtures, directory, runner):
    path = directory / group / kind
    path.mkdir(parents=True)
    (path / "cases.json").write_text(json.dumps(fixtures))
    run([BIN / "libp2p-asm-x64-probe", "quic" if group == "QuicWire" else "streams", kind, path], timeout=1800)
    for i, fixture in enumerate(fixtures):
        expected = path / f"case-{i}.expected.bin"
        assert (path / f"case-{i}.after.bin").read_bytes() == expected.read_bytes()
        regions = [(0x200000 + 0x10000 * index, len(data),
                    index in (1, 2, 5) if group == "QuicWire" else index != 3)
                   for index, data in enumerate(fixture["regions"])]
        execute(runner, directory / f"{routine}.so", path / f"case-{i}.before.bin", expected, regions)
    print(f"PASS: {group}/{kind}: {len(fixtures)} native/model/reference snapshots and ABI checks", flush=True)


def quic(directory, runner):
    from cases import packet_cases, frame_cases, tp_cases
    from encoding import packet_encodings, frame_encodings, tp_encodings
    from extra import public_packets, public_frames, permissions
    from batch import packet_batches, frame_batches
    from fuzz import cases as fuzz_cases
    suites = [
        ("packet", "quic-packet-parse", packet_cases() + public_packets() + fuzz_cases("packet")),
        ("frame", "quic-frame-parse", frame_cases() + public_frames() + fuzz_cases("frame")),
        ("tp", "quic-transport-parse", tp_cases() + fuzz_cases("tp")),
        ("packet-encode", "quic-packet-encode", packet_encodings()),
        ("frame-encode", "quic-frame-encode", frame_encodings()),
        ("tp-encode", "quic-transport-encode", tp_encodings()),
        ("permission", "quic-frame-permission", permissions()),
        ("packet-batch", "quic-packet-batch", packet_batches()),
        ("frame-batch", "quic-frame-batch", frame_batches()),
    ]
    for kind, routine, fixtures in suites:
        protocol_suite("QuicWire", kind, routine, fixtures, directory, runner)


def stream_suites():
    from cases import receive_cases, consume_cases, peek_cases
    from send_cases import suites as send_suites, permutation_suites
    from ping_cases import suites as ping_suites
    from multistream_cases import cases as negotiation_cases
    from extra_cases import emit_cases, timer_cases, quota_cases, metadata_cases
    from id_cases import cases as id_cases, ordinal_cases
    suites = {"receive": receive_cases(), "consume": consume_cases(), "peek": peek_cases(),
              "negotiate": negotiation_cases(), "neg-emit": emit_cases(), "neg-timer": timer_cases(),
              "ping-quota": quota_cases(), "id": id_cases(), "ordinal": ordinal_cases()}
    suites.update(send_suites())
    suites.update(ping_suites())
    metadata, permutations = metadata_cases(), permutation_suites()
    return {kind: fixtures + metadata.get(kind, []) + permutations.get(kind, [])
            for kind, fixtures in suites.items()}


def streams(directory, runner):
    for kind, fixtures in stream_suites().items():
        for fixture in fixtures:
            capacity = max(0, len(fixture["regions"][1]) - 17)
            length = max(0, len(fixture["regions"][3]) - 17)
            fixture["budget"] = 5000 + 300 * length if kind == "negotiate" else 5000 + 200 * (length + capacity)
        routine = {"negotiate": "multistream-feed", "neg-emit": "multistream-emit",
                   "neg-timer": "multistream-timer", "ping-timer": "ping-timeout"}.get(kind)
        if routine is None:
            routine = kind if kind.startswith("ping-") else f"stream-{kind}"
        protocol_suite("Streams", kind, routine, fixtures, directory, runner)


def hashes(directory, runner):
    from cases import write_case
    from fixtures import all_cases
    routines = {"sha256": "sha256", "sha512": "sha512", "hmac": "hmac-sha256",
                "extract": "hkdf-extract", "expand": "hkdf-expand", "tls": "tls-label"}
    for kind, routine in routines.items():
        path = directory / "HashCrypto" / kind
        path.mkdir(parents=True)
        cases = all_cases(kind)
        for i, case in enumerate(cases):
            write_case(path / f"case-{i}", kind, case, i)
        (path / "count.txt").write_text(str(len(cases)))
        run([BIN / "libp2p-asm-hash-probe", kind, path], timeout=1800)
        for i in range(len(cases)):
            folder = path / f"case-{i}"
            expected = folder / "expected.bin"
            assert (folder / "after.bin").read_bytes() == expected.read_bytes()
            sizes = struct.unpack("<6Q", (folder / "sizes.bin").read_bytes())
            regions = [((index + 1) * 0x100000, size, index in (2, 3, 5))
                       for index, size in enumerate(sizes)]
            execute(runner, directory / f"{routine}.so", folder / "before.bin", expected, regions)
        print(f"PASS: HashCrypto/{kind}: {len(cases)} native/model/Python snapshots and ABI checks", flush=True)


def main():
    group, directory, runner = sys.argv[1:]
    if group not in ("QuicWire", "Streams", "HashCrypto"):
        raise ValueError("Unknown fixture group")
    sys.path.insert(0, str(ROOT / "Tests" / group))
    {"QuicWire": quic, "Streams": streams, "HashCrypto": hashes}[group](Path(directory), Path(runner))


if __name__ == "__main__":
    main()
