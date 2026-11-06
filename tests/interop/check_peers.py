#!/usr/bin/env python3
"""Smoke-test the independent peers against each other, not the ASM implementation."""

import argparse
import itertools
import json
import os
from pathlib import Path
import selectors
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


class Peer:
    def __init__(self, binary, identity, listen, directory, target=None):
        self.log = (directory / f"{binary.name}-{identity}.stderr").open("wb")
        command = [str(binary), "--identity", identity, "--listen", listen,
                   "--count", "3", "--lifetime", "20s"]
        if target:
            command += ["--target", target]
        self.process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=self.log)
        self.buffer = b""
        self.events = []
        self.ready = None
        self.rounds = set()
        self.done = False

    def read(self):
        data = os.read(self.process.stdout.fileno(), 16384)
        if not data:
            raise AssertionError("Peer exited before completing the test")
        self.buffer += data
        if len(self.buffer) > 65536 or len(self.events) > 128:
            raise AssertionError("Peer output exceeded the test bound")
        while b"\n" in self.buffer:
            line, self.buffer = self.buffer.split(b"\n", 1)
            event = json.loads(line)
            self.events.append(event)
            if event["event"] == "error":
                raise AssertionError(f"Peer error: {event.get('reason', 'unspecified')}")
            if event["event"] == "ready":
                self.ready = event
            if event["event"] == "ping":
                self.rounds.add(event["round"])
            if event["event"] == "done":
                self.done = True

    def stop(self):
        if self.process.poll() is None:
            self.process.terminate()

    def finish(self):
        try:
            output, _ = self.process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait(timeout=5)
            raise AssertionError("Peer failed to shut down")
        finally:
            self.log.close()
        if self.process.returncode != 0:
            raise AssertionError("Peer reported an execution failure")
        remaining = self.buffer + output
        self.events += [json.loads(line) for line in remaining.splitlines() if line]
        if not any(event["event"] == "closed" for event in self.events):
            raise AssertionError("Peer did not report graceful shutdown")


def wait(peers, predicate, deadline):
    with selectors.DefaultSelector() as selector:
        for peer in peers:
            selector.register(peer.process.stdout, selectors.EVENT_READ, peer)
        while not predicate():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise AssertionError("Peer interoperability timed out")
            ready = selector.select(remaining)
            for key, _ in ready:
                key.data.read()


def check_pair(listener, dialer, listen_identity, dial_identity, family, out):
    directory = out / f"{listener.name}-{listen_identity}-{dial_identity}-{family}"
    directory.mkdir(parents=True, exist_ok=True)
    address = "/ip4/127.0.0.1/udp/0/quic-v1" if family == 4 else "/ip6/::1/udp/0/quic-v1"
    peers = []
    try:
        server = Peer(listener, listen_identity, address, directory)
        peers.append(server)
        deadline = time.monotonic() + 15
        wait(peers, lambda: server.ready is not None, deadline)
        client = Peer(dialer, dial_identity, address, directory, server.ready["address"])
        peers.append(client)
        wait(peers, lambda: all(peer.ready and peer.done and peer.rounds == {1, 2, 3} for peer in peers), deadline)
        for peer, remote in ((server, client), (client, server)):
            authenticated = [event["peer"] for event in peer.events if event["event"] in ("connected", "ping", "done")]
            if not authenticated or any(value != remote.ready["peer"] for value in authenticated):
                raise AssertionError("Authenticated Peer ID did not match the expected counterparty")
    finally:
        for peer in peers:
            peer.stop()
        failures = []
        for peer in peers:
            try:
                peer.finish()
            except Exception as error:
                failures.append(str(error))
        (directory / "events.json").write_text(json.dumps([peer.events for peer in peers], indent=2) + "\n")
        if failures:
            raise AssertionError("; ".join(failures))
    print(f"PASS peer fixtures: {listener.name} listen/{listen_identity}, {dialer.name} dial/{dial_identity}, IPv{family}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--go", type=Path, default=ROOT / "build/interop/go-peer")
    parser.add_argument("--rust", type=Path, default=ROOT / "build/interop/rust-peer")
    args = parser.parse_args()
    out = ROOT / "build/interop/peer-smoke"
    for (listener, dialer), identities, family in itertools.product(
        ((args.go.resolve(), args.rust.resolve()), (args.rust.resolve(), args.go.resolve())),
        itertools.product(("ed25519", "secp256k1"), repeat=2), (4, 6)
    ):
        check_pair(listener, dialer, *identities, family, out)
    print("PASS: 16 peer-only cases, authenticated QUIC and three Ping rounds in both directions; ASM not tested")


if __name__ == "__main__":
    main()
