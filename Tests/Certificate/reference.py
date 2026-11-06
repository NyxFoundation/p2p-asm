"""Independent structural X.509/libp2p profile oracle, not authentication."""
from dataclasses import dataclass
from datetime import datetime
import importlib.util
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "certificate_algorithm_patterns", ROOT/"Tests/CertificateAlgorithms/cases.py")
patterns = importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name] = patterns
spec.loader.exec_module(patterns)
ALGORITHMS = {k: patterns.known(k) for k in ("signature", "public")}
LIBP2P = bytes.fromhex("2b0601040183a25a0101")
MASK = 2**64-1


class Invalid(ValueError):
    def __init__(self, status=6):
        self.status = status
        super().__init__(status)


def need(ok, status=6):
    if not ok:
        raise Invalid(status)


@dataclass(frozen=True)
class Node:
    tag: int
    start: int
    content: int
    end: int

    @property
    def view(self):
        return self.content, self.end-self.content

    @property
    def raw(self):
        return self.start, self.end-self.start


class Cursor:
    def __init__(self, data, start=0, end=None):
        self.data, self.at = data, start
        self.end = len(data) if end is None else end

    def get(self, tag=None):
        start = self.at
        need(start < self.end, 1)
        t = self.data[start]
        need(t % 32 != 31 and (t >= 64 or t % 32 != 0))
        need(start+1 < self.end, 1)
        n = self.data[start+1]
        pos = start+2
        if n >= 128:
            need(n not in (128, 255) and n-128 <= 8)
            count = n-128
            need(pos+count <= self.end, 1)
            need(self.data[pos] != 0)
            n = int.from_bytes(self.data[pos:pos+count], "big")
            need(n >= 128)
            pos += count
        need(pos+n <= self.end, 1)
        need(tag is None or tag == t)
        self.at = pos+n
        return Node(t, start, pos, pos+n)

    def done(self):
        need(self.at == self.end)

    def empty(self):
        return self.at == self.end


def child(data, node):
    return Cursor(data, node.content, node.end)


def payload(data, node):
    return data[node.content:node.end]


def oid(data, node):
    raw = payload(data, node)
    need(node.tag == 6 and raw)
    first = True
    for b in raw:
        need(not (first and b == 128))
        first = b < 128
    need(first)
    return raw


def integer(data, node):
    raw = payload(data, node)
    need(node.tag == 2 and raw and raw[0] < 128)
    if len(raw) > 1 and raw[0] == 0:
        need(raw[1] >= 128)
        return node.content+1, len(raw)-1
    return node.view


def bits(data, node):
    raw = payload(data, node)
    need(node.tag == 3 and raw and raw[0] == 0)
    return node.content+1, len(raw)-1


def boolean(data, node):
    raw = payload(data, node)
    need(node.tag == 1 and raw in (b"\x00", b"\xff"))
    return raw == b"\xff"


def algorithm(data, node, kind):
    value = ALGORITHMS[kind].get(data[node.start:node.end], 0)
    need(value, 8)
    return value


def string_value(data, node):
    raw = payload(data, node)
    try:
        if node.tag == 12:
            raw.decode("utf-8", errors="strict")
        elif node.tag == 18:
            need(all(b == 32 or 48 <= b <= 57 for b in raw))
        elif node.tag == 19:
            allowed = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 '()+,-./:=?"
            need(all(b in allowed for b in raw))
        elif node.tag == 22:
            need(all(b < 128 for b in raw))
        elif node.tag in (28, 30):
            width = 4 if node.tag == 28 else 2
            need(len(raw) % width == 0)
            for i in range(0, len(raw), width):
                n = int.from_bytes(raw[i:i+width], "big")
                need(n <= 0x10ffff and not 0xd800 <= n <= 0xdfff)
    except UnicodeDecodeError as e:
        raise Invalid() from e


def name(data, node):
    outer = child(data, node)
    while not outer.empty():
        group = child(data, outer.get(49))
        need(not group.empty())
        previous = None
        while not group.empty():
            attr = group.get(48)
            fields = child(data, attr)
            oid(data, fields.get(6))
            value = fields.get()
            fields.done()
            string_value(data, value)
            raw = data[attr.start:attr.end]
            need(previous is None or previous <= raw)
            previous = raw


def calendar(data, node):
    raw = payload(data, node)
    width = 2 if node.tag == 23 else 4
    need(node.tag in (23, 24))
    need(re.fullmatch(rb"[0-9]{"+str(width+10).encode()+rb"}Z", raw))
    year = int(raw[:width])
    if width == 2:
        year += 2000 if year < 50 else 1900
    try:
        fields = [int(raw[i:i+2]) for i in range(width, width+10, 2)]
        delta = datetime(year, *fields)-datetime(1970, 1, 1)
        return delta.days*86400+delta.seconds
    except ValueError as e:
        raise Invalid() from e


def validity(data, node):
    c = child(data, node)
    before, after = c.get(), c.get()
    c.done()
    first, last = calendar(data, before), calendar(data, after)
    need(first <= last)
    return first & MASK, last & MASK


def public_key(data, node):
    c = child(data, node)
    kind = algorithm(data, c.get(48), "public")
    bit_node = c.get(3)
    c.done()
    off, size = bits(data, bit_node)
    modulus, exponent = (0, 0), (0, 0)
    if kind == 3:
        c = Cursor(data, off, off+size)
        seq = c.get(48)
        c.done()
        c = child(data, seq)
        n, e = c.get(2), c.get(2)
        c.done()
        modulus, exponent = integer(data, n), integer(data, e)
    elif kind == 1:
        need(size == 32)
    else:
        need(size == 65 and data[off] == 4)
    return kind, off, size, *modulus, *exponent


def key_usage(data, node):
    c = child(data, node)
    raw = payload(data, c.get(3))
    c.done()
    need(raw and raw[0] <= 7 and len(raw) <= 3)
    unused, payload_bytes = raw[0], raw[1:]
    if not payload_bytes:
        need(unused == 0)
        return False
    last = payload_bytes[-1]
    need(last and last % 2**unused == 0 and (last//2**unused) % 2 == 1)
    need(len(payload_bytes) != 2 or (unused == 7 and last == 128))
    return payload_bytes[0] >= 128


def constraints(data, node):
    c = child(data, node)
    seq = c.get(48)
    c.done()
    c = child(data, seq)
    if c.empty():
        return
    ca = boolean(data, c.get(1))
    if not c.empty():
        need(ca)
        integer(data, c.get(2))
        c.done()


def usage(data, node):
    c = child(data, node)
    seq = c.get(48)
    c.done()
    c = child(data, seq)
    need(not c.empty())
    result = 0
    flags = {bytes.fromhex("551d2500"): 3, bytes.fromhex("2b06010505070301"): 1,
             bytes.fromhex("2b06010505070302"): 2}
    while not c.empty():
        result |= flags.get(oid(data, c.get(6)), 0)
    return result


def extensions(data, node):
    c = child(data, node)
    seq = c.get(48)
    c.done()
    c = child(data, seq)
    need(not c.empty(), 11)
    seen, identity, ku, eku = set(), None, True, 3
    while not c.empty():
        e = child(data, c.get(48))
        identifier = oid(data, e.get(6))
        need(identifier not in seen, 9)
        seen.add(identifier)
        value = e.get()
        critical = False
        if value.tag == 1:
            critical = boolean(data, value)
            value = e.get(4)
        need(value.tag == 4)
        e.done()
        if identifier == LIBP2P:
            e = child(data, value)
            seq = e.get(48)
            e.done()
            e = child(data, seq)
            key, signature = e.get(4), e.get(4)
            e.done()
            identity = (*key.view, *signature.view)
        elif identifier == bytes.fromhex("551d0f"):
            ku = key_usage(data, value)
        elif identifier == bytes.fromhex("551d13"):
            constraints(data, value)
        elif identifier == bytes.fromhex("551d25"):
            eku = usage(data, value)
        else:
            need(not critical, 10)
    need(identity is not None, 11)
    return *identity, eku if ku else 0


def certificate(data):
    outer = Cursor(data)
    root = outer.get(48)
    outer.done()
    root_fields = child(data, root)
    tbs = root_fields.get(48)
    c = child(data, tbs)
    version = child(data, c.get(160))
    v = version.get(2)
    version.done()
    need(payload(data, v) == b"\x02")
    serial = c.get(2)
    integer(data, serial)
    need(serial.view[1] <= 20)
    sigkind = algorithm(data, c.get(48), "signature")
    name(data, c.get(48))
    times = validity(data, c.get(48))
    name(data, c.get(48))
    spki = c.get(48)
    public = public_key(data, spki)
    need(public[0] == (sigkind if sigkind < 3 else 3), 8)
    ext = c.get(163)
    c.done()
    identity = extensions(data, ext)
    need(algorithm(data, root_fields.get(48), "signature") == sigkind, 8)
    signature = root_fields.get(3)
    root_fields.done()
    return (*tbs.raw, *spki.raw, *public, sigkind, *bits(data, signature), *times, *identity)


def outcome(data):
    try:
        return 0, certificate(data)
    except Invalid as e:
        return e.status, ()
