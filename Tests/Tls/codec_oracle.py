"""Independent Python parser, field offsets and strict libp2p validation."""
import struct

HRR = bytes.fromhex('cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c')


class Error(Exception):
    def __init__(self, code): self.code = code


def require(ok, status=2):
    if not ok: raise Error(status)


class Cursor:
    def __init__(self, data, pos=0, end=None):
        self.data, self.pos, self.end = data, pos, len(data) if end is None else end

    def take(self, n):
        require(0 <= n <= self.end-self.pos)
        start = self.pos
        self.pos += n
        return start, n

    def uint(self, width):
        start, size = self.take(width)
        return int.from_bytes(self.data[start:start+size], 'big')

    def vector(self, width, minimum=0):
        size = self.uint(width)
        require(size >= minimum)
        return self.take(size)

    def sub(self, span): return Cursor(self.data, span[0], sum(span))
    def done(self): require(self.pos == self.end)


def exts(c):
    found = {}
    while c.pos < c.end:
        kind = c.uint(2)
        span = c.vector(2)
        require(kind not in found, 6)
        found[kind] = span
    return found


def uints(c, span):
    require(span[1] > 0 and span[1] % 2 == 0)
    child = c.sub(span)
    return [child.uint(2) for _ in range(span[1]//2)]


def share(c, w, seen):
    group, span = c.uint(2), c.vector(2, 1)
    require(group != 29 or span[1] == 32)
    require(group != 23 or (span[1] == 65 and c.data[span[0]] == 4))
    require(group not in seen, 6)
    seen.add(group)
    if group in (29, 23): w[56 if group == 29 else 58:58 if group == 29 else 60] = span
    w[11] += 1
    if w[0] == 2: w[54] = group


def extension(c, w, kind, span):
    d = c.sub(span)
    if kind == 43:
        s = d.vector(1, 2) if w[0] == 1 else d.take(2)
        d.done()
        values = uints(c, s)
        require(w[0] != 2 or values == [0x0304], 7)
        w[22:24], w[62] = s, int(0x0304 in values)
    elif kind in (10, 13, 50):
        s = d.vector(2, 2)
        d.done()
        values = uints(c, s)
        slot = {10: 24, 13: 28, 50: 30}[kind]
        w[slot:slot+2] = s
        if kind == 10:
            w[61] = int(29 in values) + 2*int(23 in values)
        if kind == 13:
            w[60] = sum(bit for n, bit in [(0x0403, 1), (0x0804, 2), (0x0401, 4), (0x0807, 8)] if n in values)
    elif kind == 51:
        w[26:28] = span
        if w[2]: w[54] = d.uint(2)
        elif w[0] == 2: share(d, w, set())
        else:
            inner = d.sub(d.vector(2))
            seen = set()
            while inner.pos < inner.end: share(inner, w, seen)
        d.done()
    elif kind == 16:
        w[32:34] = span
        names = d.sub(d.vector(2, 2))
        d.done()
        count = 0
        while names.pos < names.end:
            start, size = names.vector(1, 1)
            w[63] += int(c.data[start:start+size] == b'libp2p')
            count += 1
        require(w[0] != 8 or count == 1)
    elif kind == 57: w[34:36] = span
    elif kind == 44:
        w[36:38] = d.vector(2, 1)
        d.done()


def context(w,kind):
    if w[0] == 2: require(kind in ([43, 51, 44] if w[2] else [43, 51]), 3)
    if kind in (43, 51): require(w[0] in (1, 2))
    if kind == 44: require(w[0] == 1 or (w[0] == 2 and w[2]))
    if kind in (13, 50): require(w[0] in (1, 13))
    if kind in (16, 57, 10): require(w[0] in (1, 8))
    if kind == 42: require(w[0] in (1,4))


def interpret(c, w, span):
    w[20:22] = span
    for kind, data in exts(c.sub(span)).items():
        context(w,kind)
        if kind == 0 and w[0] == 1: w[55] = 1
        extension(c, w, kind, data)


def hello(c, w):
    w[4] = c.uint(2)
    require(w[4] == 0x0303, 7)
    w[12:14] = c.take(32)
    w[2] = int(w[0] == 2 and c.data[w[12]:w[12]+32] == HRR)
    w[14:16] = c.vector(1)
    require(w[15] <= 32, 7)
    if w[0] == 1:
        w[16:18] = c.vector(2, 2)
        w[5] = 0x1301 if 0x1301 in uints(c, w[16:18]) else 0
        w[18:20] = c.vector(1, 1)
        require(c.data[w[18]:w[18]+w[19]] == b'\0', 7)
    else:
        w[5], w[6] = c.uint(2), c.uint(1)
        require(w[5] == 0x1301 and w[6] == 0, 7)
    span = c.vector(2)
    c.done()
    interpret(c, w, span)


def message(c, w):
    kind = w[0]
    if kind in (1, 2): hello(c, w)
    elif kind in (8, 13):
        if kind == 13: w[38:40] = c.vector(1)
        span = c.vector(2)
        c.done()
        interpret(c, w, span)
    elif kind == 11:
        w[38:40], w[40:42] = c.vector(1), c.vector(3)
        c.done()
        entries = c.sub(w[40:42])
        while entries.pos < entries.end:
            data, extensions = entries.vector(3, 1), entries.vector(2)
            for k in exts(c.sub(extensions)): context(w,k)
            if w[10] == 0: w[42:44], w[44:46] = data, extensions
            w[10] += 1
    elif kind == 15:
        w[7], w[46:48] = c.uint(2), c.vector(2, 1)
        c.done()
        require(w[7] in (0x0403, 0x0804, 0x0807), 7)
    elif kind == 20:
        w[48:50] = c.take(32)
        c.done()
    elif kind == 4:
        w[8], w[9] = c.uint(4), c.uint(4)
        require(w[8] <= 604800, 7)
        w[50:52], w[52:54], w[20:22] = c.vector(1), c.vector(2, 1), c.vector(2)
        c.done()
        for k, data in exts(c.sub(w[20:22])).items():
            context(w,k)
            require(k != 42 or data[1] == 4)
    else: raise Error(3)


def profile(w):
    kind = w[0]
    if kind == 1:
        require(w[5] == 0x1301 and w[62] == 1 and w[61] != 0 and w[60] & 11 != 0
                and w[63] > 0 and w[34] != 0 and w[26] != 0, 7)
        require(not w[57] or w[61] & 1 != 0, 7)
        require(not w[59] or w[61] & 2 != 0, 7)
    if kind == 2:
        require(w[62] == 1, 7)
        if w[2]:
            require(w[26] or w[36], 7)
            require(not w[26] or w[54] in (23, 29), 7)
        else: require(w[11] == 1 and w[54] in (23, 29), 7)
    if kind == 8: require(w[63] == 1 and w[34] != 0, 7)
    if kind == 13: require(w[39] == 0 and w[60] & 11 != 0, 7)
    if kind == 11: require(w[39] == 0 and w[10] == 1, 7)


def decode(data, limit=2**24-1, strict=True):
    require(len(data) >= 4, 1)
    c = Cursor(data)
    kind, size = c.uint(1), c.uint(3)
    require(size <= limit, 9)
    require(size <= len(data)-4, 1)
    c.end = size+4
    w = [0]*64
    w[0:2] = [kind, c.end]
    w[3] = {1: 8, 2: 3, 8: 9, 11: 5, 15: 5, 13: 1, 4: 1}.get(kind, 0)
    message(c, w)
    if strict: profile(w)
    return struct.pack('<64Q', *w)
