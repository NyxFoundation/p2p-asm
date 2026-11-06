"""Independent byte-oriented RFC 9000 oracle. No production imports."""
from dataclasses import dataclass

MAX = (1 << 62) - 1


class WireError(Exception):
    def __init__(self, code, offset):
        self.code, self.offset = code, offset


@dataclass
class Reader:
    data: bytes
    pos: int = 0

    def take(self, count):
        if count > len(self.data) - self.pos:
            raise WireError(1, self.pos)
        start = self.pos
        self.pos += count
        return start, count

    def byte(self):
        start, _ = self.take(1)
        return self.data[start]

    def var(self):
        if self.pos == len(self.data):
            raise WireError(1, self.pos)
        size = 1 << (self.data[self.pos] >> 6)
        start, _ = self.take(size)
        return int.from_bytes(self.data[start:self.pos], 'big') & ((1 << (8*size-2))-1)

    def require(self, condition, code=3):
        if not condition:
            raise WireError(code, self.pos)


def var(value, width=None):
    assert 0 <= value <= MAX
    size = width or next(w for w in (1, 2, 4, 8) if value < 1 << (w*8-2))
    return (value | ((size.bit_length()-1) << (size*8-2))).to_bytes(size, 'big')


def packet(data, cid=0, bound=0):
    r, out = Reader(data), [0]*16
    first = r.byte()
    out[2] = first
    if first & 0x80 == 0:
        r.require(cid <= 20, 10)
        r.require(first & 0x40, 2)
        out[4:6] = r.take(cid)
        out[10], out[11] = r.pos, len(data)-r.pos
        r.require(out[11] > 0, 1)
        out[0] = len(data)
        return out
    start, _ = r.take(4)
    version = int.from_bytes(data[start:r.pos], 'big')
    out[3] = version
    for index in (4, 6):
        length = r.byte()
        r.require(length <= 20)
        out[index:index+2] = r.take(length)
    if version == 0:
        out[1] = 5
        remain = len(data)-r.pos
        r.require(remain > 0 and remain % 4 == 0, 2)
        out[12:14] = r.take(remain)
    elif version != 1:
        out[1] = 6
        out[12:14] = r.take(len(data)-r.pos)
    else:
        r.require(first & 0x40, 2)
        kind = (first >> 4) & 3
        out[1] = kind+1
        if kind == 3:
            r.require(len(data)-r.pos >= 17, 1)
            out[8:10] = r.take(len(data)-r.pos-16)
            out[12:14] = r.take(16)
        else:
            if kind == 0:
                out[8:10] = r.take(r.var())
            length = r.var()
            r.require(length > 0, 2)
            out[10], out[11] = r.take(length)
    out[0] = r.pos
    return out


def frame(data, option=0, bound=1024):
    r, out, ranges = Reader(data), [0]*16, []
    typ = r.var()
    out[1] = typ
    if typ in (0, 1, 30):
        pass
    elif typ in (2, 3):
        largest, delay, count, first = (r.var() for _ in range(4))
        out[2:6] = largest, delay, count, first
        r.require(first <= largest)
        r.require(count <= (len(data)-r.pos)//2, 1)
        r.require(count < bound, 5)
        ranges = [largest-first, largest]
        start, low = r.pos, largest-first
        for _ in range(count):
            gap, size = r.var(), r.var()
            r.require(gap+2 <= low)
            high = low-gap-2
            r.require(size <= high)
            low = high-size
            ranges += [low, high]
        out[9:11] = start, r.pos-start
        if typ == 3:
            out[6:9] = [r.var() for _ in range(3)]
    elif typ in (4, 5, 16, 17, 18, 19, 20, 21, 22, 23, 25):
        count = {4: 3, 5: 2, 17: 2, 21: 2}.get(typ, 1)
        out[2:2+count] = [r.var() for _ in range(count)]
        if typ in (18, 19, 22, 23):
            r.require(out[2] <= 1 << 60)
    elif typ == 6:
        out[2] = r.var()
        length = r.var()
        r.require(length <= MAX-out[2])
        out[3:5] = r.take(length)
    elif typ == 7:
        length = r.var()
        r.require(length > 0)
        out[2:4] = r.take(length)
    elif 8 <= typ <= 15:
        out[2] = r.var()
        out[3] = r.var() if typ & 4 else 0
        length = r.var() if typ & 2 else len(data)-r.pos
        r.require(length <= MAX-out[3])
        out[4:6] = r.take(length)
    elif typ == 24:
        out[2], out[3] = r.var(), r.var()
        r.require(out[3] <= out[2])
        length = r.byte()
        r.require(1 <= length <= 20)
        out[4:6] = r.take(length)
        out[6:8] = r.take(16)
    elif typ in (26, 27):
        out[2:4] = r.take(8)
    elif typ in (28, 29):
        out[2] = r.var()
        out[3] = r.var() if typ == 28 else 0
        out[4:6] = r.take(r.var())
    else:
        raise WireError(7, r.pos)
    out[0] = r.pos
    return out+ranges


def parameters(data, server=0, bound=1024):
    r, out, seen = Reader(data), [0]*64, set()
    out[4+3*2], out[4+10*2], out[4+11*2], out[4+14*2] = 65527, 3, 25, 2
    while r.pos < len(data):
        r.require(len(seen) < bound, 5)
        ident, length = r.var(), r.var()
        r.require(ident not in seen, 8)
        seen.add(ident)
        off, _ = r.take(length)
        if ident > 16:
            continue
        r.require(server or ident not in (0, 2, 13, 16), 9)
        out[2] |= 1 << ident
        index = 4+ident*2
        if ident in (0, 15, 16):
            r.require(length <= 20)
            out[index:index+2] = off, length
        elif ident == 2:
            r.require(length == 16)
            out[index:index+2] = off, length
        elif ident == 12:
            r.require(length == 0)
            out[index] = 1
        elif ident == 13:
            r.require(length >= 41)
            cidlen = data[off+24]
            r.require(1 <= cidlen <= 20 and length == 41+cidlen)
            out[index:index+2] = off, length
            out[40:50] = [off, 4, int.from_bytes(data[off+4:off+6], 'big'),
                          off+6, 16, int.from_bytes(data[off+22:off+24], 'big'),
                          off+25, cidlen, off+25+cidlen, 16]
        else:
            value_reader = Reader(data[off:off+length])
            try:
                value = value_reader.var()
            except WireError:
                raise WireError(2, r.pos)
            r.require(value_reader.pos == length, 2)
            r.require(ident != 3 or value >= 1200)
            r.require(ident not in (8, 9) or value <= 1 << 60)
            r.require(ident != 10 or value <= 20)
            r.require(ident != 11 or value < 1 << 14)
            r.require(ident != 14 or value >= 2)
            out[index] = value
    out[0], out[1] = r.pos, len(seen)
    return out
