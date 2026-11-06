"""Complete independently calculated snapshots, including untouched guards."""
from dataclasses import dataclass, field
import re
import struct
from build import ROOT
from schedule_oracle import oracle, published

PRESERVED = (1, 2, 3, 4, 8, 9, *range(18, 28))


@dataclass(frozen=True)
class Case:
    name: str
    a: bytes
    b: bytes = b''
    status: int = 0
    processed: bool = True
    overrides: dict = field(default_factory=dict)
    fault: str = ''


def sizes(kind, c):
    if kind == 'boundary': return 0,0,0
    if kind == 'decode': return 16896, 240, 512
    if kind == 'encode': return ((len(c.a)+11)//8)*8+17472, 352, len(c.a)+4
    if kind == 'vector': return 0, 0, len(c.a)+max(0,c.width)
    return 1536, (304 if kind in ('hash', 'messageHash') else 528), {
        'handshake': 224, 'application': 64, 'finished': 64, 'hash': 32, 'messageHash': 36}[kind]


def cases(kind):
    if kind == 'boundary':
        from boundary_cases import cases as boundary_cases
        return boundary_cases()
    if kind in ('encode','vector'):
        import encode_cases
        return encode_cases.cases() if kind == 'encode' else encode_cases.vectors()
    if kind == 'decode':
        from codec_cases import cases as codec_cases
        return codec_cases()
    result = [Case(*v) for v in published()[kind]]
    from go_oracle import load, verified
    result += [Case(*v) for v in verified(load())[kind]]
    if kind in ('hash', 'messageHash'):
        result += [Case(f'length-{n}', bytes(i % 256 for i in range(n)))
                   for n in (0, 1, 55, 56, 63, 64, 65, 255, 4096)]
        base = result[-1]
        result += [Case('caller-limit', base.a, status=9, processed=False, overrides={9: 10}),
                   Case('sha-overflow', b'', status=2, processed=False, overrides={1: 2**61}),
                   Case('unused-input', b'abc', b'x', status=2, processed=False)]
    else:
        result += [Case(f'seed-{j}', bytes((i+j) % 256 for i in range(32)), bytes([j])*32)
                   for j in range(3)]
        base = result[0]
        for n in (0, 1, 31, 33, 65):
            result += [Case(f'bad-a-{n}', bytes(n), base.b, 2, False),
                       Case(f'bad-b-{n}', base.a, bytes(n), 2, False)]
    for fault, status in [('out-cap', 5), ('work-cap', 5), ('input-wrap', 4),
                          ('out-wrap', 4), ('work-wrap', 4), ('overlap', 4),
                          ('work-input', 4), ('out-work', 4), ('stack-work', 4),
                          ('desc-align', 4), ('desc-wrap', 4), ('work-align', 4),
                          ('table-align', 4), ('stack-align', 4), ('stack-underflow', 4)]:
        result.append(Case(fault, base.a, base.b, status, False, fault=fault))
    return result


def write_case(path, kind, c, index):
    path.mkdir(parents=True, exist_ok=True)
    need, depth, size = sizes(kind, c)
    align = 0 if c.fault and kind == 'decode' else index % 8
    a, b, out, work, desc, sp = (0x100008+align, 0x200008+align, 0x300008+align,
                                0x400008, 0x500008, 0x600400)
    if kind == 'decode': out = 0x300008
    if not c.a: a = 2**64-1
    if not c.b: b = 2**64-1
    f = c.fault
    if f == 'input-wrap': a = 2**64-2
    if f == 'out-wrap': out = 2**64-(256 if kind == 'decode' else 2)
    if f == 'work-wrap': work = 2**64-8
    if f == 'overlap': out = a
    if f == 'work-input': work = 0x100000
    if f == 'out-work': out = work
    if f == 'stack-work': work = 0x600300
    if f == 'desc-align': desc += 1
    if f == 'desc-wrap': desc = 2**64-8
    if f == 'work-align': work += 1
    if f == 'stack-align': sp += 1
    if f == 'stack-underflow': sp = 128
    fields = [a, len(c.a), b, len(c.b), out, size-(f == 'out-cap'), work,
              need-(f == 'work-cap'), 0x500108+(f == 'table-align'), len(c.a)]
    if kind == 'decode':
        fields = [a, len(c.a), out, size-(f == 'out-cap'), work, need-(f == 'work-cap'), c.limit, int(c.strict)]
    if kind == 'encode':
        fields = [a,len(c.a),c.tag,out,size-(f == 'out-cap'),work,need-(f == 'work-cap'),c.limit,int(c.strict)]
    if kind == 'vector':
        fields = [a,len(c.a),c.width,c.minimum,out,size-(f == 'out-cap'),c.limit]
    for i, value in c.overrides.items(): fields[i] = value
    regs = [0] + [0x8192a3b4c5d6e700+64*index+i for i in range(1, 32)]
    regs[1:4] = [0x80000, sp, 0x700000]
    regs[10] = desc
    if kind == 'boundary': regs[10:12] = c.a
    source = (ROOT/'Libp2pAsm/Spec/Crypto/SHA256.lean').read_text()
    constants = source.split('def roundConstants', 1)[1].split('#v[', 1)[1].split(']', 1)[0]
    table = b''.join(struct.pack('<Q', int(x, 16)) for x in re.findall(r'0x[0-9a-f]+', constants))
    guarded = lambda data, offset=0: b'\xa5'*(8+offset)+data+b'\x5a'*8
    metadata = struct.pack('<'+'Q'*len(fields), *fields).ljust(256, b'\x66') + table
    regions = [guarded(c.a, align), guarded(c.b, align), guarded(b'\xcc'*(size+17), align),
               guarded(b'\xcc'*(need+17)), guarded(metadata), b'\x69'*1040]
    used = need if c.processed else 0
    depth = depth if c.processed else 0
    if kind == 'encode' and c.processed and len(c.a) < 1: depth = 112
    after = list(regions)
    if c.status == 0:
        if kind == 'decode':
            from codec_oracle import decode
            result = decode(c.a, c.limit, c.strict)
        elif kind == 'encode': result = bytes([c.tag])+len(c.a).to_bytes(3,'big')+c.a
        elif kind == 'boundary': result = b''
        elif kind == 'vector': result = len(c.a).to_bytes(c.width,'big')+c.a
        else: result = oracle(kind, c.a, c.b)
        outalign = 0 if kind == 'decode' else align
        after[2] = after[2][:8+outalign] + result + after[2][8+outalign+len(result):]
    after[3] = after[3][:8] + bytes(used) + after[3][8+used:]
    after[5] = after[5][:1024-depth] + bytes(depth) + after[5][1024:]
    expectedregs = [r if i in PRESERVED else 0 for i, r in enumerate(regs)]
    expectedregs[10] = c.status
    meta = [c.status, used, depth, min(4,len(c.a)) if kind == 'decode' and not c.fault and not c.overrides else 0,
            int(kind in ('decode','encode','vector','boundary') and not c.fault and not c.overrides), align, size, 0 if kind == 'decode' else align,
            int(c.strict) if kind in ('decode','encode') else 0,
            {'decode':64,'encode':72,'vector':56,'boundary':0}.get(kind,80)]
    for name, data in {'a': c.a, 'b': c.b,
        'before': struct.pack('<32Q', *regs)+b''.join(regions),
        'expected': struct.pack('<32Q', *expectedregs)+b''.join(after),
        'sizes': struct.pack('<6Q', *(len(r) for r in regions)),
        'meta': struct.pack('<10Q', *meta)}.items():
        (path/f'{name}.bin').write_bytes(data)
    (path/'name.txt').write_text(c.name)
