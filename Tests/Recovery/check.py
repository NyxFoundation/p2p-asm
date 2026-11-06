"""Independent arithmetic/trace checks, Spec, real RV64IM and both QEMU paths."""
import argparse
import hashlib
import json
import os
import struct
import sys
from pathlib import Path
from build import ROOT, OUT, build, run

sys.path.append(str(ROOT / 'Tests/HashCrypto'))
import native

W = 2**64
PN = 2**62
PRESERVED = (1, 2, 3, 4, 8, 9, *range(18, 28))


def pack(words):
    return struct.pack(f'<{len(words)}Q', *words)


def unpack(data):
    return list(struct.unpack(f'<{len(data)//8}Q', data))


def invariant(s):
    assert all(0 <= x < W for x in s)
    packets = [s[64+32*s[4]+20*i:64+32*s[4]+20*(i+1)] for i in range(s[12])]
    for path in range(s[4]):
        q = s[64+32*path:96+32*path]
        ps = [p for p in packets if p[2] == path]
        assert q[4] == sum(p[4] for p in ps if p[16])
        assert q[5] == sum(p[4] for p in ps if p[0] in (1, 2, 7))
        assert q[6] == sum(p[4] for p in ps if p[0] == 3 and p[5])
        assert q[7] == sum(p[4] for p in ps if p[0] in (1, 2, 7) and p[5])
        if s[17] and not q[2]:
            assert q[4]+q[5] <= 3*q[3]
    for space in range(3):
        ps = [p for p in packets if p[1] == space]
        assert len({p[3] for p in ps}) == len(ps)
        assert all(p[3] < s[32+8*space] for p in ps)
        assert all(p[0] not in (3, 4, 5, 8) or p[16] for p in ps)
    assert s[14] == sum(p[0] in (1, 2, 7) for p in packets)
    assert s[15] == sum(p[0] in (1, 2, 3, 7) for p in packets)


class Harness:
    def __init__(self, args, executable, env):
        self.args, self.executable, self.env = args, executable, env
        self.count, self.records = 0, []

    def call(self, kind, state, args=(), now=None, gen=1, status=0, ranges=(), descriptor=None, register_overrides=None):
        self.count += 1
        directory = OUT / 'cases' / f'{self.count:04}-{kind}'
        case = directory / 'case-0'
        case.mkdir(parents=True, exist_ok=True)
        event = [0, gen, state[16] if now is None else now, *args]
        event += [0]*(16-len(event))
        event += [v for r in ranges for v in r]
        regions = [pack(event), bytes(64), pack(state), bytes([0xa5])*(8*len(state)+64),
                   pack([0x300008,8*len(state),0x100008,8*len(event),0x600008,64,
                         0x400008,8*len(state)+64]), bytes([0x5a])*1040]
        if descriptor:
            d = unpack(regions[4])
            for i,v in descriptor.items(): d[i] = v
            regions[4] = pack(d)
        regions = [b'\xa7'*8+r+b'\xb9'*8 for r in regions]
        registers = [0]+[0x900+i for i in range(1,32)]
        registers[1:5] = [0x80000,0x600400,0x700000,0x904]
        registers[10] = 0x500008
        for i,v in (register_overrides or {}).items(): registers[i] = v
        before = pack(registers)+b''.join(regions)
        (case/'before.bin').write_bytes(before)
        (case/'sizes.bin').write_bytes(pack([len(r) for r in regions]))
        for name in ['a.bin','b.bin','meta.bin']:
            (case/name).write_bytes(b'')
        try:
            output = run([self.executable,kind,str(directory)],env=self.env)
        except RuntimeError:
            self.explain(case, [len(r) for r in regions])
            raise
        actual = (case/'after.bin').read_bytes()
        if status is None: status = unpack(actual[:256])[10]
        assert unpack(actual[:256])[10] == status, (kind, status, unpack(actual[:256])[10])
        offsets = [256+sum(map(len, regions[:i])) for i in range(6)]
        result = unpack(actual[offsets[2]+8:offsets[2]+len(regions[2])-8])
        action = unpack(actual[offsets[5]+8:offsets[5]+72])
        invariant(result)
        if not self.args.model_only:
            native.prepare(self.args.prefix, directory)
            native.execute(self.args,directory,case,actual,native.linker(directory))
        self.records.append({'kind':kind,'status':status,'instructions':int((case/'steps.txt').read_text()),
                             'code_sha256':hashlib.sha256((directory/'encoded.bin').read_bytes()).hexdigest()})
        print(f'{self.count}: {output.strip()}', flush=True)
        return result, action

    @staticmethod
    def explain(case, sizes):
        if not (case/'expected.bin').exists():
            return
        a, b = (case/'after.bin').read_bytes(), (case/'expected.bin').read_bytes()
        differences = [(i//8, x, y) for i in range(0,min(len(a),len(b)),8)
                       if (x:=unpack(a[i:i+8])[0]) != (y:=unpack(b[i:i+8])[0])]
        print('snapshot sizes', sizes, 'first differing words (actual, expected)', differences[:20])

    def init(self, server=False, history=16):
        state = [0]*(64+64+20*history+8)
        state = self.call('init',state,[9,int(server),history,2,4,min(3,history),history,3,5_000_000_000,
                                      1400,16_777_216,3,25_000_000],now=1)[0]
        state = self.call("keys",state,[1])[0]
        return self.call("keys",state,[2])[0]

    def reserve(self, s, space=2, size=1200, now=None, flags=3):
        return self.call('reserve',s,[space,0,size,flags,123,1,777,1],now=now)

    def sent(self, s, action, now):
        return self.call('result',s,[action[1],action[3],0,now],now=now)[0]

    def ack(self, s, ranges, now, space=2, delay=0, error=0):
        s, _ = self.call('ack',s,[space,delay,len(ranges)],ranges=ranges,now=now)
        while s[23]:
            expected = None if error else 0
            s, action = self.call('resume',s,status=expected)
            if self.records[-1]["status"]:
                assert self.records[-1]["status"] == error
                return s
        return s


def scenarios(h):
    s = h.init(server=True)
    s,_ = h.call('reserve',s,[2,0,1200,3,1,1,1,1],status=7)
    s,_ = h.call('receive',s,[0,400])
    s,a = h.reserve(s)
    h.ack(s,[(0,0)],2,error=12)
    s,_ = h.call('result',s,[0,a[3],1,0],now=2)
    assert s[14] == 1 and s[64+5] == 1200 and s[64+6] == 0
    s,a = h.call('retry',s,[0],now=3)
    s = h.sent(s,a,4)
    h.call('result',s,[0,a[3],0,4],now=5,status=6)
    s = h.ack(s,[(0,0)],100_000_004)
    q = s[64:96]
    assert (q[12],q[13],q[14],q[15]) == (100_000_000,100_000_000,100_000_000,50_000_000)
    old = s.copy()
    s = h.ack(s,[(0,0)],100_000_005)
    assert s[64:96] == old[64:96]
    s,_ = h.call('newpath',s,[1,2])
    s,_ = h.call('challenge',s,[1,0xdeadbeef,200_000_000])
    h.call('response',s,[1,2,999],status=6)
    s,_ = h.call('response',s,[1,2,0xdeadbeef])
    s,_ = h.call('activate',s,[1,2])
    h.call('handshake',s,[0,1,1],status=2)
    s,_ = h.call('handshake',s,[1,1,1])
    h.call('timer',s)
    s = h.init()
    s,a = h.reserve(s,space=0,size=1300)
    s,_ = h.call('result',s,[0,a[3],2,0],now=2)
    assert s[32] == 1 and s[64+24] == 1299
    h.ack(s,[(0,0)],3,space=0,error=12)
    s,a = h.reserve(s,space=0,now=3)
    assert a[2] == 1
    h.call('expire',s,[1],now=5_000_000_003)
    h.call('result',s,[1,a[3],0,3],now=4,gen=2,status=6)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    p.add_argument('--prefix',default='riscv64-unknown-elf-')
    p.add_argument('--model-only',action='store_true')
    args = p.parse_args()
    exe, env = build()
    h = Harness(args,exe,env)
    scenarios(h)
    import traces
    traces.run(h)
    (OUT/'verification.json').write_text(json.dumps(h.records,indent=2)+'\n')
    print(f'PASS {h.count} transitions; QEMU paths: {0 if args.model_only else 2*h.count}')


if __name__ == '__main__':
    main()
