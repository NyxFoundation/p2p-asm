"""Byte-exact fixtures from the independent protocol oracle."""
from dataclasses import replace
import struct
from oracle import Receive, MAX, NONE
B = [0x200000 + 0x10000*i for i in range(6)]
P = [B[0]+8, B[1]+9, B[2]+11, B[3]+9, B[4]+8, B[5]+4096]

def words(xs):
    return list(struct.pack('<'+'Q'*len(xs), *xs))

def recv_regions(s, payload=b''):
    meta = [s.cap,P[1],P[2],s.base,s.highest,s.final,s.limit,s.allowance,s.crypto,s.reset]
    data, tags = [0]*s.cap, [0]*s.cap
    for pos,value in s.data.items():
        data[pos % s.cap], tags[pos % s.cap] = value, 1
    return [[165]*8+words(meta)+[165]*8,
            [165]*9+data+[165]*8, [165]*11+tags+[165]*8,
            [165]*9+list(payload)+[165]*8, [165]*32, [165]*4112]

def fixture(label, before, after, args, outputs, *, stack=True, reads=None, writes=None):
    after = [list(r) for r in after]
    if stack:
        after[5][3968:4096] = [0]*128
    r = [[P[0],len(before[0])-16], [P[1],len(before[1])-17],
         [P[2],len(before[2])-19], [P[3],len(before[3])-17]]
    w = [] if outputs[0] else [r[0],r[1],r[2]]
    if stack:
        r += [[P[5]-128,128]]
        w += [[P[5]-128,128]]
    return dict(label=label,regions=before,expectedRegions=after,args=args,
                outputs=outputs+[0]*(5-len(outputs)),reads=r if reads is None else reads,
                writes=w if writes is None else writes,budget=5000+200*sum(map(len,before[:4])),stackUsed=stack)

def rx(label,s,off,payload,flag=0):
    e,t,delta = s.put(off,payload,flag)
    before = recv_regions(s,payload)
    after = recv_regions(t,payload)
    return fixture(label,before,after,[P[0],80,P[3],len(payload),0,len(payload),off,flag],
                   [e,delta,0,0,flag if not e else 0]), t

def receive_cases():
    fs=[]
    for cap in (1,3,8,17):
        for base in (0,cap-1,MAX-cap):
            s=Receive(cap=cap,base=base,highest=base)
            for n in range(cap+2):
                for off in (base,max(0,base-1),base+cap,MAX):
                    for flag in (0,1):
                        fs.append(rx(f'boundary-{cap}-{base}-{off}-{n}-{flag}',s,off,bytes(range(n)),flag)[0])
    s=Receive()
    for off,p,flag in [(3,b'def',0),(0,b'abc',0),(2,b'cde',0),(0,b'abcXef',0),
                       (6,b'gh',1),(8,b'',1),(8,b'x',0),(7,b'',1),(8,b'',2),(8,b'',2)]:
        f,s=rx(f'sequence-{len(fs)}',s,off,p,flag); fs.append(f)
    for s in (Receive(limit=3),Receive(allowance=2),Receive(crypto=1)):
        for off in (0,1,3,8,MAX):
            for p in (b'',b'xyz'):
                for flag in (0,1,2,3):
                    fs.append(rx(f'limits-{len(fs)}',s,off,p,flag)[0])
    for cap in (3,8):
        s=Receive(cap=cap,base=cap-1,highest=cap-1)
        _,s,_=s.put(cap-1,bytes(range(cap)))
        fs.append(rx(f'wrap-conflict-{cap}',s,cap,b'Z')[0])
    return fs

def consume_cases():
    fs=[]
    for cap in (1,3,8):
        for base in range(cap*2):
            for n in range(cap+2):
                s=Receive(cap=cap,base=base,highest=base)
                _,s,_=s.put(base,bytes(range(cap)))
                e,t=s.consume(n) if n<=cap else (8,s)
                fs.append(fixture(f'consume-{cap}-{base}-{n}',recv_regions(s),recv_regions(t),
                                  [P[0],80,n,0,0,0,0,0],[e]))
    s=Receive(data={2:7},highest=3)
    fs.append(fixture('consume-gap',recv_regions(s),recv_regions(s),[P[0],80,3,0,0,0,0,0],[8]))
    return fs

def peek_cases():
    fs=[]
    for base in range(16):
        for n in range(9):
            s=Receive(base=base,highest=base)
            _,s,_=s.put(base,bytes(range(n)))
            off,size=s.peek()
            fs.append(fixture(f'peek-{base}-{n}',recv_regions(s),recv_regions(s),
                              [P[0],80,0,0,0,0,0,0],[0,0,off,size,0]))
    for s in (Receive(final=0),Receive(final=0,reset=1)):
        fs.append(fixture(f'closed-{s.reset}',recv_regions(s),recv_regions(s),
                          [P[0],80,0,0,0,0,0,0],[0,0,0,0,2 if s.reset else 1]))
    return fs
