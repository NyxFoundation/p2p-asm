"""Public metadata rejection, packet-number boundaries and adversarial inputs."""
from dataclasses import dataclass, replace, field
import random
from oracle import *

@dataclass(frozen=True)
class Case:
    name: str
    a: bytes = b''
    b: bytes = b''
    pn: int = 0
    off: int = 0
    hlen: int = 0
    limit: int = 65535
    status: int = 0
    processed: bool = True
    trace: bool = False
    overrides: dict = field(default_factory=dict)
    fault: str = ''

def number_cases():
    result = [Case('rfc9000-A3',pn=0xa82f30eb,off=0x9b32,hlen=2)]
    for count in range(1,5):
        w = 1 << (8*count)
        for expected in [0,1,w//2-1,w//2,w-1,w,w+1,2**62-w,2**62-1,2**62]:
            for truncated in sorted({0,1,w//2-1,w//2,w-1,expected % w}):
                try: reconstruct(expected,truncated,count); status=0
                except ValueError: status=2
                result.append(Case(f'pn-{count}-{expected}-{truncated}',pn=expected,off=truncated,
                                   hlen=count,status=status,processed=False))
    result += [Case('bad-count',hlen=0,status=2,processed=False,trace=True),
               Case('bad-count5',hlen=5,status=2,processed=False),
               Case('truncated-overflow',pn=0,off=256,hlen=1,status=2,processed=False),
               Case('expected-overflow',pn=2**62+1,hlen=1,status=2,processed=False)]
    return result

def packet_cases(kind, rng):
    result=[]
    for name,k,h,p,packet,pn,count in (
        ('rfc-client',CLIENT_KEYS,CLIENT_HEADER,CLIENT_PAYLOAD,CLIENT_PACKET,2,4),
        ('rfc-server',SERVER_KEYS,SERVER_HEADER,SERVER_PAYLOAD,SERVER_PACKET,1,2)):
        result.append(Case(name,k,h+p if kind=='seal' else packet,pn,len(h)-count,
                           len(h) if kind=='seal' else 0,trace=True))
    for count in range(1,5):
        for first in [0x40,0xc0,0xe0]:
            for size in sorted({4-count,16,33}):
                pn = [0,2**32+17,2**62-1][size % 3]
                h = bytes([first+count-1])+rng.randbytes(8)+pn.to_bytes(8,'big')[-count:]
                p = rng.randbytes(size)
                k = rng.randbytes(44)
                b = h+p if kind=='seal' else protect(k,h+p,9,pn)
                result.append(Case(f'packet-{first}-{count}-{size}',k,b,pn,9,
                                   len(h) if kind=='seal' else 0,trace=size==16))
    base=result[1]
    for n in [0,1,15,19]:
        result.append(replace(base,name=f'truncated-{n}',b=base.b[:n],status=3 if n<=base.off else 7,
                              processed=False,trace=True))
    if kind=='open':
        for i in range(16):
            b=bytearray(base.b); b[-1-i]^=1
            result.append(replace(base,name=f'bad-tag-{i}',b=bytes(b),status=6,trace=i==0))
        for i in [0,5,base.off,base.off+4,len(base.b)-17]:
            b=bytearray(base.b); b[i]^=128 if i==0 else 1
            result.append(replace(base,name=f'bad-header-payload-{i}',b=bytes(b),status=6,trace=False))
        result += [replace(base,name='wrong-sample-offset',off=base.off-1,status=6,trace=False),
                   replace(base,name='reordered',pn=130,trace=True),
                   replace(base,name='wrong-window',pn=65538,status=6,trace=True)]
    else:
        result.append(replace(base,name='wrong-header-length',hlen=base.hlen+1,status=3,processed=False))
        result.append(replace(base,name='huge-header-length',hlen=2**64-1,status=3,processed=False))
    result += [replace(base,name='number-overflow',pn=2**62+(kind=='open'),status=2,processed=False),
               replace(base,name='configured-limit',limit=len(base.b)-1,status=1,processed=False),
               replace(base,name='gcm-limit',limit=2**36-31,status=1,processed=False),
               replace(base,name='no-sample',b=base.b[:base.off+3] if kind=='seal' else base.b[:base.off+19],
                       status=7,processed=False),
               replace(base,name='zero-offset',off=0,status=3,processed=False)]
    return result

def cases(kind):
    rng=random.Random(9001)
    if kind=='number': return number_cases()
    if kind in ('seal','open'): result=packet_cases(kind,rng)
    elif kind=='nonce':
        result=[Case(f'nonce-{n}',rng.randbytes(12),pn=n,trace=True) for n in
                [0,1,255,256,2**32-1,2**32,2**48+7,2**61,2**62-1]]
        result += [Case('nonce-overflow',pn=2**62,status=2,processed=False,trace=True),
                   Case('nonce-max',pn=2**64-1,status=2,processed=False)]
    elif kind=='initial':
        result=[Case('rfc-initial',CID,trace=True)] + [Case(f'cid-{n}',rng.randbytes(n),trace=n in (0,20)) for n in range(21)]
        result.append(Case('cid-too-long',bytes(21),status=1,processed=False,trace=True))
    elif kind in ('keys','update'):
        result=[Case('client-secret',CLIENT_SECRET,trace=True),Case('server-secret',SERVER_SECRET),
                Case('random-secret',rng.randbytes(32),trace=True),Case('zero-secret',bytes(32))]
        result += [Case(f'secret-length-{n}',bytes(n),status=1,processed=False,trace=True) for n in (0,31,33)]
    else:
        checking=kind=='retrycheck'
        result=[Case('rfc-retry',CID,RETRY if checking else RETRY[:-16],trace=True)]
        for n in (0,1,20):
            c=Case(f'cid-{n}',rng.randbytes(n),rng.randbytes(4097 if n==1 else 37),trace=n!=1)
            if checking: c=replace(c,b=c.b+oracle('retry',c))
            result.append(c)
        if checking:
            for i in range(16):
                b=bytearray(RETRY); b[-i-1]^=1
                result.append(Case(f'bad-tag-{i}',CID,bytes(b),status=6,trace=True))
            result += [Case(f'short-{n}',CID,RETRY[:n],status=1,processed=False,trace=True) for n in range(16)]
        result.append(Case('cid-too-long',bytes(21),RETRY,status=1,processed=False))
    base=result[0]
    for fault in ['input-wrap','output-wrap','work-wrap','work-alignment','overlap','work-input',
                  'output-work','stack-work','stack-underflow','stack-alignment','descriptor-wrap','descriptor-alignment']:
        if kind=='nonce' and ('work' in fault or fault.startswith('stack-')): continue
        if kind=='retrycheck' and fault in ('output-wrap','overlap','output-work'): continue
        result.append(replace(base,name=fault,fault=fault,status=4,processed=False,trace=True))
    if kind!='retrycheck': result.append(replace(base,name='output-capacity',fault='output-capacity',status=5,processed=False,trace=True))
    if kind!='nonce': result.append(replace(base,name='work-capacity',fault='work-capacity',status=5,processed=False,trace=True))
    return result
