"""Descriptor preflight, minimal integer encodings, ownership and policy cases."""
import copy
import struct
from fixtures import fixture, be


def fields(f):
    return list(struct.unpack('<16Q',bytes(f['regions'][2][8:136])))


def mutate(f,label,index,value,status=5,content=False):
    g = copy.deepcopy(f)
    g['label'],g['status'],g['checkSpec'] = label,status,False
    if not content:
        g['wipeLength'],g['stackDepth'] = 0,0
    fs = fields(g); fs[index] = value
    g['regions'][2][8:136] = struct.pack('<16Q',*fs)
    return g


def preflight_cases(f):
    out = []
    tests = [(1,0,1,'empty-n'),(3,0,1,'empty-e'),(3,257,1,'e-longer-n'),
             (1,65537,5,'arithmetic-ceiling'),(11,255,5,'configured-n-limit'),
             (12,0,5,'configured-e-limit'),(5,255,2,'short-signature'),
             (5,257,2,'long-signature'),(7,31,3,'short-digest'),(7,33,3,'long-digest'),
             (9,f['wipeLength']-1,5,'short-work'),(15,287,5,'short-stack'),
             (14,0,5,'zero-budget'),(14,fields(f)[14]-1,5,'short-budget'),
             (13,2047,5,'weak-policy-config'),(13,3072,6,'stronger-policy')]
    for i,v,s,label in tests:
        out.append(mutate(f,label,i,v,s,label == 'stronger-policy'))
    for i in [0,2,4,6,8,10]:
        # Make range wrapping, retaining required alignment for scratch/table.
        out.append(mutate(f,f'wrapping-pointer-{i}',i,2**64-(8 if i in [8,10] else 1),4))
    for i in [8,10]:
        out.append(mutate(f,f'unaligned-{i}',i,fields(f)[i]+1,4))
    for i in [0,2,4,6,10]:
        out.append(mutate(f,f'input-work-overlap-{i}',i,0x230008,4))
        out.append(mutate(f,f'input-stack-overlap-{i}',i,0x250ff8,4))
    out.append(mutate(f,'descriptor-work-overlap',8,0x220008,4))
    out.append(mutate(f,'work-stack-overlap',8,0x250f00,4))
    for label,ptr in [('descriptor-alignment',0x220009),('descriptor-wrap',2**64-8)]:
        g=copy.deepcopy(f);g.update(label=label,args=[ptr],status=4,
                                   wipeLength=0,stackDepth=0,checkSpec=False);out.append(g)
    for label,sp in [('stack-alignment',0x251001),('stack-underflow',272)]:
        g=copy.deepcopy(f);g.update(label=label,stack=sp,status=4,
                                   wipeLength=0,stackDepth=0,checkSpec=False);out.append(g)
    return out


def content_cases(f):
    n,e = int.from_bytes(bytes(f['n']),'big'),int.from_bytes(bytes(f['e']),'big')
    digest,sig = bytes(f['digest']),bytes(f['signature'])
    out = [fixture('s-equals-n',n,e,digest,be(n,len(sig)),2),
           fixture('s-above-n',n,e,digest,be(n+1,len(sig)),2),
           fixture('even-n',n-1,e,digest,sig,1),
           fixture('zero-e',n,0,digest,sig,1),fixture('one-e',n,1,digest,sig,1),
           fixture('two-e',n,2,digest,sig,1),fixture('even-e',n,4,digest,sig,1),
           fixture('e-equals-n',n,n,digest,sig,1),fixture('e-above-n',n,n+2,digest,sig,1)]
    out += [fixture('leading-zero-valid-n',n,e,digest,b'\x00'+sig,1,raw_n=b'\x00'+be(n)),
            fixture('leading-zero-valid-e',n,e,digest,sig,1,raw_e=b'\x00'+be(e)),
            fixture('one-bit-below-strength',(n>>1)|1,e,digest,sig,6)]
    for value in [0,1,2,3,4,5,127,255]:
        out.append(fixture(f'small-n-{value}',value,3,digest,bytes(1),1 if value<5 or value%2==0 else 6))
    for i,region,pos in [(0,0,8),(2,1,8)]:
        g=copy.deepcopy(f);g['regions'][region][pos]=0
        g.update(label=f'nonminimal-{i}',status=1,checkSpec=False);out.append(g)
    return out


def unaligned_valid(f):
    g = copy.deepcopy(f)
    g['label']='unaligned-readonly-inputs'
    g['regions'][0].insert(8,0x77)
    g['regions'][1].insert(8,0x88)
    fs=fields(g)
    for i in [0,2,4,6]: fs[i]+=1
    g['regions'][2][8:136]=struct.pack('<16Q',*fs)
    return g
