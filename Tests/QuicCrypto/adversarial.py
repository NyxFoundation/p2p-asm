"""Extra metadata limits, large packets, exhaustion and retained-HP key updates."""
from dataclasses import replace
from fixtures import Case
from oracle import *

def cases(kind):
    if kind in ('seal','open'):
        updated=expand(CLIENT_SECRET,'quic ku',32)
        newkeys=keys(updated)[:28]+CLIENT_KEYS[28:]
        packets=[('updated-retained-hp',newkeys,b'\x47abcdefgh'+bytes(4)+b'updated payload',9,2**32+7),
                 ('large-payload',CLIENT_KEYS,b'\xc3abcdefgh'+bytes(4)+bytes(range(256))*16+b'x',9,77),
                 ('exhausted-reordered',CLIENT_KEYS,b'\x43abcdefgh'+b'\xff'*4+b'boundary',9,2**62-1)]
        result=[]
        for name,k,raw,off,pn in packets:
            b=raw if kind=='seal' else protect(k,raw,off,pn)
            result.append(Case(name,k,b,pn if name!='exhausted-reordered' or kind=='seal' else 2**62,
                               off,off+4 if kind=='seal' else 0,trace=name!='large-payload'))
        base=result[0]
        result += [replace(base,name='offset-overflow',off=2**64-1,status=3,processed=False),
                   replace(base,name='input-length-overflow',overrides={2:2**64-1},status=1,processed=False),
                   replace(base,name='max-packet-resource',limit=2**36-32,
                           overrides={2:2**36-32,6:2**36},status=5,processed=False),
                   replace(base,name='packet-input-wrap',overrides={1:2**64-2},status=4,processed=False)]
        if kind=='open':
            raw=b'\x40abcdefgh\0abc'
            result.append(Case('exhausted-outside-domain',CLIENT_KEYS,protect(CLIENT_KEYS,raw,9,0),
                               2**62,9,0,status=2,trace=True))
            result.append(replace(base,name='open-nonzero-header-slot',hlen=1,status=3,processed=False))
        return result
    if kind in ('retry','retrycheck'):
        c=Case('rfc-retry',CID,RETRY if kind=='retrycheck' else RETRY[:-16])
        empty=Case('empty-pseudo-payload',b'',b'')
        if kind=='retrycheck': empty=replace(empty,b=oracle('retry',empty))
        return [empty,replace(c,name='retry-limit-overflow',limit=2**61-21,status=1,processed=False),
                replace(c,name='retry-input-overflow',overrides={3:2**64-1},status=1,processed=False),
                replace(c,name='retry-max-resource',limit=2**61-22,overrides={3:2**61-22},
                        status=5,processed=False),
                replace(c,name='retry-packet-wrap',overrides={2:2**64-2},status=4,processed=False)]
    return []
