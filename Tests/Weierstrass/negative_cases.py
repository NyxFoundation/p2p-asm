"""Public validation must finish before any private byte is accessed."""
import copy
import json
import struct
from pathlib import Path
from check import CURVES


def patch(f, offset, value):
    f['regions'][1][8+offset:16+offset] = list(struct.pack('<Q', value))


def rejection(original, label, status, depth=0):
    f = copy.deepcopy(original)
    f.update(label=label, status=status, stackDepth=depth, wipeLength=2064 if depth else 0, traceGroup='')
    f['expected'] = f['regions'][2][f['outputOffset']:-8]
    return f


def public_errors(curve, kind, original):
    edits = [('out-capacity',72, max(0,len(original['expected'])-1),5),
             ('work-capacity',88,2063,5), ('work-align',80,0x230009,4),
             ('work-wrap',80,2**64-8,4), ('out-wrap',64,2**64-1,4)]
    if kind.startswith('verify'):
        edits = [e for e in edits if not e[0].startswith('out-')]
    if kind in ('public','ecdh') or kind.startswith('sign'):
        edits += [('secret-length',8,31,1), ('secret-wrap',0,2**64-16,4)]
    if kind == 'ecdh' or kind.startswith('verify'):
        edits += [('peer-length',24,34,1),('peer-wrap',16,2**64-16,4)]
    if kind.startswith(('sign','verify')):
        edits += [('digest-length',40,31,1),('digest-wrap',32,2**64-16,4)]
    if kind.startswith('sign'):
        edits += [('constants-align',96,0x240009,4),('constants-wrap',96,2**64-8,4)]
    out = []
    for label, offset, value, status in edits:
        f = rejection(original,label,status)
        patch(f,offset,value)
        out.append(f)
    for label, field, value in [('descriptor-align','args',[0x210009]),
        ('descriptor-wrap','args',[2**64-8]),('stack-align','stack',0x251003),('stack-underflow','stack',127)]:
        f = rejection(original,label,4)
        f[field] = value
        out.append(f)
    return out


def peer_errors(curve, original):
    p, _ = CURVES[curve]
    size = 65 if curve == 'p256' else 33
    cases = [('infinity',bytes(size),112),('noncanonical-x',bytes([4 if curve=='p256' else 2])+p.to_bytes(32,'big')+bytes(size-33),112)]
    if curve == 'p256':
        encoded = bytes(original['regions'][1][128:128+size])
        cases += [('hybrid-tag',bytes([6])+encoded[1:],112)]
        cases += [('noncanonical-y',bytes([4])+bytes(32)+p.to_bytes(32,'big'),224),
                  ('off-curve',bytes([4])+bytes(64),224)]
        for t in json.loads((Path(__file__).parent/'wycheproof-ecdh.json').read_text())['tests']:
            data = bytes.fromhex(t['public'])
            if len(data)==65:
                cases.append((f'wycheproof-ecdh-{t["tcId"]}',data,224))
    else:
        # x=0 gives y²=7, which is not a quadratic residue modulo secp256k1 p.
        assert pow(7,(p-1)//2,p)==p-1
        cases += [('no-square-root',bytes([2])+bytes(32),464)]
    out = []
    for label, data, depth in cases:
        f = rejection(original,label,9,depth)
        f['regions'][1][128:128+size] = data
        out.append(f)
    return out


def failure_cases(curve):
    from sign_cases import fixture
    n = CURVES[curve][1]
    out=[]
    for label,k,r,s in [('valid',1,1,1),('nonce-zero',0,1,1),('nonce-order',n,1,1),
                         ('nonce-max',2**256-1,1,1),('r-zero',1,0,1),('s-zero',1,1,0)]:
        data=b''.join(x.to_bytes(32,'big') for x in (k,r,s))
        output=bytes([0xcc]*64)
        expected=data[32:] if label=='valid' else output
        f=fixture(label,1,b'',bytes(32),b'',output,expected,0 if label=='valid' else 10,112)
        f['regions'][0]=[0xa5]*11+list(data)+[0x5a]*8
        patch(f,8,96)
        f['traceGroup']='fixed'
        out.append(f)
    return out
