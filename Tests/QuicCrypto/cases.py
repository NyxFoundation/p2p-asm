"""Independent complete memory/register snapshots, including guards and wipes."""
import struct
import re
from dataclasses import replace
from build import ROOT
from oracle import oracle
from vectors import SAMPLES,MASKS

PRESERVED=(1,2,3,4,8,9,*range(18,28))

def guarded(payload,align=0): return b'\xa5'*(8+align)+payload+b'\x5a'*8

def sizes(kind,c):
    if kind in ('initial','keys','update'): return 1280,528,{'initial':184,'keys':44,'update':60}[kind],56
    if kind=='nonce': return 0,0,12,32
    if kind=='number': return 0,0,8,40
    if kind in ('seal','open'): return 1616+len(c.b),240,len(c.b)+(16 if kind=='seal' else 0),88
    n=len(c.b)-(16 if kind=='retrycheck' else 0)
    return 1441+len(c.a)+max(0,n),240,0 if kind=='retrycheck' else 16,72

def descriptor(kind,c,a,b,out,work,cap):
    na,nb=len(c.a),len(c.b)
    need,_,size,_=sizes(kind,c)
    if kind in ('initial','keys','update'): return [a,na,out,size,work,cap,0x500108]
    if kind=='nonce': return [a,c.pn,out,size]
    if kind=='number': return [c.pn,c.off,c.hlen,out,size]
    if kind in ('seal','open'): return [a,b,nb,c.off,c.pn,out,size,work,cap,c.limit,c.hlen]
    return [a,na,b,nb,out,size,work,cap,c.limit]

def arguments(kind,c,align):
    need,depth,size,descsize=sizes(kind,c)
    a,b,out,work,desc,sp=0x100008+align,0x200008+align,0x300008+align,0x400008,0x500008,0x600400
    if not c.a: a=2**64-1
    if not c.b: b=2**64-1
    f=c.fault
    if f=='input-wrap': a=2**64-2
    if f=='output-wrap': out=2**64-2
    if f=='work-wrap': work=2**64-8
    if f=='work-alignment': work+=1
    if f=='overlap': out=a
    if f=='work-input': work=0x100000
    if f=='output-work': out=work
    if f=='stack-work': work=0x600300
    if f=='stack-underflow': sp=128
    if f=='stack-alignment': sp+=1
    if f=='descriptor-wrap': desc=2**64-8
    if f=='descriptor-alignment': desc+=1
    fields=descriptor(kind,c,a,b,out,work,need-1 if f=='work-capacity' else need)
    oi={'initial':3,'keys':3,'update':3,'nonce':3,'number':4,'seal':6,'open':6,'retry':5,'retrycheck':5}[kind]
    if f=='output-capacity': fields[oi]=size-1
    for index,value in c.overrides.items(): fields[index]=value
    return fields,desc,sp

def write_case(directory,kind,c,index):
    directory.mkdir(parents=True,exist_ok=True)
    align=index%8
    result=b'' if c.status else oracle(kind,c)
    need,depth,size,descsize=sizes(kind,c)
    fields,desc,sp=arguments(kind,c,align)
    regs=[0]+[0x8192a3b4c5d6e700+64*index+i for i in range(1,32)]
    regs[1:4]=[0x80000,sp,0x700000]; regs[10]=desc
    source=(ROOT/'Libp2pAsm/Spec/Crypto/SHA256.lean').read_text()
    constants=source.split('def roundConstants',1)[1].split('#v[',1)[1].split(']',1)[0]
    table=b''.join(struct.pack('<Q',int(x,16)) for x in re.findall(r'0x[0-9a-f]+',constants))
    metadata=struct.pack('<'+'Q'*len(fields),*fields).ljust(256,b'\x66')+table
    regions=[guarded(c.a,align),guarded(c.b,align),guarded(b'\xcc'*max(64,size+17),align),
             guarded(b'\xcc'*(need+17)),guarded(metadata),b'\x69'*1040]
    used=need if c.processed and kind not in ('number','nonce') else 0
    depth=depth if used else 0
    after=list(regions); start=8+align
    if not c.status: after[2]=after[2][:start]+result+after[2][start+len(result):]
    after[3]=after[3][:8]+bytes(used)+after[3][8+used:]
    after[5]=after[5][:1024-depth]+bytes(depth)+after[5][1024:]
    expectedregs=[r if i in PRESERVED else 0 for i,r in enumerate(regs)]
    expectedregs[10]=c.status
    files={'a':c.a,'b':c.b,'before':struct.pack('<32Q',*regs)+b''.join(regions),
           'expected':struct.pack('<32Q',*expectedregs)+b''.join(after),
           'sizes':struct.pack('<6Q',*(len(r) for r in regions)),
           'meta':struct.pack('<10Q',c.status,used,depth,c.pn,c.trace,align,size,c.off,c.hlen,descsize)}
    for name,data in files.items(): (directory/f'{name}.bin').write_bytes(data)
    (directory/'name.txt').write_text(c.name)
    if kind in ('seal','open') and c.name in ('rfc-client','rfc-server'):
        vector=0 if c.name=='rfc-client' else 1
        (directory/'sample.bin').write_bytes(SAMPLES[vector])
        (directory/'mask.bin').write_bytes(MASKS[vector])

def changed(kind,c):
    a=bytes(x^255 for x in c.a)
    if kind=='open': a=bytes(x^255 for x in c.a[:28])+c.a[28:]
    other=replace(c,a=a,trace=False)
    if c.status==0 and kind in ('open','retrycheck'): other=replace(other,status=6)
    if kind=='retrycheck' and not c.a:
        other=replace(other,b=c.b[:-1]+bytes([c.b[-1]^1]))
    return other
