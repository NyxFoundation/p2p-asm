"""Whole-machine fixture construction, independent of the Lean executor."""
import struct
from fixtures import oracle

PRESERVED = (1,2,3,4,8,9,*range(18,28))


def guarded(payload, alignment=0):
    return b'\xa5'*(8+alignment)+payload+b'\x5a'*8


def write_case(directory, kind, c, index):
    directory.mkdir(parents=True, exist_ok=True)
    align = index%8
    result = b'' if c.status else oracle(kind,c)
    if c.published and not c.status:
        assert result == c.published, (kind,c.name,'published mismatch')
    a,b,out,work = 0x100008+align,0x200008+align,0x300008+align,0x400008
    if c.bad_range == 'input': a = 2**64-2
    if c.bad_range == 'output': out = 2**64-2
    if c.bad_range == 'second': b = 2**64-1
    if c.bad_range == 'work': work = 2**64-2
    if c.bad_range == 'alignment': work += 1
    if c.bad_range == 'overlap': out = a
    if c.bad_range == 'work-input-overlap': work = 0x100000
    if c.bad_range == 'output-work-overlap': out = work
    if c.bad_range == 'stack-work-overlap': work = 0x600300
    na = len(c.a) if c.declared_a is None else c.declared_a
    nb = len(c.b) if c.declared_b is None else c.declared_b
    output_arg = len(c.signature) if kind == 'edverify' else c.output_capacity
    args = [a,na,out,output_arg,work,c.capacity] if kind in ('xpublic','edpublic') else [
        a,na,b,nb,out,output_arg,work,c.capacity]
    registers=[0]+[0x8192a3b4c5d6e700+64*index+i for i in range(1,32)]
    registers[1:4]=[0x80000,0x600400,0x700000]
    if c.bad_range == "stack-underflow": registers[2]=128
    if c.bad_range == "stack-alignment": registers[2]+=1
    registers[10:10+len(args)]=args
    need=4160+len(c.b) if kind.startswith('ed') else 896
    output_payload=c.signature if kind=='edverify' else b'\xcc'*64
    regions=[guarded(c.a,align),guarded(c.b,align),guarded(output_payload,align),
             guarded(b'\xcc'*(need+17)),guarded(b'\x66'),b'\x69'*1040]
    used=need if c.status == 0 or c.status >= 9 else 0
    depth=(384 if kind.startswith("ed") else (272 if c.status==0 else 160)) if used else 0
    after=list(regions)
    start=8+align
    if result: after[2]=after[2][:start]+result+after[2][start+len(result):]
    after[3]=after[3][:8]+bytes(used)+after[3][8+used:]
    after[5]=after[5][:1024-depth]+bytes(depth)+after[5][1024:]
    expected_regs=[r if i in PRESERVED else 0 for i,r in enumerate(registers)]
    expected_regs[10]=c.status
    before=struct.pack('<32Q',*registers)+b''.join(regions)
    expected=struct.pack('<32Q',*expected_regs)+b''.join(after)
    for name,data in [('a',c.a),('b',c.b),('before',before),('expected',expected),
                      ('sizes',struct.pack('<6Q',*(len(r) for r in regions))),
                      ('meta',struct.pack('<8Q',c.status,used,depth,kind=='edverify',c.trace,align,len(c.signature),
                                          64 if kind in ('edsign','edverify') else 32))]:
        (directory/f'{name}.bin').write_bytes(data)
    (directory/'name.txt').write_text(c.name)
    return expected
