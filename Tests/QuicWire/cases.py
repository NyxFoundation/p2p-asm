"""Deterministic public vectors, every truncation, semantic and ABI boundaries."""
import struct
from reference import packet, frame, parameters, var, WireError, MAX, Reader


def fixture(kind, label, data, option=0, bound=32):
    minimum = 512 if kind == 'tp' else 128
    f = dict(label=label, regions=[list(b'\xa5'*9+data+b'\xa5'*8),
        [0xa5]*(11+2048+8), [0xa5]*(8+2048+8), [0xa5], [0xa5], [0xa5]*4104],
        args=[0x200009,len(data),0x21000b,2048,0x220008,2048,option,bound],
        status=0, errorOffset=0, consumed=0, output=[], wipeLength=minimum, stackDepth=256,
        checkSpec=True,inputOffset=9,outputOffset=11,workOffset=8,stack=0x251000)
    try:
        words = {'packet': packet, 'frame': frame, 'tp': parameters}[kind](data,option,bound)
        f.update(output=list(struct.pack('<'+'Q'*len(words),*words)),consumed=words[0])
        f['wipeLength'] = 8*len(words)
    except WireError as e:
        f.update(status=e.code,errorOffset=e.offset)
        if kind == 'frame':
            r=Reader(data)
            try:
                if r.var() in (2,3):
                    largest,delay,count,first=(r.var() for _ in range(4))
                    if first<=largest and count<bound and count<=(len(data)-r.pos)//2:
                        f['wipeLength']=144+16*count
            except WireError:
                pass
    return f


def packet_cases():
    long = bytes.fromhex('c000000001048394c8f0021234')
    inputs = [long+b'\x03tok\x04abcd',
        bytes.fromhex('d000000001000002ab'),bytes.fromhex('e000000001000002ab'),
        bytes.fromhex('ff000000010008f067a5502a4262b5746f6b656e04a265ba2eff4d829058fb3f0f2496ba'),
        bytes.fromhex('800000000000000000000100000002'),
        bytes.fromhex('80000000020000'), b'\x40abcd', b'\x7fabcd',
        long+b'\x40\x00\x40\x01x',long+b'\0\x01x'+long+b'\0\x01y']
    result=[]
    for i,data in enumerate(inputs):
        result.append(fixture('packet',f'packet-{i}',data))
        result += [fixture('packet',f'packet-{i}-cut-{j}',data[:j]) for j in range(len(data))]
    for name,data,option in [('cid20',b'\x40'+b'x'*21,20),('cid21',b'\x40'+b'x'*22,21),
        ('zero-length',long+b'\0\0',0),('huge-token',long+var(MAX),0),
        ('huge-length',long+b'\0'+var(MAX),0),('vn-empty',bytes.fromhex('80000000000000'),0),
        ('vn-odd',bytes.fromhex('8000000000000001'),0),
        ('unknown-fixed-zero',bytes.fromhex('800000000200007f'),0),
        ('v1-fixed-zero',bytes.fromhex('80000000010000000178'),0),
        ('long-cid21',bytes.fromhex('c00000000115')+b'x'*21+b'\0\0\x01x',0)]:
        result.append(fixture('packet',name,data,option))
    result += preflight(result[0])
    return result


def frame_cases():
    inputs=[b'\0',b'\1',b'\x1e',b'\x40\1',bytes([2,20,0,2,2,1,3,0,1]),
            bytes([3,20,0,2,2,1,3,0,1,1,2,3])]
    for typ,count in [(4,3),(5,2),(16,1),(17,2),(18,1),(19,1),(20,1),
                      (21,2),(22,1),(23,1),(25,1)]:
        inputs.append(bytes([typ])+b''.join(var(i+1) for i in range(count)))
    inputs += [b'\x06\0\x03abc',b'\x07\x03tok',bytes([24,2,1,4])+b'cid0'+b't'*16,
               b'\x1a12345678',b'\x1b12345678',b'\x1c\x01\x02\x03why',b'\x1d\x01\x03why']
    for typ in range(8,16):
        inputs.append(bytes([typ])+var(128)+(var(64) if typ&4 else b'')+
                      (var(3) if typ&2 else b'')+b'abc')
    result=[]
    for i,data in enumerate(inputs):
        result.append(fixture('frame',f'frame-{i}',data))
        result += [fixture('frame',f'frame-{i}-cut-{j}',data[:j]) for j in range(len(data))]
    bad=[('unknown',b'\x1f'),('unknown-huge',var(MAX)),('ack-first',bytes([2,1,0,0,2])),
         ('ack-gap',bytes([2,1,0,1,0,0,0])),('ack-range',bytes([2,3,0,1,0,0,2])),
         ('ack-huge-count',bytes([2,1,0])+var(MAX)+b'\0'),
         ('crypto-overflow',b'\6'+var(MAX)+var(1)+b'x'),
         ('stream-overflow',b'\x0e\0'+var(MAX)+var(1)+b'x'),
         ('new-token-empty',b'\7\0'),('cid-zero',bytes([24,0,0,0])+b't'*16),
         ('cid21',bytes([24,0,0,21])+b'c'*21+b't'*16),
         ('cid-retire',bytes([24,0,1,1])+b'c'+b't'*16)]
    for typ in (18,19,22,23):
        for n in ((1<<60),(1<<60)+1,MAX):
            bad.append((f'count-{typ}-{n}',bytes([typ])+var(n)))
    for n in (0,63,64,16383,16384,(1<<30)-1,1<<30,MAX):
        bad.append((f'crypto-empty-offset-{n}',b'\6'+var(n)+b'\0'))
    result += [fixture('frame',name,data) for name,data in bad]
    result.append(fixture('frame','ack-capacity',inputs[4],bound=2))
    result.append(fixture('frame','ack-zero-capacity',bytes([2,0,0,0,0]),bound=0))
    result.append(fixture('frame','ack-max-pn',b'\x03'+var(MAX)+var(MAX)+b'\0'+var(MAX)+var(MAX)*3))
    return result


def preflight(valid):
    import copy
    result=[]
    tests=[('input-wrap',0,(1<<64)-2),('output-wrap',2,(1<<64)-2),
           ('work-wrap',4,(1<<64)-2),('output-small',3,127),('work-small',5,127),
           ('work-unaligned',4,0x220009),('input-output-alias',2,0x200009),
           ('work-output-alias',4,0x210008),('stack-input-alias',0,0x250f80),
           ('stack-output-alias',2,0x250f80),('stack-work-alias',4,0x250f80)]
    for name,index,value in tests:
        f=copy.deepcopy(valid)
        f['args'][index]=value
        f.update(label=name,status=4 if name.endswith('wrap') else 5 if name.endswith('small') else 6,
                 output=[],consumed=0,errorOffset=0,stackDepth=0,wipeLength=0,checkSpec=False)
        result.append(f)
    for name,sp,status in [('stack-unaligned',0x251001,6),('stack-underflow',0,4)]:
        f=copy.deepcopy(valid)
        f.update(label=name,status=status,stack=sp,output=[],consumed=0,errorOffset=0,
            stackDepth=0,wipeLength=0,checkSpec=False)
        result.append(f)
    return result


def tp_cases():
    def tp(i,value):
        return var(i)+var(len(value))+value
    pref=bytes.fromhex('c000020101bb')+bytes(16)+b'\x01\xbb\x04cid0'+b't'*16
    values={0:b'orig',1:var(30000),2:b't'*16,3:var(1200),4:var(MAX),5:var(100),
            6:var(200),7:var(0),8:var(1<<60),9:var(0),10:var(20),11:var(16383),
            12:b'',13:pref,14:var(2),15:b'init',16:b'retry'}
    result=[]
    inputs=[b'',b''.join(tp(i,v) for i,v in values.items()),tp(MAX,b'ignored')]
    for i,v in values.items():
        data=tp(i,v)
        inputs.append(data)
        result.append(fixture('tp',f'client-role-{i}',data,0))
        result.append(fixture('tp',f'duplicate-{i}',data+data,1))
    for i,data in enumerate(inputs):
        result.append(fixture('tp',f'tp-{i}',data,1))
        result += [fixture('tp',f'tp-{i}-cut-{j}',data[:j],1) for j in range(len(data))]
    for i,nums in {3:[1199,1200,65527,65528,MAX],8:[(1<<60),(1<<60)+1],
                   9:[(1<<60),(1<<60)+1],10:[20,21],11:[16383,16384],14:[1,2]}.items():
        result += [fixture('tp',f'bound-{i}-{n}',tp(i,var(n)),1) for n in nums]
    for i in (0,15,16):
        result += [fixture('tp',f'cid-{i}-{n}',tp(i,b'c'*n),1) for n in (0,20,21)]
    for i,bs in [(2,b't'*15),(2,b't'*17),(12,b'\0'),(13,pref[:-1]),
                  (13,pref[:24]+b'\0'+pref[25:]),(13,pref[:24]+b'\x15'+pref[25:]),
                  (3,b''),(3,var(1200)+b'\0'),(3,b'\xc0'),(1,var(1,8))]:
        result.append(fixture('tp',f'invalid-{i}-{bs.hex()}',tp(i,bs),1))
    for name,data,bound in [('unknown-duplicate',tp(100,b'a')+tp(101,b'b')+tp(100,b'c'),32),
        ('nonminimal-duplicate',tp(100,b'a')+var(100,4)+b'\0',32),
        ('huge-length',var(99)+var(MAX),32),('huge-id',tp(MAX,b''),32),
        ('bound-zero',tp(99,b''),0),('bound-two',tp(100,b'')+tp(101,b'')+tp(102,b''),2)]:
        result.append(fixture('tp',name,data,1,bound))
    many=b''.join(tp(1000+i,b'') for i in range(100))
    result.append(fixture('tp','unknown-100-parameters',many,1,100))
    result.append(fixture('tp','unknown-100-duplicate-last',many+tp(1000,b''),1,101))
    result.append(fixture('tp','unknown-100-capacity',many,1,99))
    return result
