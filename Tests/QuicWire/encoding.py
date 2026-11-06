"""Independent canonical encoders and descriptor fixtures."""
import copy
import struct
from reference import MAX, WireError, packet, frame, parameters, var
from cases import fixture, packet_cases, frame_cases


def encode_packet(w, source):
    def data(i):
        off,n=w[i:i+2]
        if off+n>len(source): raise WireError(1,0)
        return source[off:off+n]
    k,flags=w[1:3]
    if flags|36 !=36 or w[5]>20 or w[7]>20: raise WireError(3,0)
    dc,sc,tok,payload=data(4),data(6),data(8),data(12)
    ids=bytes([len(dc)])+dc+bytes([len(sc)])+sc
    if k==5:
        if not payload or len(payload)%4: raise WireError(2,0)
        return b'\x80'+bytes(4)+ids+payload
    if k==4:
        if not tok or len(payload)!=16: raise WireError(3,0)
        return b'\xf0\0\0\0\1'+ids+tok+payload
    if k>5: raise WireError(10,0)
    n,pn=w[14:16]
    if not 1<=n<=4 or pn>=1<<(8*n): raise WireError(3,0)
    tail=pn.to_bytes(n,'big')+payload
    if k==0: return bytes([64+flags+n-1])+dc+tail
    return bytes([192+16*(k-1)+n-1,0,0,0,1])+ids+(var(len(tok))+tok if k==1 else b'')+var(len(tail))+tail


def encode_frame(w, source, bound):
    t=w[1]
    def vi(n):
        if n>MAX: raise WireError(3,0)
        return var(n)
    def data(i):
        off,n=w[i:i+2]
        if off+n>len(source): raise WireError(1,0)
        return source[off:off+n]
    if t>30: raise WireError(7,0)
    if t in (0,1,30): return bytes([t])
    if t in (2,3):
        if w[4]>=bound: raise WireError(5,0)
        if w[4]+1>(len(w)-16)//2: raise WireError(1,0)
        if w[5]>w[2] or w[16:18]!=[w[2]-w[5],w[2]]: raise WireError(3,0)
        out=b''.join(vi(n) for n in w[2:6])
        low=w[16]
        for i in range(w[4]):
            lo,hi=w[18+2*i:20+2*i]
            if not lo<=hi<=MAX or hi+2>low: raise WireError(3,0)
            out+=vi(low-hi-2)+vi(hi-lo)
            low=lo
        return bytes([t])+out+(b''.join(vi(n) for n in w[6:9]) if t==3 else b'')
    if t in (4,5,16,17,18,19,20,21,22,23,25):
        n={4:3,5:2,17:2,21:2}.get(t,1)
        if t in (18,19,22,23) and w[2]>1<<60: raise WireError(3,0)
        return bytes([t])+b''.join(vi(n) for n in w[2:2+n])
    if t==6:
        if w[2]+w[4]>MAX: raise WireError(3,0)
        return b'\6'+vi(w[2])+vi(w[4])+data(3)
    if t==7:
        if not w[3]: raise WireError(3,0)
        return b'\7'+vi(w[3])+data(2)
    if 8<=t<=15:
        if w[3]+w[5]>MAX or (not t&4 and w[3]): raise WireError(3,0)
        return bytes([t])+vi(w[2])+(vi(w[3]) if t&4 else b'')+(vi(w[5]) if t&2 else b'')+data(4)
    if t==24:
        if w[3]>w[2] or not 1<=w[5]<=20 or w[7]!=16: raise WireError(3,0)
        return b'\x18'+vi(w[2])+vi(w[3])+bytes([w[5]])+data(4)+data(6)
    if t in (26,27):
        if w[3]!=8: raise WireError(3,0)
        return bytes([t])+data(2)
    return bytes([t])+vi(w[2])+(vi(w[3]) if t==28 else b'')+vi(w[5])+data(4)


def encode_tp(w, source, server):
    mask=w[2]
    if mask>=1<<17 or mask&1<<13: raise WireError(10,0)
    def item(i,value): return var(i)+var(len(value))+value
    out=b''
    for i in (1,3,4,5,6,7,8,9,10,11,14):
        n=w[4+2*i] if i not in (7,9) else 0
        if n>MAX or (i==3 and n<1200) or (i==8 and n>1<<60) or (i==10 and n>20) or (i==11 and n>=1<<14) or (i==14 and n<2):
            raise WireError(3,0)
        out+=item(i,var(n))
    out+=item(12,b'')
    for i in (15,0,16,2):
        if i!=15 and not mask&(1<<i): continue
        if i!=15 and not server: raise WireError(9,0)
        off,n=w[4+2*i:6+2*i]
        if (n!=16 if i==2 else n>20): raise WireError(3,0)
        if off+n>len(source): raise WireError(1,0)
        out+=item(i,source[off:off+n])
    return out


def encode_fixture(kind,name,words,extra=b'',option=0,bound=32,cap=2048,source_length=None):
    source=struct.pack('<'+'Q'*len(words),*words)+extra
    if source_length is not None: source=source[:source_length]
    f=fixture('packet',name,source,option,bound)
    f.update(status=0,errorOffset=0,consumed=0,output=[],wipeLength=2048)
    f['args'][3]=cap
    try:
        if len(source)<(512 if kind=='tp-encode' else 128): raise WireError(1,0)
        if kind=='packet-encode': out=encode_packet(words,source)
        elif kind=='frame-encode': out=encode_frame(words[:len(source)//8],source,bound)
        else: out=encode_tp(words,source,option)
        if len(out)>cap: raise WireError(5,0)
        f.update(output=list(out),consumed=len(out))
        if kind=='frame-encode':
            parsed=frame(out,bound=bound)
            assert encode_frame(parsed, out, bound)==out
        elif kind=='tp-encode':
            parsed=parameters(out,option,bound)
            assert parsed[4+7*2]==parsed[4+9*2]==0 and parsed[28]==1
        else:
            assert packet(out,len(extra[:words[5]]) if words[1]==0 else 0)[0]==len(out)
    except WireError as e:
        f.update(status=e.code)
    return f


def truncations(kind, fixtures):
    """Every fixed-header cut, then every remaining cut of each valid body."""
    result=[]
    header=512 if kind=='tp-encode' else 128
    first=True
    for f in fixtures:
        if f['status']: continue
        source=bytes(f['regions'][0][9:9+f['args'][1]])
        size=header
        if kind=='frame-encode' and struct.unpack_from('<Q',source,8)[0] in (2,3):
            size+=16*(struct.unpack_from('<Q',source,32)[0]+1)
        words=list(struct.unpack_from('<'+'Q'*(size//8),source))
        for n in range(0 if first else header,len(source)):
            result.append(encode_fixture(kind,f'{f["label"]}-source-cut-{n}',words,
                source[size:],f['args'][6],f['args'][7],source_length=n))
        first=False
    return result


def packet_encodings():
    result=[]
    for kind in range(6):
        for pnlen in range(1,5):
            w=[0]*16
            w[1],w[2]=kind,36 if kind==0 else 0
            w[4:8]=[128,4,132,4]
            w[8:10]=[136,3]
            w[12:16]=[139,16 if kind==4 else 8,pnlen,(1<<(pnlen*8))-1]
            result.append(encode_fixture('packet-encode',f'build-{kind}-{pnlen}',w,b'dcidscidtok'+b'a'*16))
    w=list(struct.unpack('<16Q',bytes(result[0]['regions'][0][9:137])))
    extra=bytes(result[0]['regions'][0][137:-8])
    for i,n in [(5,21),(7,21),(14,0),(14,5),(15,256),(2,128),(13,MAX),
                (4,(1<<64)-1),(6,(1<<64)-1),(8,(1<<64)-1)]:
        bad=w.copy();bad[i]=n
        result.append(encode_fixture('packet-encode',f'reject-{i}-{n}',bad,extra))
    result += [encode_fixture('packet-encode',f'capacity-{n}',w,extra,cap=n) for n in range(14)]
    return result+truncations('packet-encode',result)


def frame_encodings():
    result=[]
    for f in frame_cases():
        if f['status'] or '-cut-' in f['label']: continue
        w=list(struct.unpack('<'+'Q'*(len(f['output'])//8),bytes(f['output'])))
        data=bytes(f['regions'][0][9:9+f['args'][1]])
        t=w[1]
        indices=([3] if t==6 else [2] if t in (7,26,27) else [4,6] if t==24 else
                 [4] if 8<=t<=15 or t in (28,29) else [])
        for i in indices: w[i]+=len(w)*8
        result.append(encode_fixture('frame-encode',f['label'],w,data))
        if t in (2,3):
            for i,n in [(4,MAX),(5,w[2]+1),(16,MAX),(18,MAX),(19,MAX)]:
                if i>=len(w): continue
                bad=w.copy();bad[i]=n
                result.append(encode_fixture('frame-encode',f'bad-ack-{t}-{i}',bad,data))
        for i in indices:
            bad=w.copy();bad[i]=(1<<64)-1
            result.append(encode_fixture('frame-encode',f'bad-view-{t}-{i}',bad,data))
        result.append(encode_fixture('frame-encode',f'no-capacity-{f["label"]}',w,data,cap=0))
    return result+truncations('frame-encode',result)


def tp_encodings():
    w=[0]*64
    for i,n in {1:30000,3:1200,4:123456,5:1000,6:2000,7:555,8:20,9:555,10:3,11:25,14:4}.items(): w[4+2*i]=n
    w[34:36]=[512,4]
    w[4:6]=[516,4];w[36:38]=[520,5];w[8:10]=[525,16]
    extra=b'init' + b'orig'+b'retry'+b't'*16
    result=[encode_fixture('tp-encode','client-profile',w,extra)]
    w[2]=(1<<0)|(1<<2)|(1<<16)
    result.append(encode_fixture('tp-encode','server-profile',w,extra,1))
    result.append(encode_fixture('tp-encode','server-fields-from-client',w,extra,0))
    for i,n in [(10,1199),(20,(1<<60)+1),(24,21),(26,16384),(32,1),(35,21),(9,15),(2,1<<13),(12,1<<62)]:
        bad=w.copy();bad[i]=n
        result.append(encode_fixture('tp-encode',f'bad-profile-{i}',bad,extra,1))
    for cap in (0,1,10,40,80): result.append(encode_fixture('tp-encode',f'capacity-{cap}',w,extra,1,cap=cap))
    return result+truncations('tp-encode',result)
