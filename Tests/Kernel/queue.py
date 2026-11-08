from cases import fixture,pack


def fresh(n=2,source=0):return [n,0,0,0,source,64,0,0]+[0]*(32*n)


def step(s,b,op,source):
    a=s[:];cap,head,count,res,kind=s[:5]
    def done(e=0,x=0,y=0,out=b''):return (s[:] if e else a,e,x,y,out)
    if op==2:
        if count+res>=cap:return done(19)
        a[3]+=1;return done()
    if op==3:
        if not res:return done(14)
        a[3]-=1;return done()
    if op==1:
        if not count:return done(19)
        off=s[5]//8+32*head;rec=a[off:off+32];a[off:off+32]=[0]*32
        a[1]=(head+1)%cap;a[2]-=1;return done(0,rec[0],rec[1],pack(rec))
    if source!=kind or source>4:return done(23)
    if len(b)>224:return done(13)
    if op==4:
        if source!=2:return done(23)
        if not res:return done(14)
    elif count+res>=cap:return done(20 if source==0 else 19)
    import struct
    off=s[5]//8+32*((head+count)%cap)
    a[off:off+32]=[source,len(b),0,0]+list(struct.unpack('<28Q',b+bytes(224-len(b))))
    a[2]+=1
    if op==4:a[3]-=1
    return done()


def cases():
    out={f'queue-{i}':[] for i in range(5)}
    def case(name,s,b,op,source):
        a,e,x,y,data=step(s,b,op,source)
        f=fixture(name,s,b,e,x,y,a,option=source)
        if data:f['after'][2][8:264]=data
        out[f'queue-{op}'].append(f);return a
    for src in range(5):
        s=fresh(source=src)
        s=case('first',s,b'payload',0,src)
        s=case('reserve-before-send',s,b'',2,src)
        case('reserved-not-consumed',s,b'next',0,src)
        case('reservation-full',s,b'',2,src)
        case('wrong-envelope',s,b'\2'*32,0,(src+1)%5)
        case('host-spoof',s,b'\2'*32,4,src)
        if src==2:
            s=case('completion-guaranteed',s,b'result',4,src)
            case('duplicate-completion',s,b'late',4,src)
        else:s=case('cancel-reservation',s,b'',3,src)
        s=case('dequeue',s,b'',1,src)
        s=case('wrap-tail',s,b'new',0,src)
        s=case('drain-first',s,b'',1,src)
        s=case('drain-second',s,b'',1,src)
        case('empty',s,b'',1,src)
        for n in [0,1,223,224,225]:case(f'length-{n}',fresh(source=src),b'! '*n if n==0 else b'!'*n,0,src)
    return out
