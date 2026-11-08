"""Independent request reservation, matching, deadline, and zeroization oracle."""
from cases import fixture,pack
from limits import MAX
import struct


def fresh():
    h=[4,0,1,4,1,1,1,1,0,0,0,0,32,4,0,0,0,0,100,10,20]+[0]*11
    return h+[0]*64+[0]*(3*4)


def step(s,v,body,op,source=2):
    a=s[:]
    def done(e=0,x=0,y=0,data=b''):return (s[:] if e else a,e,x,y,data)
    if op==0 and s[16]:return done(15)
    if op==1 and source!=2:return done(23)
    if op==7:
        idx=a[23];d=32+16*idx;a[23]=(idx+1)%a[0]
        if a[d+1]!=1 or v[0]<a[d+4]:return done(0,0,idx)
        if a[d+3]!=3:
            off=32+16*a[0]+idx*a[12]//8;a[off:off+a[12]//8]=[0]*(a[12]//8)
        result=0 if a[d+3]==3 else 4
        a[d+1]=2;a[d+14]=result;a[d+15]=v[0]
        return done(0,idx+1,result)
    if op==6:
        for _ in range(32):
            idx=a[22];a[22]=(idx+1)%a[0]
            if a[32+16*idx+1]==2:return done(0,idx+1,a[22])
        return done(0,0,a[22])
    if op==3:
        if not s[16]:
            if source not in (1,2):return done(12)
            a[16]=source;a[17]=0
        slot=a[17]
        if slot>=a[0]:a[16]=a[17]=0;return done()
        d=32+16*slot
        if a[d+1] in (1,2) and (a[16]==2 or a[d+8]):
            if a[d+3]!=3:
                off=32+16*a[0]+slot*a[12]//8;a[off:off+a[12]//8]=[0]*(a[12]//8)
            a[d+1]=2;a[d+14]=5
        a[17]+=1;return done(0,1,a[17])
    slot,gen=v[:2]
    if slot>=s[0]:return done(13)
    d=32+16*slot
    if s[d]!=gen:return done(14)
    payload=32+16*s[0]+slot*s[12]//8
    def wipe():
        if a[d+3]!=3:a[payload:payload+s[12]//8]=[0]*(s[12]//8)
    if op==0:
        kind,now,delay,n,owner,og,auth,lease,lg=v[2:]
        if s[d+1]==4:return done(16)
        if s[d+1]:return done(15)
        if kind>3:return done(12)
        if (slot<s[0]-s[7])!=(kind!=3):return done(13)
        if s[8+kind]>=s[4+kind] or s[1]>=s[3] or s[14]>=s[13]:return done(19)
        if not s[2]:return done(17)
        if n>s[12] or (kind==3 and n):return done(13)
        if auth>1:return done(12)
        delay=delay if kind==3 else s[18+kind]
        if not delay:return done(13)
        if now+delay>MAX:return done(17)
        ident=s[2]
        a[d:d+16]=[gen,1,ident,kind,now+delay,n,owner,og,auth,lease,lg,0,0,0,0,0]
        a[2]=0 if ident==MAX else ident+1
        a[1]+=1;a[8+kind]+=1;a[14]+=1
        return done(0,ident,now+delay,pack(a[d:d+16]))
    if op==1:
        ident,kind,now,result,n=v[2:]
        if s[d+1]!=1 or s[d+2]!=ident or s[d+3]!=kind:return done(14)
        if kind==3 and now<s[d+4]:return done(25)
        if result>3:return done(12)
        outcome=4 if kind!=3 and now>=s[d+4] else result
        if n!=len(body) or n!=s[d+5]:outcome=6
        wipe()
        if outcome==0 and kind!=3:
            padded=body+bytes(s[12]-len(body));a[payload:payload+s[12]//8]=struct.unpack('<'+'Q'*(s[12]//8),padded)
        a[d+1]=2;a[d+14]=outcome;a[d+15]=now
        return done(0,outcome)
    if op in (4,5):
        if s[d+1]!=1 or s[d+2]!=v[2]:return done(14)
        if op==5 and v[3]<s[d+4]:return done(25)
        result=(0 if s[d+3]==3 else 4) if op==5 else 5
        wipe();a[d+1]=2;a[d+14]=result;return done(0,result)
    if s[d+1]!=2:return done(14)
    kind,ident,outcome=s[d+3],s[d+2],s[d+14]
    out=pack(s[d:d+16])+(pack(s[payload:payload+s[12]//8]) if kind!=3 else b'')
    wipe();a[1]-=1;a[8+kind]-=1
    a[d:d+16]=[min(MAX,gen+1),4 if gen==MAX else 0]+[0]*14
    return done(0,ident,outcome,out)


def cases():
    out={f'request-{i}':[] for i in range(8)}
    def case(name,s,v,op,body=b'',source=2):
        a,e,x,y,data=step(s,v,body,op,source)
        f=fixture(name,s,pack(v)+body,e,x,y,a,option=source)
        if data:f['after'][2][8:8+len(data)]=data
        out[f'request-{op}'].append(f);return a
    for kind in range(4):
        slot=kind
        s=fresh();v=[slot,0,kind,10,5,0 if kind==3 else 16,7,8,1,9,10]
        s=case(f'issue-{kind}',s,v,0)
        case('duplicate-issue',s,v,0)
        case('wrong-generation',s,[slot,1,1,kind,11,0,16],1,b'x'*16)
        case('wrong-id',s,[slot,0,2,kind,11,0,16],1,b'x'*16)
        case('network-cannot-complete',s,[slot,0,1,kind,11,0,16],1,b'x'*16,source=0)
        case('kind-spoof',s,[slot,0,1,(kind+1)%4,11,0,16],1,b'x'*16)
        for status,n,at in [(0,v[5],11),(1,v[5],11),(3,v[5],11),(0,0,11),(0,v[5],MAX),(4,v[5],11),(0,MAX,11)]:
            body=b'x'*n if n<=32 else b''
            t=case(f'result-{kind}-{status}-{n}-{at}',s,[slot,0,1,kind,at,status,n],1,body)
            if t[32+16*slot+1]==2:
                case('duplicate-response',t,[slot,0,1,kind,at,status,n],1,body)
                u=case('reap-and-wipe',t,[slot,0],2)
                case('double-reap',u,[slot,0],2)
                case('late-after-release',u,[slot,0,1,kind,at,status,n],1,body)
        case('timer-or-deadline-boundary',s,[slot,0,1,kind,s[32+16*slot+4],0,v[5]],1,b'x'*v[5])
        for now in (MAX-1,MAX):case('deadline-overflow',fresh(),[slot,0,kind,now,5,v[5],7,8,1,9,10],0)
    s=fresh();s[2]=MAX
    s=case('last-id',s,[0,0,0,1,0,0,1,1,0,0,0],0)
    case('id-exhausted',s,[1,0,1,1,0,1,1,1,0,0,0],0)
    s=fresh();s[13]=1
    s=case('action-budget-issue',s,[0,0,0,1,0,0,1,1,0,0,0],0)
    case('action-budget-full',s,[1,0,1,1,0,1,1,1,0,0,0],0)
    s=fresh()
    for kind in range(4):
        s=case(f'cleanup-issued-{kind}',s,[kind,0,kind,0,5,0,7,8,kind%2,0,0],0)
    for mode in (1,2):
        t=s[:]
        for i in range(5):t=case(f'cleanup-mode-{mode}-{i}',t,[],3,source=mode)
    case('cleanup-invalid-mode',fresh(),[],3,source=0)
    for op in (4,5):
        for slot in range(4):
            for now in (0,MAX):
                t=case(f'stop-{op}-{slot}-{now}',s,[slot,0,slot+1,now],op)
                case('late-after-stop',t,[slot,0,slot+1,slot,MAX,0,0],1)
                case('consume-stop',t,[slot,0],2)
    t=s[:]
    for idx in (2,0,3,1):
        t=case(f'out-of-order-{idx}',t,[idx,0,idx+1,idx,5 if idx==3 else 1,0,0],1)
        t=case('discover-ready',t,[],6)
    for idx in range(4):
        t=case('find-next-ready',t,[],6)
        t=case(f'reap-out-of-order-{idx}',t,[idx,0],2)
    case('bounded-empty-ready-scan',t,[],6)
    t=s[:]
    for i in range(8):t=case(f'independent-expiry-{i}',t,[MAX],7)
    for idx in range(4):case('late-response-after-expiry',t,[idx,0,idx+1,idx,MAX,0,0],1)
    return out
