from cases import fixture,pack
from admission import fresh as ingress
from limits import MAX


def fresh():
    a=[0]*160;a[0]=2;a[10]=256;a[11]=1024
    a[32:96]=ingress();a[128]=2
    return a


def starts(w,now,width):
    e,n,p=w
    return w[:] if now-e<width else [now-now%width,0,n if (now-e)//width==1 else 0]


def step(s,v,op):
    a=s[:]
    def done(e=0,x=0,y=0):return (s[:] if e else a,e,x,y)
    if op==0 and s[20]:return done(15)
    if s[0]!=2:return done(14)
    g=s[10]//8;l=s[11]//8;slot,gen=v[:2]
    if slot>=s[l]:return done(13)
    d=l+16+8*slot
    if s[d]!=gen:return done(14)
    phase=s[d+1]
    if not op:
        if phase==3:return done(16)
        if phase:return done(15)
    elif phase not in (1,2):return done(14)
    source=v[2] if not op else s[d+2]
    if source>=s[g]:return done(13)
    p=g+32+16*source
    if not op:
        now=v[3]
        if now<s[g+6]:return done(24)
        if any(s[i]>=s[j] for i,j in [(g+22,g+23),(p+10,g+24),(g+21,g+16),(p+9,g+17)]):return done(19)
        if now<s[g+13] or now<s[p+6]:return done(24)
        gs=starts(s[g+13:g+16],now,s[g+20]);ps=starts(s[p+6:p+9],now,s[g+20])
        if gs[1]+gs[2]>=s[g+18] or ps[1]+ps[2]>=s[g+19]:return done(19)
        gs[1]+=1;ps[1]+=1;a[g+13:g+16]=gs;a[p+6:p+9]=ps
        for i in [g+22,p+10,g+21,p+9]:a[i]+=1
        a[d+1:d+8]=[1,source,now,0,0,0,0]
        return done(0,slot,gen)
    if op==1 and phase!=1:return done(14)
    if phase==1:a[g+21]-=1;a[p+9]-=1
    if op==1:a[d+1]=2;return done()
    a[g+22]-=1;a[p+10]-=1;a[d:d+8]=[min(MAX,gen+1),3 if gen==MAX else 0]+[0]*6
    return done()


def cases():
    out={f'connection-{i}':[] for i in range(4)}
    def case(name,s,v,op):
        a,e,x,y=step(s,v,op);out[f'connection-{op}'].append(fixture(name,s,pack(v),e,x,y,a));return a
    s=fresh();s=case('new-quota-lease',s,[0,0,0,0],0)
    case('same-source-concurrent-quota',s,[1,0,0,0],0)
    t=case('other-source',s,[1,0,1,0],0)
    s=case('release-handshake-quota',s,[0,0],1)
    case('double-handshake-release',s,[0,0],1)
    s=case('new-connection-same-source',s,[1,0,0,1],0)
    t=case('release-still-handshaking',t,[1,0],2)
    case('double-release',t,[1,0],2)
    s=case('release-open-connection',s,[0,0],2)
    case('stale-aba',s,[0,0,0,2],0)
    case('start-rate-full',s,[0,1,0,2],0)
    for now in (99,100,199,200,MAX):
        u=fresh();u[32+14]=4;u[32+32+7]=2
        case(f'rolling-start-{now}',u,[0,0,0,now],0)
    u=fresh();u[144]=MAX;u=case('last-generation-allocate',u,[0,MAX,0,0],0)
    u=case('retire-generation',u,[0,MAX],2);case('retired-unavailable',u,[0,MAX,0,0],0)
    for mode in (1,2):
        s,_e,_x,_y=step(fresh(),[0,0,0,0],0)
        s,_e,_x,_y=step(s,[1,0,1,0],0)
        s,_e,_x,_y=step(s,[1,0],1)
        for i in range(3):
            a=s[:];data=b''
            if not a[20]:a[20]=mode;a[21]=0
            idx=a[21];l=a[11]//8
            if idx>=a[l]:a[20]=a[21]=0;x=y=0
            else:
                a[21]+=1;d=l+16+idx*8;phase=a[d+1];x=1;y=idx
                if phase in (1,2) and (mode==2 or phase==1):
                    data=pack([idx,a[d],a[d+2],phase]);a,e,_,_=step(a,[idx,a[d]],2);assert not e;x=2
            f=fixture(f'cleanup-{mode}-{i}',s,b'',0,x,y,a,option=mode)
            if data:f['after'][2][8:8+len(data)]=data
            out['connection-3'].append(f);s=a
    return out
