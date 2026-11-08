"""Independent registry lifecycle, borrows, and resumable alias validation."""
from cases import fixture,pack
from limits import MAX


def fresh(n=2):
    return [n,0,0,0,0x200000,0x10000,0x10000,0x70000]+[0]*8+[0]*(8*n)


def step(s,v,op):
    a=s[:]
    def done(e=0,x=0,y=0):return (s[:] if e else a,e,x,y)
    def apart(p,n,q,m):return p+n<=q or q+m<=p
    if op==1:
        if a[8]!=1:return done(14)
        end=min(a[0],a[13]+32)
        for i in range(a[13],end):
            d=16+4*i
            if a[d+3] and (a[d+3]==3 or a[12]) and not apart(a[10],a[11],a[d+1],a[d+2]):
                a[8:15]=[0]*7;return done(0,2,18)
        a[13]=end
        if end<a[0]:return done(0,1,end)
        d=16+4*a[9];a[d:d+4]=[a[14],a[10],a[11],1+2*a[12]]
        a[1]+=1;a[8:15]=[0]*7;return done()
    if op==9:
        start=max(0,a[15]-1);end=min(a[0],start+32)
        for i in range(start,end):
            m=16+4*a[0]+4*i
            if a[m]:a[m]=0;a[2]-=1
        a[15]=end+1 if end<a[0] else 0
        return done(0,int(end<a[0]),end)
    if (a[8] or a[15]) and op not in (4,6,8):return done(15)
    i,g=v[:2]
    if i>=a[0]:return done(13)
    d=16+4*i;m=16+4*a[0]+4*i
    if g!=a[d]:return done(14)
    if op==0:
        b,n,w=v[2:]
        if a[d+3] or any(a[m:m+3]):return done(15)
        if a[m+3]:return done(16)
        if w>1 or n==0 or b+n>MAX:return done(9)
        if not apart(b,n,a[4],a[5]) or not apart(b,n,a[6],a[7]):return done(18)
        a[8:15]=[1,i,b,n,w,0,g];return done(0,1)
    if not a[d+3]:return done(14)
    if op==2:
        if any(a[m:m+3]):return done(15)
        a[d:d+4]=[min(MAX,g+1),0,0,0];a[m+3]=int(g==MAX);a[1]-=1;return done()
    k=(op-3)//2;acquire=op%2==1
    if acquire:
        if a[m+k]:return done(15)
        if k==2:
            if a[d+3]!=3:return done(21)
            if any(a[m:m+3]):return done(15)
        elif a[m+2]:return done(15)
    elif a[m+k]!=1:return done(14)
    a[m+k]=int(acquire)
    if k<2:a[2+k]+=1 if acquire else -1
    return done()


def cases():
    out={f'registry-{op}':[] for op in range(10)}
    def case(name,s,v,op):
        a,e,x,y=step(s,v,op)
        out[f'registry-{op}'].append(fixture(name,s,pack(v),e,x,y,a))
        return a
    s=fresh()
    s=case('stage',s,[0,0,0x300003,101,1],0)
    case('pending-blocks',s,[1,0,0x400000,32,0],0)
    s=case('publish',s,[],1)
    case('resume-twice',s,[],1)
    for op in (3,5,7):
        t=case(f'borrow-{op}',s,[0,0],op)
        case(f'double-borrow-{op}',t,[0,0],op)
        case(f'borrow-blocks-free-{op}',t,[0,0],2)
        for other in (3,5,7):case(f'conflict-{op}-{other}',t,[0,0],other)
        u=case(f'release-{op}',t,[0,0],op+1)
        case(f'double-release-{op}',u,[0,0],op+1)
    t=case('unregister',s,[0,0],2)
    case('double-free',t,[0,0],2)
    case('aba',t,[0,0,0x300000,100,1],0)
    t=case('reuse',t,[0,1,0x300000,100,1],0);case('reuse-publish',t,[],1)
    for base,size,w in [(MAX,1,0),(MAX-1,1,0),(MAX-1,2,0),(0,0,0),(0x200000,8,0),(0x10000,4,0),(0x300003,100,2)]:
        case(f'raw-span-{base}-{size}-{w}',fresh(),[0,0,base,size,w],0)
    t=s[:];t[16]=MAX
    t=case('retire',t,[0,MAX],2)
    case('permanent-retirement',t,[0,MAX,0x400000,8,1],0)
    t=case('overlap-stage',s,[1,0,0x300000,200,0],0);case('overlap-abort',t,[],1)
    t=fresh(65);t=case('large-stage',t,[64,0,0x400000,100,0],0)
    for i in range(3):t=case(f'resume-{i}',t,[],1)
    for op in (0,2,3,4,5,6,7,8):
        case('stale-generation',s,[0,1,0x400000,16,0] if op==0 else [0,1],op)
        case('unknown-slot',s,[2,0,0x400000,16,0] if op==0 else [2,0],op)
    s=fresh(65);s[2]=65
    for i in range(65):s[16+4*65+4*i]=1
    for i in range(3):s=case(f'end-step-{i}',s,[],9)
    return out
