from cases import fixture,pack
from limits import MAX


def fresh():
    a=[0]*64
    for i,n in {0:2,8:8,9:16000,10:10,11:3,16:2,17:1,18:4,19:2,20:100,23:4,24:2,25:4,26:8000,28:2048}.items():a[i]=n
    return a


def rotate(w,now,width):
    epoch,d,b,pd,pb=w
    if now-epoch<width:return w[:]
    return [now-now%width,0,0,d if (now-epoch)//width==1 else 0,b if (now-epoch)//width==1 else 0]


def step(s,v):
    a=s[:];slot,now,n,trunc=v
    if slot>=s[0]:return s[:],13,0,0
    off=32+16*slot
    if now<s[6] or now<s[off+5]:return s[:],24,0,0
    g=rotate(s[1:6],now,s[10]);p=rotate(s[off:off+5],now,s[10])
    ok=lambda w,dc,bc:w[1]+w[3]<dc and w[2]+w[4]+n<=bc
    reason=0 if ok(g,s[8],s[9]) and ok(p,s[25],s[26]) else 1
    if s[7]>=s[11]:reason=2
    if n>s[28]:reason=3
    if trunc:reason=4
    for w in (g,p):w[1]=min(MAX,w[1]+1);w[2]=min(MAX,w[2]+n)
    a[1:6]=g;a[off:off+5]=p;a[6]=now;a[off+5]=now;a[7]=min(MAX,s[7]+1)
    if reason:a[12]=min(MAX,a[12]+1);a[off+11]=min(MAX,a[off+11]+1)
    return a,0,int(reason!=0),reason


def ledgers():return [2,0,0,0,10,100,300,500,4,0,0,0,0,0,0,0]+[0,1,0,0,0,0,0,0]+[0,2,1,0,0,0,0,0]


def charge(s,v):
    a=s[:];slot,gen,now,cost,actions=v
    if slot>=s[0]:return a,13,0,0
    d=16+8*slot
    if s[d]!=gen or s[d+1] not in (1,2):return a,14,0,0
    if now<s[1] or now<s[d+3]:return a,24,0,0
    glob=0 if now-s[1]>=s[4] else s[2]
    conn=0 if now-s[d+3]>=s[4] else s[d+4]
    if not cost or glob+cost>s[7] or conn+cost>s[6] or s[3]+cost>s[5] or s[9]+actions>s[8]:return a,19,0,0
    a[2]=glob+cost;a[d+4]=conn+cost;a[3]+=cost;a[9]+=actions
    if now-s[1]>=s[4]:a[1]=now
    if now-s[d+3]>=s[4]:a[d+3]=now
    return a,0,cost,actions


def cases():
    out={'admit':[],'charge':[],'quantum':[]}
    def case(kind,name,s,v,fn):
        a,e,x,y=fn(s,v);out[kind].append(fixture(name,s,pack(v),e,x,y,a));return a
    s=fresh()
    for i,(source,now,n,trunc) in enumerate([(0,0,1200,0),(0,1,1200,1),(1,2,1200,0),(0,3,1200,0),(1,4,MAX,0),(0,9,1,0),(0,10,1,0),(1,19,1,0),(0,20,1,0),(0,40,1,0)]):
        s=case('admit',f'sequence-{i}',s,[source,now,n,trunc],step)
    for n in (0,1,2048,2049,MAX):case('admit',f'size-{n}',fresh(),[0,0,n,0],step)
    for now in (9,10,19,20,21,MAX):
        s=fresh();s[2]=4;s[3]=8000;s[33]=4;s[34]=8000
        case('admit',f'rolling-{now}',s,[0,now,1,0],step)
    s=fresh();s[12]=MAX;s[43]=MAX;s[2]=MAX;s[3]=MAX;s[33]=MAX;s[34]=MAX
    case('admit','saturated',s,[0,0,MAX,0],step)
    case('admit','bad-source',fresh(),[2,0,1,0],step)
    s=fresh();s[6]=10
    case('admit','clock-regression',s,[0,9,1,0],step)
    s=ledgers()
    for cost in (0,1,100,101,MAX):case('charge',f'cost-{cost}',s,[0,0,1,cost,1],charge)
    for actions in (0,4,5,MAX):case('charge',f'actions-{actions}',s,[0,0,1,1,actions],charge)
    s=case('charge','fill-quantum',s,[0,0,1,100,4],charge)
    case('charge','exhausted',s,[1,0,2,1,0],charge)
    def quantum(s,_):
        a=s[:];idx=s[10];a[10]=(idx+1)%s[0];a[3]=a[9]=0
        return a,0,idx,s[16+8*idx+1]
    for i in range(5):s=case('quantum',f'round-robin-{i}',s,[],quantum)
    for now in (9,10,MAX):case('charge',f'window-{now}',s,[0,0,now,100,0],charge)
    s=ledgers();s[2]=500
    case('charge','global-exhausted',s,[0,0,0,1,0],charge)
    s=ledgers();s[20]=300
    case('charge','connection-exhausted',s,[0,0,0,1,0],charge)
    case('charge','stale',s,[0,1,0,1,0],charge)
    return out
