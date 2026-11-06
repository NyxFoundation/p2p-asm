"""Loss, PTO, key and arithmetic boundary timelines through real entry points."""
from oracle import rtt, pto, published_examples

W = 2**64
PN = 2**62


def drain(h, s):
    while s[23]:
        s, _ = h.call('resume', s)
    return s


def packet(s, i):
    start = 64+32*s[4]+20*i
    return s[start:start+20]


def timing(h):
    s = h.init()
    s, _ = h.call('handshake',s,[1,1,1])
    actions = []
    for i in range(4):
        now = 1_000_000+i*3_000_000
        s,a = h.reserve(s,size=80,now=now)
        s = h.sent(s,a,now)
        actions.append(a)
    s = h.ack(s,[(3,3)],110_000_000)
    assert [packet(s,i)[0] for i in range(4)] == [5,3,3,4]
    assert s[55] == 116_500_000
    s,t = h.call('timer',s)
    assert (t[0],t[1],t[3],t[4]) == (11,2,1,116_500_000)
    window = s[72]
    s,_ = h.call('loss',s,[2],now=t[4])
    s = drain(h,s)
    assert packet(s,1)[0] == 5 and s[72] == window
    s = h.ack(s,[(0,1)],120_000_000)
    assert s[70] == 80  # only PN2 remains in flight
    old = tuple(s[76:80])
    s,a = h.reserve(s,size=80,now=200_000_000)
    s = h.sent(s,a,200_000_000)
    s = h.ack(s,[(4,4)],340_000_000,delay=PN-1)
    assert tuple(s[76:80]) == rtt(old,140_000_000,PN-1,3,25_000_000,True,2)


def probes_and_discard(h):
    s = h.init()
    s,t = h.call('timer',s)
    assert t[1] == 1 and t[4] == 999_000_001
    s,_ = h.call('receive',s,[0,1200],now=500_000_000)
    _,same = h.call('timer',s)
    assert same == t  # unrelated received traffic cannot postpone the probe
    s,a = h.call('pto',s,[t[4],t[1]],now=t[4])
    assert a[0] == 12 and s[22] == 1 and s[93] == 2
    s,a = h.reserve(s,space=1,now=s[16],flags=7)
    s = h.sent(s,a,s[16])
    s,t = h.call('timer',s)
    assert t[4] == s[16]+pto(333_000_000,166_500_000,25_000_000,False,1,1)
    s,_ = h.call('discard',s,[1])
    s = drain(h,s)
    assert s[22] == 0 and s[70] == 0 and s[41] == 1
    h.call('keys',s,[1],status=10)
    h.call('ack',s,[1,0,1],ranges=[(0,0)],status=10)


def boundaries(h):
    s = h.init()
    s[48] = PN-1
    s,a = h.reserve(s,now=10)
    assert a[2] == PN-1 and s[48] == PN
    s = h.sent(s,a,10)
    h.call('reserve',s,[2,0,80,3,1,1,2,1],now=100_000_000,status=3)
    s = h.ack(s,[(PN-1,PN-1)],100_000_010)
    s = h.init()
    s[13] = W-1
    h.call('reserve',s,[0,0,80,3,1,1,2,1],status=3)
    s[13] = 1
    h.call('reserve',s,[0,0,80,3,1,1,2,1],now=W-1,status=3)
    s[67] = W-1
    h.call('receive',s,[0,1],status=3)
    h.call('ack',s,[2,0,2],ranges=[(3,4),(2,3)],status=2)
    h.call('ack',s,[2,0,1],ranges=[(PN,PN)],status=2)


def persistent_and_expiry(h):
    s = h.init()
    s,_ = h.call('handshake',s,[1,1,1])
    s,a = h.reserve(s,now=1_000_000,size=80)
    s = h.sent(s,a,1_000_000)
    s = h.ack(s,[(0,0)],101_000_000)
    for now in (1_000_000_000,2_000_000_000,3_000_000_000):
        s,a = h.reserve(s,now=now,size=80)
        s = h.sent(s,a,now)
    s = h.ack(s,[(3,3)],3_100_000_000)
    assert packet(s,1)[0] == packet(s,2)[0] == 5
    s,_ = h.call('persistent',s,[1,2])
    assert s[72] == 2800 and s[77] == s[76]
    h.call('persistent',s,[1,2],status=6)
    s = h.ack(s,[(1,1)],3_100_000_001)
    h.call('persistent',s,[1,2],status=10)
    s = h.init()
    s,a = h.reserve(s,space=0)
    s,_ = h.call('result',s,[0,a[3],1,0],now=2)
    old = packet(s,0)
    s,a = h.call('retry',s,[0],now=3)
    new = packet(s,0)
    assert [old[i] for i in (1,2,3,4,7,8,9,10,13,14)] == [new[i] for i in (1,2,3,4,7,8,9,10,13,14)]
    h.call('result',s,[0,old[11],0,2],now=3,status=6)
    h.call('result',s,[0,a[3],0,2],now=3,status=9)
    s,_ = h.call('ack',s,[0,0,1],now=4,ranges=[(0,0)])
    s,a = h.call('expire',s,[0],now=5_000_000_001)
    assert s[23] == 0 and s[63] == 9 and a[0] == 6 and s[14] == 1


def amplification_and_paths(h):
    s = h.init(server=True)
    s,_ = h.call('receive',s,[0,W-1])
    s,a = h.reserve(s,space=0)
    s = h.sent(s,a,2)
    h.call('timer',s)
    s,_ = h.call('newpath',s,[1,9])
    h.call('reserve',s,[2,1,1200,3,1,1,2,1],status=7)
    h.call('activate',s,[1,9],status=10)
    s,_ = h.call('challenge',s,[1,W-1,10])
    h.call('response',s,[1,9,W-1],now=10,status=8)
    s,_ = h.call('validate',s,[1,9])
    s,_ = h.call('activate',s,[1,9])
    s,t = h.call('timer',s)
    assert t[5] == 0  # outstanding Initial belongs to the previous path
    s,_ = h.call('pto',s,[t[4],t[1]],now=t[4])
    assert s[93] == 2 and s[125] == 0


def resource_and_memory(h):
    words = 64+32*2+20*128+2*64
    budget = 200000+100*words+500*128*2
    args = [9,0,128,2,64,64,128,16,5_000_000_000,2048,budget,3,25_000_000]
    h.call('init',[0]*words,args,now=1)
    args[10] = budget-1
    h.call('init',[0]*words,args,now=1,status=5)
    s = h.init(history=1)
    s,a = h.reserve(s,size=80)
    s = h.sent(s,a,1)
    s = h.ack(s,[(0,0)],100_000_001)
    h.call('reserve',s,[2,0,80,3,1,1,2,1],now=200_000_000,status=5)
    s = h.init()
    h.ack(s,[(0,PN-1)],2,error=12)
    h.call('ack',s,[2,0,5],ranges=[(8,8),(6,6),(4,4),(2,2),(0,0)],status=5)
    for d in ({0:0x300009},{2:W-8},{4:0x300008},{6:0x300008},{5:63},{7:0},{1:511}):
        status = 5 if 5 in d or 7 in d else 4
        h.call('timer',s,status=status,descriptor=d)
    h.call('timer',s,status=4,register_overrides={10:0x500009})
    h.call('timer',s,status=4,register_overrides={2:0x600401})
    s,a = h.reserve(s,space=0)
    for now in (2,4,6):
        s,_ = h.call('result',s,[0,a[3],1,0],now=now)
        if now < 6:
            s,a = h.call('retry',s,[0],now=now+1)
    h.call('retry',s,[0],now=7,status=8)
    s,a = h.call('expire',s,[0],now=7)
    assert s[14] == 0 and s[87] == 1 and a[0] == 5


def result_order(h):
    s = h.init()
    s,a = h.call('reserve',s,[0,0,1200,3,1,1,9001,1],now=2)
    s,b = h.call('reserve',s,[1,0,1200,3,2,1,9002,1],now=3)
    h.ack(s,[(0,0)],4,space=1,error=12)
    s,_ = h.call('result',s,[b[1],b[3],0,10],now=20)
    s,_ = h.call('result',s,[a[1],a[3],0,9],now=21)
    assert s[83] == 10 and s[35] == 9 and s[43] == 10
    s = h.ack(s,[(0,0)],100_000_009,space=0)
    assert s[70] == 1200
    s = h.ack(s,[(0,0)],100_000_010,space=1)
    assert s[70] == 0


def run(h):
    published_examples()
    timing(h)
    probes_and_discard(h)
    boundaries(h)
    persistent_and_expiry(h)
    amplification_and_paths(h)
    resource_and_memory(h)
    result_order(h)
