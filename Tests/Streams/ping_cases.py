from dataclasses import replace
from ping_oracle import Ping
from cases import fixture,words,P

PAYLOAD=bytes(range(32))  # Test entropy fixture only, never a runtime generator.

def regions(s,data=b''):
    meta=[s.role,s.phase,len(s.rx),s.deadline,s.gate,s.local_fin,s.remote_fin,s.token]
    body=list(s.rx.ljust(32,b'\0')+s.expected.ljust(32,b'\0'))
    return [[165]*8+words(meta)+body+[165]*8,[165]*25,[165]*27,
            [165]*9+list(data)+[165]*8,[165]*32,[165]*4112]

def suites():
    fs={k:[] for k in ['ping-begin','ping-feed','ping-release','ping-finish','ping-cancel','ping-timer']}
    def add(kind,s,data=b'',now=0,flag=0):
        if kind=='ping-begin':r=s.begin(data,now,flag)
        elif kind=='ping-feed':r=s.feed(data,now,flag)
        elif kind=='ping-release':r=s.release(now)
        elif kind=='ping-finish':r=s.finish()
        else:r=s.cancel(now,kind=='ping-timer')
        e,t,*out=r
        args=[P[0],128,P[3],len(data),0,len(data),now,flag] if kind in ('ping-begin','ping-feed') else [P[0],128,now,0,0,0,0,0]
        fs[kind].append(fixture(f'{kind}-{len(fs[kind])}',regions(s,data),regions(t,data),args,[e,*out]))
        return t
    for role in (0,1):
        for split in range(33):
            s=Ping(role=role)
            if not role:s=add('ping-begin',s,PAYLOAD,flag=1)
            s=add('ping-feed',s,PAYLOAD[:split]);s=add('ping-feed',s,PAYLOAD[split:]) if split<32 else s
            add('ping-feed',s,b'extra');s=add('ping-release',s)
            if not role:s=add('ping-begin',s,PAYLOAD,flag=1)
            s=add('ping-feed',s,PAYLOAD,flag=1);add('ping-release',s)
        s=Ping(role=role)
        if not role:s=add('ping-begin',s,PAYLOAD,flag=1)
        for b in PAYLOAD:s=add('ping-feed',s,bytes([b]))
        s=add('ping-finish',s);add('ping-release',s)
    s=Ping()
    data=PAYLOAD*3
    for i in range(3):
        s=add('ping-feed',s,data,flag=1)
        data=data[32:]
        s=add('ping-release',s)
    assert s.phase==3 and s.local_fin
    s=add('ping-begin',Ping(role=0),PAYLOAD,flag=1)
    add('ping-feed',s,b'',flag=1)
    s=add('ping-finish',s)
    s=add('ping-feed',s,PAYLOAD)
    add('ping-release',s)
    for split in range(33):
        s=add('ping-begin',Ping(role=0),PAYLOAD,flag=1)
        bad=PAYLOAD[:7]+b'X'+PAYLOAD[8:]
        s=add('ping-feed',s,bad[:split]);add('ping-feed',s,bad[split:])
    for n in range(1,32):add('ping-feed',Ping(),PAYLOAD[:n],flag=1)
    add('ping-feed',Ping(),PAYLOAD*3,flag=1);add('ping-feed',Ping(),b'',flag=1)
    for g in range(4):
        s=Ping(role=0,gate=g)
        add('ping-begin',s,PAYLOAD,flag=1);add('ping-feed',s,PAYLOAD);add('ping-finish',s)
    for n in (0,31,33):add('ping-begin',Ping(role=0),PAYLOAD[:n] if n<=32 else PAYLOAD+b'x',flag=1)
    add('ping-begin',Ping(role=0),PAYLOAD,flag=2)
    for s in (Ping(),Ping(phase=3),Ping(rx=b'partial'),Ping(role=0,phase=1,expected=PAYLOAD)):
        add('ping-cancel',s)
        for now in (999,1000,1001):add('ping-timer',s,now=now)
        add('ping-feed',s,b'x',now=1000)
    return fs
