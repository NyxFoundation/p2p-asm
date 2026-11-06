from dataclasses import replace
from copy import deepcopy
from cases import fixture,words,P,recv_regions,rx
from oracle import Receive
from multistream_oracle import Negotiation,metadata,frame,HEADER,PING,NA
from multistream_cases import regions as neg_regions,call as neg_call
from send_oracle import Send
from send_cases import call as send_call
from ping_oracle import Ping
from ping_cases import regions as ping_regions,PAYLOAD


def emit_cases():
    fs=[]
    for kind in range(5):
        for cap in [0,1,3,4,17,18,19,20,37,38,64]:
            data=[frame(HEADER),frame(HEADER)+frame(PING),frame(PING),frame(NA)][min(kind,3)]
            rs=[[165]*(cap+16),[165]*17,[165]*19,[165]*17,[165]*32,[165]*4112]
            after=deepcopy(rs);e=1 if kind>3 else 6 if cap<len(data) else 0
            if not e:after[0][8:8+len(data)]=data
            fs.append(fixture(f'emit-{kind}-{cap}',rs,after,[P[0],cap,kind,0,0,0,0,0],
                              [e,0 if e else len(data)],stack=False,reads=[],writes=[] if e else [[P[0],len(data)]]))
    return fs


def timer_cases():
    fs=[]
    for phase in range(4):
        for now in (0,999,1000,1001,(1<<64)-1):
            s=Negotiation(phase=phase,pending=b'\x13/mul' if phase<2 else b'')
            expired=phase<2 and now>=s.deadline
            t=replace(s,phase=3,pending=b'') if expired else s
            fs.append(fixture(f'neg-timer-{phase}-{now}',neg_regions(s,b''),neg_regions(t,b''),
                              [P[0],120,now,0,0,0,0,0],[0,0,0,0,int(expired)]))
    return fs


def quota_cases():
    fs=[]
    for outbound in range(3):
        for inbound in range(4):
            for role in range(3):
                for acquire in range(3):
                    counts=[outbound,inbound];after=counts[:];e=0;n=0
                    if outbound>1 or inbound>2 or role>1 or acquire>1:e=1
                    elif (not acquire and not counts[role]) or (acquire and counts[role]>=role+1):e=8
                    else:after[role]+=1 if acquire else -1;n=after[role]
                    rs=[[165]*8+words(counts)+[165]*8,[165]*17,[165]*19,[165]*17,[165]*32,[165]*4112]
                    out=deepcopy(rs);out[0][8:24]=words(after)
                    fs.append(fixture(f'quota-{outbound}-{inbound}-{role}-{acquire}',rs,out,
                                      [P[0],16,role,acquire,0,0,0,0],[e,n]))
    return fs


def metadata_cases():
    s=Receive();recv,_=rx('valid',s,0,b'ab')
    app,_=send_call('append',Send(),(0,),b'ab')
    neg,_,_=neg_call(Negotiation(),frame(HEADER))
    p=Ping(role=0)
    ping=fixture('valid',ping_regions(p,PAYLOAD),ping_regions(p,PAYLOAD),
                 [P[0],128,P[3],32,0,32,0,1],[0])
    result={}
    for kind,baseline,size in [('receive',recv,80),('append',app,128),('negotiate',neg,120),('ping-begin',ping,128)]:
        fs=[]
        for slot,val,stack in [(1,0,False),(1,size-1,False),(0,P[0]+1,False),
                              (1,(1<<64)-1,False),(3,1,True),(4,(1<<64)-1,True),
                              (2,(1<<64)-1,True),(5,(1<<64)-1,True)]:
            f=deepcopy(baseline);f['label']=f'metadata-{kind}-{slot}-{val}'
            f['args'][slot]=val;f['outputs']=[1,0,0,0,0]
            f['expectedRegions']=deepcopy(f['regions']);f['stackUsed']=stack
            if stack:
                f['expectedRegions'][5][3968:4096]=[0]*128
                f['writes']=[[P[5]-128,128]]
            else:f['reads']=[];f['writes']=[]
            fs.append(f)
        f=deepcopy(baseline);f["label"]=f"nonzero-source-view-{kind}"
        source=f["regions"][3][9:-8]
        f["regions"][3]=[165]*9+list(b"prefix!")+source+list(b"suffix!")+[165]*8
        f["expectedRegions"][3]=f["regions"][3][:]
        f["args"][3]=len(source)+14;f["args"][4]=7
        f["reads"]=[r for r in f["reads"] if r[0]!=P[3]]+[[P[3]+7,len(source)]]
        if kind!="ping-begin":fs.append(f)
        result[kind]=fs
    return result


def large_receive_cases():
    fs=[]
    for cap in (257,4097):
        for base in (0,1000000000):
            s=Receive(cap=cap,base=base,highest=base)
            f,s=rx(f'large-cap-{cap}-{base}',s,base+cap-1,b'Z');fs.append(f)
    return fs

def overlap_cases():
    from itertools import permutations
    fs=[]
    for order in permutations([(0,b'ab'),(2,b'cd'),(4,b'ef')]):
        s=Receive(cap=6)
        for off,p in order:
            f,s=rx(f'reorder-{len(fs)}',s,off,p);fs.append(f)
            f,s=rx(f'duplicate-{len(fs)}',s,off,p);fs.append(f)
        for i in range(6):
            bad=bytearray(b'abcdef');bad[i]^=255
            f,_=rx(f'conflict-position-{len(fs)}',s,0,bytes(bad));fs.append(f)
        assert bytes(s.data[i] for i in range(6))==b'abcdef'
    return fs
