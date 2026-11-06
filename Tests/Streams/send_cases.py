from send_oracle import Send
from cases import fixture,words,P
from oracle import MAX,NONE

def regions(s,payload=b''):
    pending=list(s.pending or (0,0,0))+[int(s.pending is not None)]
    m=[s.cap,P[1],P[2],s.base,s.queued,s.sent,s.limit,s.allowance,s.final,
       s.fin_sent,s.fin_ack,s.reset]+pending
    data,tags=[0]*s.cap,[0]*s.cap
    for k,v in s.data.items(): data[k%s.cap]=v
    for k in s.acked: tags[k%s.cap]=1
    return [[165]*8+words(m)+[165]*8,[165]*9+data+[165]*8,
            [165]*11+tags+[165]*8,[165]*9+list(payload)+[165]*8,[165]*32,[165]*4112]

def call(kind,s,args=(),payload=b'',label=''):
    if kind=='append':
        e,t=s.append(payload,*args)
        a=[P[0],128,P[3],len(payload),0,len(payload),*args,0]
        out=[e]
    elif kind=='reserve':
        e,t,d=s.reserve(*args)
        a=[P[0],128,*args,0,0,0]
        off,n,_=args
        first=min(n,s.cap-off%s.cap)
        out=[e,d,off%s.cap if not e else 0,first if not e else 0,n-first if not e else 0]
    elif kind=='settle':
        e,t,d=s.settle(*args);a=[P[0],128,*args,0,0,0,0,0]
        out=[e,d,0,0,args[0] if not e else 0]
    elif kind=='ack':
        e,t=s.ack(*args);a=[P[0],128,*args,0,0,0]
        out=[e,t.base-s.base,0,0,0]
    else:
        e,t=s.stop();a=[P[0],128,0,0,0,0,0,0];out=[e,0,0,0,2 if not e else 0]
    return fixture(label or f'{kind}-{args}',regions(s,payload),regions(t,payload),a,out),t

def suites():
    fs={k:[] for k in ['append','reserve','settle','ack','stop']}
    def run(kind,s,args=(),payload=b''):
        f,t=call(kind,s,args,payload,label=f'{kind}-{len(fs[kind])}')
        fs[kind].append(f);return t
    for cap in (1,3,8):
        for base in (0,cap-1,MAX-cap):
            s=Send(cap=cap,base=base,queued=base,sent=base)
            for n in range(cap+2):
                for fin in (0,1,2): run('append',s,(fin,),bytes(range(n)))
            s=run('append',s,(1,),bytes(range(cap)))
            run('append',s,(0,),b'x')
            for off in (base,base+1):
                for n in range(cap+2):
                    for fin in (0,1):run('reserve',s,(off,n,fin))
            p=run('reserve',s,(base,cap,1))
            run('reserve',p,(base,0,0));run('stop',p)
            run('settle',p,(0,));s=run('settle',p,(1,));run('settle',s,(1,))
            for off in range(cap+1):
                for n in range(cap+2-off):
                    for fin in (0,1):run('ack',s,(base+off,n,fin))
            p=run('reserve',s,(base,cap,1))
            p=run('ack',p,(base,cap,1));run('settle',p,(0,));run('settle',p,(1,))
            s=run('ack',s,(base+cap//2,cap-cap//2,1))
            s=run('ack',s,(base,cap//2,0));run('ack',s,(base,cap,1));run('stop',s)
    s=Send()
    s=run('append',s,(0,),b'abcdefgh')
    s=run('reserve',s,(0,4,0));s=run('settle',s,(1,))
    s=run('ack',s,(0,4,0));s=run('append',s,(1,),b'ijkl')
    s=run('reserve',s,(4,8,1));s=run('settle',s,(1,));s=run('ack',s,(4,8,1))
    for limit,allow in [(2,MAX),(MAX,2)]:
        s=Send(limit=limit,allowance=allow)
        s=run('append',s,(0,),b'abc');run('reserve',s,(0,3,0))
    s=run('append',Send(),(1,),b'');s=run('reserve',s,(0,0,1))
    s=run('settle',s,(1,));run('ack',s,(0,0,1))
    return fs

def permutation_suites():
    from itertools import permutations
    fs={k:[] for k in ['append','reserve','settle','ack','stop']}
    def run(kind,s,args=(),payload=b''):
        f,t=call(kind,s,args,payload,label=f'permutation-{kind}-{len(fs[kind])}')
        fs[kind].append(f);return t
    for order in permutations([(0,2,0),(2,2,0),(4,2,1)]):
        s=run('append',Send(cap=6),(1,),b'abcdef')
        s=run('reserve',s,(0,6,1));s=run('settle',s,(1,))
        for ack in order:
            s=run('ack',s,ack);s=run('ack',s,ack)
        assert s.base==6 and s.fin_ack
    s=run('append',Send(),(1,),b'abcdefgh')
    for off,n in [(0,3),(3,3),(6,2)]:
        s=run('reserve',s,(off,n,int(off+n==8)));s=run('settle',s,(1,))
    for off,n in [(3,3),(0,2),(1,6),(6,2)]:
        p=run('reserve',s,(off,n,int(off+n==8)))
        run('settle',p,(0,));s=run('settle',p,(1,))
    s=run('ack',s,(2,6,1));s=run('ack',s,(0,2,0))
    return fs
