from cases import fixture,pack
from registry import fresh as registry_fresh,step as registry_step
from requests import fresh as request_fresh,step as request_step
from limits import MAX


def fresh():
    reg=registry_fresh();reg[1]=1;reg[16:20]=[0,0x300003,101,3]
    req=request_fresh()
    root=[0]*128;root[0]=2;root[8]=1024;root[9]=1024+len(reg)*8;root[10]=root[9]+len(req)*8
    return root+reg+req


def slices(s):
    r0,r1,r2=(s[i]//8 for i in (8,9,10))
    return r0,r1,r2,s[r0:r1],s[r1:r2]


def owned(s,v,op):
    a=s[:];r0,r1,r2,reg,req=slices(s)
    if s[0]!=2:return s[:],14,0,0,b''
    if op==0 and v[2]==0:
        reg,e,_,_=registry_step(reg,v[9:11],5)
        if e:return s[:],e,0,0,b''
    req,e,x,y,data=request_step(req,v,b'',2 if op else 0)
    if e:return s[:],e,0,0,b''
    if op:
        import struct
        words=struct.unpack('<16Q',data[:128])
        if words[3]==0:reg,e,_,_=registry_step(reg,list(words[9:11]),6);assert e==0
    a[r0:r1]=reg;a[r1:r2]=req
    return a,0,x,y,data


def cases():
    out={'owned-issue':[],'owned-reap':[],'resolve':[],'kernel-quantum':[]}
    def case(name,s,v,op):
        a,e,x,y,data=owned(s,v,op)
        f=fixture(name,s,pack(v),e,x,y,a);f['stackDepth']=512;f['after'][5][-512:]=bytes(512)
        if data:f['after'][2][8:8+len(data)]=data
        out['owned-reap' if op else 'owned-issue'].append(f);return a
    s=fresh();v=[0,0,0,10,0,0,7,8,1,0,0]
    t=case('owned-send-reserve',s,v,0)
    case('duplicate-owned-send',t,v,0)
    u=fresh();u[u[9]//8+2]=0
    case('issue-failure-rolls-lease-back',u,v,0)
    u=fresh();u[u[9]//8+14]=4
    case('action-pressure-rolls-lease-back',u,v,0)
    r0,r1,r2,reg,req=slices(t)
    for outcome in (0,1,2,3):
        done,e,_,_,_=request_step(req,[0,0,1,0,11,outcome,0],b'',1);assert e==0
        a=t[:];a[r1:r2]=done
        b=case(f'owned-result-release-{outcome}',a,[0,0],1)
        case('stale-owned-reap',b,[0,0],1)
    for write,lease in [(0,0),(0,1),(1,0),(1,1)]:
        reg=registry_fresh();reg[1]=1;reg[16:20]=[5,MAX-101,101,3]
        reg[16+4*2+(2 if write else 0)]=lease
        for slot,gen,off,n in [(0,5,101,0),(0,5,0,101),(0,5,100,2),(0,4,0,1),(2,0,0,0),(0,5,MAX,1)]:
            status=1 if slot>=2 else 2 if gen!=5 else 3 if n>101 or off>101-n else 15 if not lease else 0
            out['resolve'].append(fixture(f'resolve-{write}-{lease}-{slot}-{gen}-{off}-{n}',reg,pack([slot,gen,off,n]),
                status,MAX-101+off if not status else 0,n if not status else 0,reg,option=write))
    from admission import fresh as ingress,ledgers
    s=fresh();s[11]=len(s)*8+len(ingress())*8;s+=ingress()+ledgers();s[12]=len(s)*8
    r=s[8]//8;q=s[9]//8;g=s[10]//8;l=s[11]//8
    s[q+14]=4;s[g+7]=8;s[l+3]=100;s[l+9]=4
    for i in range(16):
        a=s[:];idx=s[l+10];lane=s[22];a[q+14]=a[g+7]=a[l+3]=a[l+9]=0
        if lane==2:a[l+10]=(idx+1)%a[l]
        a[22]=(lane+1)%5
        out['kernel-quantum'].append(fixture(f'kernel-quantum-{i}',s,b'',0,idx,lane,a));s=a
    for field in (r+2,r+15):
        a=s[:];a[field]=1
        out['kernel-quantum'].append(fixture('borrow-must-expire-before-next-step',a,b'',15,0,0,a))
    return out
