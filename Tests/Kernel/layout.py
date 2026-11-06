from limits import DEFAULT,validate,reserved,MAX
from cases import fixture,pack


def layout(v,allocated):
    e=validate(v)
    if e:return e,[]
    req=v[30]+v[32]+v[33];stride=(v[10]+7)//8*8
    sizes=[128+64*v[60],256+128*(req+v[31])+stride*req,256+128*v[4],128+64*v[0],64+256*v[34],64+256*v[35],192]
    offs=[1024]
    for n in sizes:offs.append(offs[-1]+n)
    if offs[-1]>v[58] or v[58]%16:return 22,[]
    conn=v[0]*(v[56]+v[57]+2*v[19]+v[16]*(v[17]+v[18]))
    data=v[58]+conn;events=(data+(v[15]+v[30])*v[10]+15)//16*16
    stack=events+v[27]*256;used=stack+v[59]
    if used>min(v[55],allocated,MAX) or v[51]<1000000:return 22,[]
    return 0,offs[:7]+[v[58],data,events,stack,used]


def small():
    v=DEFAULT[:]
    changes={0:1,1:1,2:1,3:1,4:1,5:1,6:1,10:1200,11:1,13:2,14:2400,15:1,16:3,17:1024,18:1024,19:4096,
      27:17,28:15,29:1,30:1,31:12,32:1,33:1,34:1,35:1,49:4096,50:4096,55:65536,56:8,57:8,58:16384,59:256,60:2}
    for i,n in changes.items():v[i]=n
    assert validate(v)==0
    return v


def headers(a):
    v=a[64:125]
    def put(table,fields):
        start=a[8+table]//8
        for i,n in fields.items():a[start+i]=n
    put(0,{0:v[60],4:0x200008,5:a[1],6:a[5],7:a[6]})
    put(1,{0:sum(v[i] for i in (30,31,32,33)),2:1,3:v[28],4:v[30],5:v[32],6:v[33],7:v[31],12:(v[10]+7)//8*8,13:v[35],18:v[38],19:v[40],20:v[41]})
    put(2,{0:v[4],8:v[13],9:v[14],10:v[12],11:v[11],16:v[2],17:v[3],18:v[5],19:v[6],20:v[7],23:v[0],24:v[1],28:v[10],25:max(1,v[13]//v[4]),26:max(v[10],v[14]//v[4])})
    put(3,{0:v[0],4:v[54],5:v[51],6:v[52],7:v[53],8:v[35]})
    put(4,{0:v[34],4:3,5:64});put(5,{0:v[35],4:4,5:64})
    q=a[14]//8;data=a[17]
    for k,c in enumerate((v[15],v[29],v[28])):
        a[q]=c;a[q+4]=k;a[q+5]=data-q*8;q+=8;data+=c*256


def cases():
    out={'init-begin':[],'init-resume':[]}
    v=small();_,d=layout(v,65536)
    size=(d[-1]+7)//8*8
    s=[0xabababababababab]*(size//8)
    # The main arena ABI requires 16-byte alignment; fixtures normally start at +8.
    def f(name,s,inp,e,x,y,a):
        item=fixture(name,s,inp,e,x,y,a,option=0x10000,budget=0x70000)
        # Move the state to base+16 without changing its contents.
        item['regions'][0]=[71]*16+list(pack(s))+[71]*8
        item['after'][0]=[71]*16+list(pack(a))+[71]*8
        item['args'][0]=0x200010
        return item
    e,d=layout(v,size);assert e==0
    a=s[:];a[:128]=[0]*128;a[0:7]=[1,d[-1],1024,0,size,0x10000,0x70000]
    a[3]=d[6]+192;a[8:20]=d;a[64:125]=v
    out['init-begin'].append(f('begin-validated',s,pack(v),0,1,1024,a))
    s=a
    while s[2]<s[1]:
        a=s[:];end=min(s[1],s[2]+4096);a[s[2]//8:end//8]=[0]*((end-s[2])//8);a[2]=end
        more=end<s[1]
        if not more:
            headers(a);a[a[8]//8+4]=0x200010;a[0]=2
        out['init-resume'].append(f(f'clear-{s[2]}',s,b'',0,int(more),end,a));s=a
    for idx,n in [(58,1),(58,16385),(55,1),(51,999999),(60,MAX)]:
        bad=v[:];bad[idx]=n;e,_=layout(bad,size)
        out['init-begin'].append(f(f'bad-layout-{idx}',s,pack(bad),e,0,0,s))
    out['init-resume'].append(f('resume-ready',s,b'',14,0,0,s))
    return out
