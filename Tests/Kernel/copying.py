from cases import fixture,pack
from registry import fresh


def cases():
    result=[]
    for n in [0,1,7,16,223,224,488,489]:
        s=fresh();s[1]=1;s[2]=1;s[16:20]=[0,0x230003,n+1,1];s[24]=1
        source=bytes((i*13+7)%256 for i in range(n+8))
        e=11 if n>488 else 0
        f=fixture(f'copy-{n}',s,pack([0,0,0,n]),e,n if not e else 0,0,s)
        f['regions'][3]=list(source);f['after'][3]=list(source)
        f['extraReads']=[[0x230003,n]] if not e else []
        if not e:f['after'][2][8:8+n]=source[3:3+n]
        result.append(f)
    return result
