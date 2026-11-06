from cases import fixture,P

def cases():
    fs=[]
    for sid in [*range(16),(1<<62)-4,(1<<62)-1,1<<62,(1<<64)-1]:
        for role in range(3):
            for limit in [0,1,4,1<<60,(1<<60)+1]:
                for direction in range(3):
                    e=0
                    if role>1 or direction>1:e=1
                    elif sid>=1<<62:e=2
                    elif limit>1<<60 or sid//4>=limit:e=15
                    elif sid//2%2 and (sid%2==role)!=bool(direction):e=16
                    out=[e] if e else [0,sid%2,sid//2%2,sid//4,int(sid%2==role)]
                    rs=[[165]*16,[165]*17,[165]*19,[165]*17,[165]*32,[165]*4112]
                    fs.append(fixture(f'id-{len(fs)}',rs,rs,[sid,role,limit,direction,0,0,0,0],out,stack=False,reads=[],writes=[]))
    return fs


def ordinal_cases():
    fs=[]
    for sid in [0,1,2,3,4,7,8, *(1<<i for i in range(62)), (1<<62)-1]:
        rs=[[165]*16,[165]*17,[165]*19,[165]*17,[165]*32,[165]*4112]
        fs.append(fixture(f'ordinal-{sid}',rs,rs,[sid,0,0,0,0,0,0,0],[sid//4],stack=False,reads=[],writes=[]))
    return fs
