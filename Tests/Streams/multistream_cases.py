from multistream_oracle import Negotiation,frame,HEADER,PING,NA,metadata
from cases import fixture,words,P

def regions(s,data):
    return [[165]*8+words(metadata(s))+[165]*8,[165]*25,[165]*27,
            [165]*9+list(data)+[165]*8,[165]*32,[165]*4112]

def call(s,data,now=0,label=''):
    e,t,used,action,selected=s.feed(data,now)
    f=fixture(label,regions(s,data),regions(t,data),
              [P[0],120,P[3],len(data),0,len(data),now,0],[e,used,action,selected,0])
    return f,t,used

def cases():
    fs=[]
    def add(s,data,now=0):
        f,t,u=call(s,data,now,f'negotiation-{len(fs)}');fs.append(f);return t,u
    wire=frame(HEADER)+frame(PING)+bytes(range(32))
    for role in (0,1):
        for split in range(len(wire)+1):
            s=Negotiation(role=role)
            for data in (wire[:split],wire[split:]):
                while data and s.phase!=2:
                    s,u=add(s,data)
                    assert u
                    data=data[u:]
            assert s.phase==2
        s=Negotiation(role=role)
        for b in wire[:len(frame(HEADER)+frame(PING))]:s,_=add(s,bytes([b]))
        add(s,b'leftover')
    s,_=add(Negotiation(),frame(HEADER))
    for p in [b'/\xc2\x80\n', b'/\xdf\xbf\n', b'/\xe0\xa0\x80\n',
              b'/\xed\x9f\xbf\n', b'/\xee\x80\x80\n', b'/\xf0\x90\x80\x80\n',
              b'/\xf4\x8f\xbf\xbf\n', b'ls\n',b'/unknown\n',b'/\xe3\x81\x82\n',HEADER,b'x'*200+b'\n']:
        for split in range(len(frame(p))+1):
            t,_=add(s,frame(p)[:split]);add(t,frame(p)[split:])
    for p in [b'\x80\0',b'\x80'*9,b'\0',frame(b'bad'),frame(b'bad\nmore\n'),
              frame(b'\xc0\x80\n'),frame(b'\xed\xa0\x80\n'),frame(b'\xf4\x90\x80\x80\n'),
              frame(b'\xe0\x80\x80\n'),frame(b'\xf0\x80\x80\x80\n'),frame(b'\xff\n'),
              frame(b'\xe3\n'),frame(b'\x80\n')]:
        add(s,p)
    for raw in [frame(b"\xed\xa0\x80\n"), frame(b"\xf4\x90\x80\x80\n"), frame(b"a\nb\n")]:
        for split in range(len(raw)+1):
            f,t,u=call(s,raw[:split],label=f"bad-prefix-{len(fs)}");fs.append(f)
            if not f["outputs"][0]:add(t,raw[split:])
    add(Negotiation(limit=3),frame(HEADER));add(s,b'\x81\x08')
    for i in range(s.max_proposals+1):s,_=add(s,frame(NA))
    add(Negotiation(),frame(HEADER),1000);add(Negotiation(),b'',1001)
    return fs
