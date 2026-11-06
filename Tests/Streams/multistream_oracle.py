"""Pinned-wire messages; Python's strict UTF-8 decoder is the independent oracle."""
from dataclasses import dataclass,replace
import codecs
HEADER=b'/multistream/1.0.0\n'
PING=b'/ipfs/ping/1.0.0\n'
NA=b'na\n'

def frame(x):
    n=len(x);prefix=[]
    while n>=128: prefix.append((n&127)|128);n>>=7
    return bytes(prefix+[n])+x

@dataclass
class Negotiation:
    limit:int=1024
    max_proposals:int=8
    proposals:int=0
    role:int=1
    phase:int=0
    pending:bytes=b''
    deadline:int=1000

    def feed(self,data,now=0):
        if now>=self.deadline: return 10,self,0,0,0
        if self.phase==3:return 9,self,0,0,0
        if self.phase==2:return 0,self,0,0,1
        buf=self.pending
        for used,byte in enumerate(data,1):
            buf+=bytes([byte])
            e,n,start=prefix(buf)
            if e:return e,self,0,0,0
            if start is None:continue
            if not 0<n<=self.limit:return 13,self,0,0,0
            body=buf[start:]
            try:
                decoder=codecs.getincrementaldecoder('utf-8')()
                decoder.decode(body,final=len(body)==n)
                tail=decoder.getstate()[0]
                if tail:
                    width=2 if tail[0]<224 else 3 if tail[0]<240 else 4
                    fill=bytes([160 if tail[0]==224 else 144 if tail[0]==240 else 128]) if len(tail)==1 else b''
                    (tail+fill+b'\x80'*(width-len(tail)-len(fill))).decode('utf-8')
            except UnicodeDecodeError:return 13,self,0,0,0
            if b'\n' in body[:-1] or (body.endswith(b'\n') and len(body)!=n):
                return 13,self,0,0,0
            if len(body)<n:continue
            if not body.endswith(b'\n'):return 13,self,0,0,0
            if self.phase==0:
                if body!=HEADER:return 13,self,0,0,0
                return 0,replace(self,phase=1,pending=b''),used,0,0
            if self.role==0:
                if body!=PING:return 9 if body==NA else 13,self,0,0,0
                return 0,replace(self,phase=2,pending=b''),used,0,1
            if self.proposals>=self.max_proposals:return 14,self,0,0,0
            chosen=body==PING
            return 0,replace(self,phase=2 if chosen else 1,proposals=self.proposals+1,pending=b''),used,2 if chosen else 3,int(chosen)
        return 0,replace(self,pending=buf),len(data),0,0

def prefix(buf):
    n=0
    for i,b in enumerate(buf[:9]):
        n|=(b&127)<<(7*i)
        if b<128:
            if i and b==0:return 13,0,None
            return 0,n,i+1
    if len(buf)>=9:return 13,0,None
    return 0,n,None

def utf_state(bs):
    remain,lo,hi=0,128,191
    for b in bs:
        if remain:
            remain-=1;lo,hi=128,191
        elif b>=128:
            if b<224:remain=1
            elif b<240:
                remain=2;lo=160 if b==224 else 128;hi=159 if b==237 else 191
            else:
                remain=3;lo=144 if b==240 else 128;hi=143 if b==244 else 191
    return remain,lo,hi

def metadata(s):
    _,n,start=prefix(s.pending)
    if start is None:
        parser=[n,len(s.pending)*7,0,0,0,0,128,191,0]
    else:
        body=s.pending[start:];pos=len(body)
        mask=sum(bit for bit,msg in [(1,HEADER),(2,PING),(4,NA)] if len(msg)==n and msg.startswith(body))
        parser=[n,0,n-pos,pos,mask,*utf_state(body),1]
    return [s.limit,s.max_proposals,s.proposals,s.role,s.phase,*parser,s.deadline]
