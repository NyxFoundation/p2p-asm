from dataclasses import dataclass,replace

@dataclass
class Ping:
    role:int=1
    phase:int=0
    rx:bytes=b''
    expected:bytes=b''
    deadline:int=1000
    gate:int=3
    local_fin:int=0
    remote_fin:int=0
    token:int=1

    def begin(self,data,now,token):
        if self.gate!=3:return 11,self,0,0,0,0
        if now>=self.deadline:return 10,self,0,0,0,0
        if len(data)!=32 or token!=self.token or self.role!=0:return 1,self,0,0,0,0
        if self.phase or self.local_fin or self.remote_fin:return 9,self,0,0,0,0
        return 0,replace(self,phase=1,expected=data),0,96,32,1

    def feed(self,data,now=0,fin=0):
        if self.gate!=3:return 11,self,0,0,0,0
        if now>=self.deadline:return 10,self,0,0,0,0
        if fin not in (0,1):return 1,self,0,0,0,0
        if self.phase==3 or self.remote_fin:return 9,self,0,0,0,0
        if self.role and self.local_fin:return 9,self,0,0,0,0
        if self.phase==2:return 8,self,0,0,0,0
        if self.role==0 and self.phase!=1:return 8,self,0,0,0,0
        n=min(len(data),32-len(self.rx));rx=self.rx+data[:n]
        ended=fin and n==len(data)
        if ended and len(rx) not in (0,32):return 13,self,0,0,0,0
        if len(rx)==32 and self.role==0 and rx!=self.expected:return 12,self,0,0,0,0
        if ended and not rx and not self.role:return 13,self,0,0,0,0
        if ended and not rx:
            return 0,replace(self,phase=3,local_fin=1,remote_fin=1),0,0,0,3
        ready=len(rx)==32
        t=replace(self,rx=rx,phase=2 if ready else self.phase,remote_fin=int(ended))
        return 0,t,n,64 if ready and self.role else 0,32 if ready and self.role else 0,(1 if self.role else 2) if ready else 0

    def release(self,now=0):
        if self.gate!=3:return 11,self,0,0,0,0
        if now>=self.deadline:return 10,self,0,0,0,0
        if self.phase!=2:return 8,self,0,0,0,0
        closed=self.local_fin if self.role==0 else self.remote_fin
        return 0,replace(self,rx=b'',expected=b'',phase=3 if closed else 0,
                         local_fin=int(self.local_fin or closed)),0,0,0,3 if closed else (0 if self.role else 1)

    def finish(self):
        if self.role and self.phase==2:return 8,self,0,0,0,0
        if self.gate!=3:return 11,self,0,0,0,0
        if self.phase==3:return 9,self,0,0,0,0
        return 0,replace(self,local_fin=1),0,0,0,3

    def cancel(self,now=0,timer=False):
        if timer and (now<self.deadline or self.phase==3):return 0,self,0,0,0,0
        return 0,replace(self,rx=b'',expected=b'',phase=3,local_fin=1),0,0,0,5 if timer else 4
