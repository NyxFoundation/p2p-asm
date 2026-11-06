"""Send oracle uses absolute byte dictionaries and ACK sets, not the ASM ring."""
from dataclasses import dataclass,field,replace
from oracle import MAX,NONE

@dataclass
class Send:
    cap:int=8
    base:int=0
    queued:int=0
    sent:int=0
    limit:int=MAX
    allowance:int=MAX
    final:int=NONE
    fin_sent:int=0
    fin_ack:int=0
    reset:int=0
    pending:object=None
    data:dict=field(default_factory=dict)
    acked:set=field(default_factory=set)

    def append(self,payload,fin=0):
        if fin not in (0,1): return 1,self
        if self.reset or self.final!=NONE: return 9,self
        end=self.queued+len(payload)
        if end>MAX: return 2,self
        if end-self.base>self.cap: return 6,self
        return 0,replace(self,queued=end,final=end if fin else NONE,
                         data=self.data|{self.queued+i:b for i,b in enumerate(payload)})

    def reserve(self,off,n,fin=0):
        if fin not in (0,1): return 1,self,0
        if self.reset: return 9,self,0
        if self.pending is not None: return 8,self,0
        end=off+n
        if off<self.base or off>self.sent or end>self.queued: return 8,self,0
        if fin and (self.final==NONE or end!=self.final): return 4,self,0
        d=max(self.sent,end)-self.sent
        if end>self.limit or d>self.allowance: return 3,self,0
        return 0,replace(self,pending=(off,n,fin)),d

    def collect(self):
        base=self.base
        while base<self.sent and base in self.acked and (self.pending is None or base<self.pending[0]):
            base+=1
        return replace(self,base=base,data={k:v for k,v in self.data.items() if k>=base},
                       acked={k for k in self.acked if k>=base})

    def settle(self,success):
        if success not in (0,1): return 1,self,0
        if self.pending is None: return 8,self,0
        off,n,fin=self.pending
        d=max(self.sent,off+n)-self.sent
        t=replace(self,pending=None,sent=max(self.sent,off+n) if success else self.sent,
                  fin_sent=int(self.fin_sent or (success and fin)))
        return 0,t.collect(),d

    def ack(self,off,n,fin=0):
        if fin not in (0,1): return 1,self
        end=off+n
        if end>self.sent: return 8,self
        if fin and (not self.fin_sent or end!=self.final): return 4,self
        t=replace(self,acked=self.acked|set(range(max(self.base,off),end)),
                  fin_ack=int(self.fin_ack or fin))
        return 0,t.collect()

    def stop(self):
        if self.pending is not None: return 8,self
        return 0,replace(self,base=self.sent,queued=self.sent,final=self.sent,reset=1,data={},acked=set())
