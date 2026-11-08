"""Preflight failures have no stack or memory effect, and preserve every saved register."""
from cases import fixture,pack
from limits import DEFAULT,MAX


def cases():
    result=[]
    def add(name,index,value,error,other=None):
        f=fixture(name,[],pack(DEFAULT),error)
        f['args'][index]=value
        if other:
            for i,n in other.items():f['args'][i]=n
        f['entered']=False;f['after']=[r[:] for r in f['regions']]
        result.append(f)
    add('input-one-past-overflow',2,MAX,9)
    add('state-one-past-overflow',0,MAX-7,9,{1:8})
    add('output-one-past-overflow',4,MAX-7,9)
    add('state-alignment',0,0x200009,10)
    add('output-alignment',4,0x220009,10)
    add('input-output-alias',4,0x210008,10)
    add('stack-input-alias',2,0x250f00,10)
    return result
