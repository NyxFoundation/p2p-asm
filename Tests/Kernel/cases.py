"""State and full-memory fixtures from independent integer oracles."""
import struct
from limits import variants,validate,reserved,DEFAULT


def pack(v): return struct.pack('<'+'Q'*len(v),*v)


def fixture(label,state,inp,status=0,first=0,second=0,after=None,option=0,budget=64):
    regions=[list(b'G'*8+pack(state)+b'G'*8),list(b'I'*9+inp+b'I'*9),list(b'O'*520),list(b'X'*16),list(b'Y'*16),list(b'S'*4096)]
    want=[r[:] for r in regions]
    if after is not None: want[0][8:8+8*len(after)]=pack(after)
    want[5][-256:]=bytes(256)
    return dict(label=label,regions=regions,after=want,
        args=[0x200008,8*len(state),0x210009,len(inp),0x220008,488,option,budget],
        status=status,first=first,second=second,entered=True,stackDepth=256,extraReads=[])


def limits_cases(export=False):
    result=[]
    for name,v in variants():
        status=validate(v)
        f=fixture(name,[],pack(v),status,(488 if export else reserved(v)) if not status else 0)
        if export and not status: f['after'][2][8:496]=pack(v)
        result.append(f)
    for n in (0,1,7,8,487,489):
        result.append(fixture(f'size-{n}',[],(pack(DEFAULT)+b'!')[:n],1))
    return result
