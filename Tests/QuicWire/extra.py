"""Public vectors, negotiated CID lengths, resource and permission boundaries."""
from cases import fixture
from reference import frame, packet, var, MAX
from vectors import CLIENT_PACKET, SERVER_PACKET, CLIENT_PAYLOAD, SERVER_PAYLOAD, RETRY


def public_packets():
    result=[]
    for name,data in [('rfc-client',CLIENT_PACKET),('rfc-server',SERVER_PACKET),('rfc-retry',RETRY)]:
        result.append(fixture('packet',name,data))
        result += [fixture('packet',f'{name}-cut-{i}',data[:i]) for i in range(len(data))]
    result.append(fixture('packet','rfc-coalesced',CLIENT_PACKET+SERVER_PACKET))
    for cid in range(21): result.append(fixture('packet',f'short-cid-{cid}',b'\x7f'+b'c'*cid+b'payload',cid))
    return result


def public_frames():
    result=[]
    for name,data in [('rfc-client-crypto',CLIENT_PAYLOAD),('rfc-server-ack',SERVER_PAYLOAD)]:
        w=frame(data)
        end=w[0]
        result.append(fixture('frame',name,data))
        result += [fixture('frame',f'{name}-cut-{i}',data[:i]) for i in range(end)]
        if name=='rfc-server-ack': result.append(fixture('frame','rfc-server-crypto',data[end:]))
    # Configurable capacity above tiny fixtures; no RFC cap at 32 ACK ranges.
    count=100
    result.append(fixture('frame','ack-101-ranges',b'\2'+var(1000)+b'\0'+var(count)+b'\0'+b'\0\0'*count,bound=count+1))
    result[-1]['args'][3:6:2]=[4096,4096]
    result[-1]['regions'][1]=[0xa5]*(11+4096+8)
    result[-1]['regions'][2]=[0xa5]*(8+4096+8)
    return result


def permissions():
    result=[]
    for tag in range(32):
        for level in range(4):
            for server in range(2):
                allowed=(tag<=30 and not (tag in (7,30) and not server) and
                    not(level==2 and server) and
                    (tag in (0,1,2,3,6,28) if level<2 else
                     tag<=29 and tag not in (2,3,6,7,25,27) if level==2 else True))
                f=fixture('packet',f'permission-{tag}-{level}-{server}',b'')
                f.update(args=[tag,level,server,0,0,0,0,0],checkSpec=False,
                    output=[],stackDepth=0,wipeLength=0,status=0 if allowed else 7 if tag>30 else 9,
                    errorOffset=int(allowed and tag not in (0,2,3,28,29)),
                    consumed=int(allowed and tag not in (2,3,28,29)))
                result.append(f)
    return result
