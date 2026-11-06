"""Atomic multi-packet/frame caller and descriptor reference."""
import struct
from cases import fixture
from reference import packet, frame, WireError
from vectors import CLIENT_PACKET,SERVER_PACKET,SERVER_PAYLOAD


def case(packets,name,data,option=0,capacity=4):
    width=18 if packets else 18+2*option
    stage=16+width*8*capacity
    child=128 if packets else 128+16*option
    f=fixture('packet',name,data,option,capacity)
    f.update(status=0,errorOffset=0,consumed=0,output=[],wipeLength=stage+child,
             stackDepth=512 if data and capacity else 256)
    # Batch front end only promises the footprint it actually claims after admission.
    f['args'][3]=stage
    f['args'][5]=stage+child
    f['regions'][1]=[0xa5]*(11+stage+8)
    f['regions'][2]=[0xa5]*(8+stage+child+8)
    pos,count,words=0,0,[]
    try:
        while pos<len(data):
            if count==capacity: raise WireError(5,0)
            w=packet(data[pos:],option) if packets else frame(data[pos:],bound=option)
            words+=[pos]+w+[0]*(width-1-len(w))
            pos+=w[0]
            count+=1
        words=[pos,count]+words+[0]*(width*(capacity-count))
        f.update(output=list(struct.pack('<'+'Q'*len(words),*words)),consumed=pos)
    except WireError as e:
        f.update(status=e.code,errorOffset=pos+e.offset)
    return f


def packet_batches():
    a=bytes.fromhex('c0000000010000000178')
    b=bytes.fromhex('e0000000010000027879')
    return [case(True,'empty',b''),case(True,'three-long-short',a+b+b'\x40end'),
        case(True,'unknown-after-long',a+bytes.fromhex('80000000020000abcd')),
        case(True,'rfc-coalesced',CLIENT_PACKET+SERVER_PACKET),
        case(True,'bad-second-atomic',a+b[:-1]),case(True,'capacity-one',a+b,capacity=1),
        case(True,'zero-capacity',a,capacity=0)]


def frame_batches():
    return [case(False,'rfc-frames',SERVER_PAYLOAD,4),
        case(False,'padding-ping-stream',b'\0\1\x08\0rest',4),
        case(False,'ack-plus-data',bytes([2,20,0,1,2,0,1,6,0,3])+b'abc',4),
        case(False,'unknown-second-atomic',b'\1\x1f',4),
        case(False,'frame-capacity',b'\1\1\1',4,2),
        case(False,'empty-frame-batch',b'',0,0)]
