"""Independent, unbounded integer policy and allocation oracle."""
from dataclasses import dataclass
import struct

MAX = (1 << 64) - 1
NAMES = '''maxConnections maxConnectionsPerSource maxHandshakes maxHandshakesPerSource maxSources maxStarts maxStartsPerSource startWindowNs handshakeTimeoutNs maxSockets maxDatagramBytes maxRxBatch rxWindowNs maxRxDatagrams maxRxBytes maxQueuedDatagrams maxStreamsPerConnection streamReceiveBytes streamSendBytes cryptoBufferBytes maxAckRanges trackedPacketNumbers maxSentPackets maxPathsPerConnection maxActiveConnectionIds maxPacketsPerQuantum maxFramesPerQuantum maxInputEvents completionSlots maxApplicationRequests maxPendingSends maxTimers maxEntropyRequests maxClockRequests maxContinuations maxActions maxWallClockDriftNs maxClockSampleSpanNs maxSendWaitNs maxSendAttempts maxEntropyWaitNs maxClockWaitNs idleTimeoutNs negotiationTimeoutNs pingTimeoutNs maxNegotiationBytes maxProposals maxInboundPings maxOutboundPings maxCertificateBytes maxHostPublicKeyBytes maxInstructionsPerQuantum maxInstructionsPerConnection maxInstructionsGlobal cpuWindowNs arenaBytes connectionMetadataBytes cryptoScratchBytes globalMetadataBytes maxStackBytes maxRegions'''.split()
DEFAULT = [16,4,8,2,64,16,4,10**9,10**10,4,2048,32,10**9,1024,2097152,64,8,65536,65536,65536,64,4096,128,2,8,4,64,1024,640,64,64,512,32,16,32,16,250000000,1000000,5000000000,16,10**9,10**9,60000000000,10**10,10**10,1024,8,2,1,16384,4096,16777216,268435456,1073741824,10**9,33554432,65536,65536,1048576,16384,256]


def reserved(v):
    l = dict(zip(NAMES,v)); g = l.__getitem__
    return g('maxConnections')*(g('connectionMetadataBytes')+g('cryptoScratchBytes')+2*g('cryptoBufferBytes')+g('maxStreamsPerConnection')*(g('streamReceiveBytes')+g('streamSendBytes'))) + (g('maxQueuedDatagrams')+g('maxPendingSends'))*g('maxDatagramBytes')+g('maxInputEvents')*256+g('globalMetadataBytes')+g('maxStackBytes')


def validate(v):
    if len(v)!=61 or not all(0<x<=MAX for x in v): return 1
    l = dict(zip(NAMES,v)); g = l.__getitem__
    pairs = [('maxConnectionsPerSource','maxConnections'),('maxHandshakes','maxConnections'),('maxHandshakesPerSource','maxHandshakes'),('maxHandshakesPerSource','maxConnectionsPerSource'),('maxConnections','maxSources'),('maxStartsPerSource','maxStarts')]
    if not all(g(a)<=g(b) for a,b in pairs) or min(v[23:25])<2: return 2
    if not (1200<=v[10]<=65507 and v[11]<=v[13] and v[11]<=v[15] and v[10]<=v[14] and 2*v[20]<=v[21]): return 3
    if not (v[47]==2 and v[48]==1 and v[47]+v[48]<=v[16] and v[45]<=v[17] and v[45]<=v[18] and 4096<=v[49]<=v[19] and v[50]<=v[49]): return 4
    if not (v[31]+v[30]+v[32]+v[33]<=v[28] and v[28]+v[15]+v[29]<=v[27] and 5*v[0]+v[2]+v[0]*v[16]+v[30]+v[32]+v[33]<=v[31]): return 5
    if v[37]>v[36]: return 6
    if not v[51]<=v[52]<=v[53]: return 7
    if v[59]%16 or reserved(v)>v[55]: return 8
    return 0


def variants():
    yield 'defaults',DEFAULT[:]
    for i in range(61):
        for n in (0,1,MAX//2,MAX//2+1,MAX-1,MAX):
            v=DEFAULT[:];v[i]=n
            yield f'field-{i}-{n}',v
    for a,b in [(31,30),(28,15),(0,16),(17,18),(56,57),(15,30)]:
        v=DEFAULT[:];v[a]=MAX;v[b]=MAX
        yield f'sum-product-{a}-{b}',v


def test_oracle():
    assert len(NAMES)==len(DEFAULT)==61
    assert validate(DEFAULT)==0 and reserved(DEFAULT)==22560768
    assert len(list(variants()))==373

if __name__=='__main__': test_oracle()
