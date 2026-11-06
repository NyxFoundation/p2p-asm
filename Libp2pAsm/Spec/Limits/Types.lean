import Std

namespace Libp2pAsm.Spec

/-- Local resource policy, not RFC maxima. Every configured limit has a finite default. -/
structure Limits where
  maxConnections : Nat := 16
  maxConnectionsPerSource : Nat := 4
  maxHandshakes : Nat := 8
  maxHandshakesPerSource : Nat := 2
  maxSources : Nat := 64
  maxStarts : Nat := 16
  maxStartsPerSource : Nat := 4
  startWindowNs : Nat := 1000000000
  handshakeTimeoutNs : Nat := 10000000000
  maxSockets : Nat := 4
  maxDatagramBytes : Nat := 2048
  maxRxBatch : Nat := 32
  rxWindowNs : Nat := 1000000000
  maxRxDatagrams : Nat := 1024
  maxRxBytes : Nat := 2097152
  maxQueuedDatagrams : Nat := 64
  maxStreamsPerConnection : Nat := 8
  streamReceiveBytes : Nat := 65536
  streamSendBytes : Nat := 65536
  cryptoBufferBytes : Nat := 65536
  maxAckRanges : Nat := 64
  trackedPacketNumbers : Nat := 4096
  maxSentPackets : Nat := 128
  maxPathsPerConnection : Nat := 2
  maxActiveConnectionIds : Nat := 8
  maxPacketsPerQuantum : Nat := 4
  maxFramesPerQuantum : Nat := 64
  maxInputEvents : Nat := 1024
  completionSlots : Nat := 640
  maxApplicationRequests : Nat := 64
  maxPendingSends : Nat := 64
  maxTimers : Nat := 512
  maxEntropyRequests : Nat := 32
  maxClockRequests : Nat := 16
  maxContinuations : Nat := 32
  maxActions : Nat := 16
  maxWallClockDriftNs : Nat := 250000000
  maxClockSampleSpanNs : Nat := 1000000
  maxSendWaitNs : Nat := 5000000000
  maxSendAttempts : Nat := 16
  maxEntropyWaitNs : Nat := 1000000000
  maxClockWaitNs : Nat := 1000000000
  idleTimeoutNs : Nat := 60000000000
  negotiationTimeoutNs : Nat := 10000000000
  pingTimeoutNs : Nat := 10000000000
  maxNegotiationBytes : Nat := 1024
  maxProposals : Nat := 8
  maxInboundPings : Nat := 2
  maxOutboundPings : Nat := 1
  maxCertificateBytes : Nat := 16384
  maxHostPublicKeyBytes : Nat := 4096
  maxInstructionsPerQuantum : Nat := 16777216
  maxInstructionsPerConnection : Nat := 268435456
  maxInstructionsGlobal : Nat := 1073741824
  cpuWindowNs : Nat := 1000000000
  arenaBytes : Nat := 33554432
  connectionMetadataBytes : Nat := 65536
  cryptoScratchBytes : Nat := 65536
  globalMetadataBytes : Nat := 1048576
  maxStackBytes : Nat := 16384
  maxRegions : Nat := 256
  deriving Repr, BEq

def Limits.wordFields (l : Limits) : List Nat :=
  [
    l.maxConnections, l.maxConnectionsPerSource, l.maxHandshakes,
    l.maxHandshakesPerSource, l.maxSources, l.maxStarts,
    l.maxStartsPerSource, l.startWindowNs, l.handshakeTimeoutNs,
    l.maxSockets, l.maxDatagramBytes, l.maxRxBatch,
    l.rxWindowNs, l.maxRxDatagrams, l.maxRxBytes,
    l.maxQueuedDatagrams, l.maxStreamsPerConnection, l.streamReceiveBytes,
    l.streamSendBytes, l.cryptoBufferBytes, l.maxAckRanges,
    l.trackedPacketNumbers, l.maxSentPackets, l.maxPathsPerConnection,
    l.maxActiveConnectionIds, l.maxPacketsPerQuantum, l.maxFramesPerQuantum,
    l.maxInputEvents, l.completionSlots, l.maxApplicationRequests,
    l.maxPendingSends, l.maxTimers, l.maxEntropyRequests,
    l.maxClockRequests, l.maxContinuations, l.maxActions,
    l.maxWallClockDriftNs, l.maxClockSampleSpanNs, l.maxSendWaitNs,
    l.maxSendAttempts, l.maxEntropyWaitNs, l.maxClockWaitNs,
    l.idleTimeoutNs, l.negotiationTimeoutNs, l.pingTimeoutNs,
    l.maxNegotiationBytes, l.maxProposals, l.maxInboundPings,
    l.maxOutboundPings, l.maxCertificateBytes, l.maxHostPublicKeyBytes,
    l.maxInstructionsPerQuantum, l.maxInstructionsPerConnection, l.maxInstructionsGlobal,
    l.cpuWindowNs, l.arenaBytes, l.connectionMetadataBytes,
    l.cryptoScratchBytes, l.globalMetadataBytes, l.maxStackBytes,
    l.maxRegions]

/-- Fixed event-slot reservation for the Linux event/action ABI, in bytes. -/
def eventSlotBytes : Nat := 256

/-- Reservation accounting. Actual allocator/stack usage must separately refine these budgets. -/
def Limits.reservedBytes (l : Limits) : Nat :=
  l.maxConnections * (l.connectionMetadataBytes + l.cryptoScratchBytes +
    2 * l.cryptoBufferBytes +
    l.maxStreamsPerConnection * (l.streamReceiveBytes + l.streamSendBytes)) +
  (l.maxQueuedDatagrams + l.maxPendingSends) * l.maxDatagramBytes +
  l.maxInputEvents * eventSlotBytes + l.globalMetadataBytes + l.maxStackBytes

def Limits.requiredCompletionSlots (l : Limits) : Nat :=
  l.maxTimers + l.maxPendingSends + l.maxEntropyRequests + l.maxClockRequests

/-- One idle, three PN-space, and one pacing timer per connection, plus request deadlines. -/
def Limits.requiredTimers (l : Limits) : Nat :=
  5 * l.maxConnections + l.maxHandshakes + l.maxConnections * l.maxStreamsPerConnection +
    l.maxPendingSends + l.maxEntropyRequests + l.maxClockRequests

end Libp2pAsm.Spec
