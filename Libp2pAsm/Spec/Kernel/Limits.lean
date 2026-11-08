import Libp2pAsm.Spec.Limits
import Libp2pAsm.Spec.Kernel.Words

namespace Libp2pAsm.Spec.Kernel

def rawLimitsBytes : Nat := 488

def decodeLimits (bs : Array UInt8) : Except Nat Limits := do
  unless bs.size = rawLimitsBytes do throw 1
  return {
    maxConnections := word bs 0
    maxConnectionsPerSource := word bs 8
    maxHandshakes := word bs 16
    maxHandshakesPerSource := word bs 24
    maxSources := word bs 32
    maxStarts := word bs 40
    maxStartsPerSource := word bs 48
    startWindowNs := word bs 56
    handshakeTimeoutNs := word bs 64
    maxSockets := word bs 72
    maxDatagramBytes := word bs 80
    maxRxBatch := word bs 88
    rxWindowNs := word bs 96
    maxRxDatagrams := word bs 104
    maxRxBytes := word bs 112
    maxQueuedDatagrams := word bs 120
    maxStreamsPerConnection := word bs 128
    streamReceiveBytes := word bs 136
    streamSendBytes := word bs 144
    cryptoBufferBytes := word bs 152
    maxAckRanges := word bs 160
    trackedPacketNumbers := word bs 168
    maxSentPackets := word bs 176
    maxPathsPerConnection := word bs 184
    maxActiveConnectionIds := word bs 192
    maxPacketsPerQuantum := word bs 200
    maxFramesPerQuantum := word bs 208
    maxInputEvents := word bs 216
    completionSlots := word bs 224
    maxApplicationRequests := word bs 232
    maxPendingSends := word bs 240
    maxTimers := word bs 248
    maxEntropyRequests := word bs 256
    maxClockRequests := word bs 264
    maxContinuations := word bs 272
    maxActions := word bs 280
    maxWallClockDriftNs := word bs 288
    maxClockSampleSpanNs := word bs 296
    maxSendWaitNs := word bs 304
    maxSendAttempts := word bs 312
    maxEntropyWaitNs := word bs 320
    maxClockWaitNs := word bs 328
    idleTimeoutNs := word bs 336
    negotiationTimeoutNs := word bs 344
    pingTimeoutNs := word bs 352
    maxNegotiationBytes := word bs 360
    maxProposals := word bs 368
    maxInboundPings := word bs 376
    maxOutboundPings := word bs 384
    maxCertificateBytes := word bs 392
    maxHostPublicKeyBytes := word bs 400
    maxInstructionsPerQuantum := word bs 408
    maxInstructionsPerConnection := word bs 416
    maxInstructionsGlobal := word bs 424
    cpuWindowNs := word bs 432
    arenaBytes := word bs 440
    connectionMetadataBytes := word bs 448
    cryptoScratchBytes := word bs 456
    globalMetadataBytes := word bs 464
    maxStackBytes := word bs 472
    maxRegions := word bs 480
  }

def limitsErrorCode : LimitsError → Nat
  | .range => 1 | .connections => 2 | .packets => 3 | .streams => 4
  | .completions => 5 | .clocks => 6 | .execution => 7 | .memory => 8

def encodeLimits (l : Limits) : Except Nat (List UInt8) := do
  l.validate.mapError limitsErrorCode
  return pack l.wordFields

def validateRaw (bs : Array UInt8) : Except Nat Limits := do
  let l ← decodeLimits bs
  l.validate.mapError limitsErrorCode
  return l

end Libp2pAsm.Spec.Kernel
