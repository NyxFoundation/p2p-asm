import Libp2pAsm.Spec.Limits.Types

namespace Libp2pAsm.Spec

inductive LimitsError where
  | range | connections | packets | streams | completions | clocks | execution | memory
  deriving Repr, BEq, DecidableEq

private def connectionsValid (l : Limits) : Bool := decide (
  l.maxConnectionsPerSource ≤ l.maxConnections ∧
  l.maxHandshakes ≤ l.maxConnections ∧
  l.maxHandshakesPerSource ≤ l.maxHandshakes ∧
  l.maxHandshakesPerSource ≤ l.maxConnectionsPerSource ∧
  l.maxConnections ≤ l.maxSources ∧ l.maxStartsPerSource ≤ l.maxStarts ∧
  2 ≤ l.maxActiveConnectionIds ∧ 2 ≤ l.maxPathsPerConnection)

private def packetsValid (l : Limits) : Bool := decide (
  1200 ≤ l.maxDatagramBytes ∧ l.maxDatagramBytes ≤ 65507 ∧
  l.maxRxBatch ≤ l.maxRxDatagrams ∧ l.maxRxBatch ≤ l.maxQueuedDatagrams ∧
  l.maxDatagramBytes ≤ l.maxRxBytes ∧ 2 * l.maxAckRanges ≤ l.trackedPacketNumbers)

private def streamsValid (l : Limits) : Bool := decide (
  l.maxInboundPings = 2 ∧ l.maxOutboundPings = 1 ∧
  l.maxInboundPings + l.maxOutboundPings ≤ l.maxStreamsPerConnection ∧
  l.maxNegotiationBytes ≤ l.streamReceiveBytes ∧
  l.maxNegotiationBytes ≤ l.streamSendBytes ∧
  4096 ≤ l.maxCertificateBytes ∧ l.maxCertificateBytes ≤ l.cryptoBufferBytes ∧
  l.maxHostPublicKeyBytes ≤ l.maxCertificateBytes)

private def completionsValid (l : Limits) : Bool := decide (
  l.requiredCompletionSlots ≤ l.completionSlots ∧
  l.completionSlots + l.maxQueuedDatagrams + l.maxApplicationRequests ≤ l.maxInputEvents ∧
  l.requiredTimers ≤ l.maxTimers)

private def executionValid (l : Limits) : Bool := decide (
  l.maxInstructionsPerQuantum ≤ l.maxInstructionsPerConnection ∧
  l.maxInstructionsPerConnection ≤ l.maxInstructionsGlobal)

def Limits.validate (l : Limits) : Except LimitsError Unit := do
  unless l.wordFields.all (fun n => decide (0 < n ∧ n < 2^64)) do throw .range
  unless connectionsValid l do throw .connections
  unless packetsValid l do throw .packets
  unless streamsValid l do throw .streams
  unless completionsValid l do throw .completions
  unless l.maxClockSampleSpanNs ≤ l.maxWallClockDriftNs do throw .clocks
  unless executionValid l do throw .execution
  unless l.maxStackBytes % 16 = 0 ∧ l.reservedBytes ≤ l.arenaBytes do throw .memory

theorem Limits.defaults_valid : ({} : Limits).validate = .ok () := by rfl

theorem Limits.defaults_reservations :
    ({} : Limits).reservedBytes = 22560768 := by decide

end Libp2pAsm.Spec
