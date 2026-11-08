import Libp2pAsm.Spec.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.Frame
import Libp2pAsm.Spec.Quic.Wire.FrameEncode
import Libp2pAsm.Spec.Quic.Wire.Transport
import Libp2pAsm.Spec.Crypto.Quic.Packet
import Libp2pAsm.Spec.Crypto.SHA256
import Libp2pAsm.Spec.Limits

/-! Per-connection event-driven core: shared envelope and arithmetic types.

This is the executable Spec for the design §5 semantic shape
`step(State, Event) → Step`. One step call processes exactly one event and
returns bounded actions; the host adapter serializes events and applies them.
The kernel resource routine owns admission, scheduling and instruction
accounting; this module owns the protocol state itself. -/

namespace Libp2pAsm.Spec.Connection

/-- Endpoint role. Drives CID selection, key directions and the TLS FSM. -/
inductive Role where | client | server deriving Repr, BEq, DecidableEq

inductive Error where
  | malformed | unsupported | limit | resource | keys | authentication
  | stale | closed | busy | state | timeout | entropy | clock
  /-- Diagnostic passthrough with the wrapped numeric cause, used only to
  localize transport-layer failures during development runs. -/
  | coded (cause : Nat)
  deriving Repr, BEq, DecidableEq

def Error.code : Error → Nat
  | .malformed => 1 | .unsupported => 2 | .limit => 3 | .resource => 4
  | .keys => 5 | .authentication => 6 | .stale => 7 | .closed => 8
  | .busy => 9 | .state => 10 | .timeout => 11 | .entropy => 12 | .clock => 13
  | .coded cause => cause

/-- UDP payload cap; this profile fixes the path MTU at 1200 bytes. -/
def maxDatagram : Nat := 1200

/-- Packet-number spaces of a v1 connection. -/
inductive Level where
  | initial | handshake | application
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Bounded ACK-eliciting send record for loss reporting. CRYPTO ranges are
repacketized with a fresh packet number; stream payloads are re-reserved from
their immutable pending bytes; raw ciphertext is never reused. -/
structure SentRecord where
  number : Nat
  sentAt : Nat
  attempts : Nat
  crypto : List (Nat × Nat) := []
  streams : List (Nat × Nat × Nat × Bool) := []
  deriving Repr, BEq

/-- One packet-number space. `key` holds the 44-byte packetKeys encoding
(key[16] || IV[12] || HP[16]); `peerKey` opens incoming packets together with
the peer's 32-byte traffic secret, retained for one key phase update. -/
structure Space where
  next : Nat := 0
  acked : Nat := 0
  seenNext : Nat := 0
  seen : List Nat := []
  ackPending : Bool := false
  unacked : List SentRecord := []
  key : Option (List UInt8) := none
  peerKey : Option (List UInt8) := none
  peerSecret : Option (List UInt8) := none
  recvPhase : Bool := false
  recvUpdated : Bool := false
  prevRecvKey : Option (List UInt8) := none
  deriving Repr, BEq

/-- Received packet numbers as descending non-overlapping (start,count) ranges.
Extending the newest receives is O(1); the range count stays bounded. -/
structure AckSet where
  count : Nat := 0
  ranges : List (Nat × Nat) := []
  deriving Repr, BEq

def AckSet.contains (a : AckSet) (n : Nat) : Bool :=
  a.ranges.any (fun (s,c) => s ≤ n && n < s + c)

def AckSet.ready (a : AckSet) : Bool := a.count != 0

/-- Record one received packet number, keeping at most `limit` ranges; the
oldest (smallest-start) ranges retire when full, so the footprint stays fixed. -/
def AckSet.record (a : AckSet) (n : Nat) (limit : Nat) : AckSet :=
  match a.ranges with
  | (s,c) :: rest =>
    if n == s then a
    else if n == s + c then ⟨a.count+1, (s,c+1) :: rest⟩
    else if n+1 == s then ⟨a.count+1, (n,c+1) :: rest⟩
    else
      let ranges := (n,1) :: (if a.ranges.length < limit then a.ranges else a.ranges.dropLast)
      ⟨a.count+1, ranges⟩
  | [] => ⟨1, [(n,1)]⟩

/-- Deterministic CID derivation from entropy bytes. Production CIDs must come
from the host entropy source; this derivation keeps the model and tests fully
determined without any hidden randomness. SHA-256 over these bounded inputs
always succeeds; the `[]` branch only closes the `Except` type, never a path
reachable with nonempty bounded inputs. -/
def deriveCid (entropy : List UInt8) (index : Nat) : List UInt8 :=
  match Crypto.SHA256.hash (entropy ++ [UInt8.ofNat (index % 256)]) with
  | .ok digest => digest.take 8
  | .error _ => []

/-- CRYPTO reassembly for one level. `next` is the contiguous prefix length
the consumer can read via `ready`; out-of-order chunks stay pending, sorted,
and never overlap the ready span. -/
structure CryptoIn where
  next : Nat := 0
  bytes : Nat := 0
  ready : List UInt8 := []
  pending : List (Nat × List UInt8) := []
  deriving Repr, BEq

structure CryptoOut where
  offset : Nat := 0
  buffer : List UInt8 := []
  deriving Repr, BEq

private def sortedInsert (o : Nat) (v : List UInt8) :
    List (Nat × List UInt8) → List (Nat × List UInt8)
  | [] => [(o,v)]
  | (o',v') :: rest =>
    if o < o' then (o,v) :: (o',v') :: rest
    else (o',v') :: sortedInsert o v rest

private def drainChunks :
    List (Nat × List UInt8) → List UInt8 → Nat →
    List (Nat × List UInt8) × List UInt8 × Nat
  | [], ready, next => ([], ready, next)
  | (o,v) :: rest, ready, next =>
    if o == next then drainChunks rest (ready ++ v) (next + v.length)
    else (if o < next then rest else (o,v) :: rest, ready, next)

/-- Insert one CRYPTO chunk. Retransmissions of already-received bytes are
dropped without consuming budget; overlaps against the contiguous prefix are
trimmed before insertion. The buffer bound is checked before any write, and
the only subtraction runs after its guard. -/
def CryptoIn.insert (c : CryptoIn) (offset : Nat) (value : List UInt8)
    (limit : Nat) : Except Error CryptoIn := do
  if offset + value.length ≤ c.next then
    return c
  if c.bytes + value.length > limit then throw .limit
  let fresh := if offset < c.next then value.drop (c.next - offset) else value
  let pending := sortedInsert offset fresh (c.pending.filter (fun p => p.1 != offset))
  let (pending', ready, next) := drainChunks pending c.ready c.next
  return {
    c with
    next := next,
    ready := ready,
    pending := pending',
    bytes := c.bytes + value.length
  }

/-- Drop the first `n` consumed bytes from the ready span. -/
def CryptoIn.dropReady (c : CryptoIn) (n : Nat) : Except Error CryptoIn :=
  if n ≤ c.ready.length then
    .ok {c with ready := c.ready.drop n, bytes := c.bytes - n}
  else .error .state

theorem CryptoIn.dropReady_ok (c : CryptoIn) (n : Nat) (h : n ≤ c.ready.length) :
    c.dropReady n = .ok {c with ready := c.ready.drop n, bytes := c.bytes - n} := by
  simp [CryptoIn.dropReady, h]

/-- Crypto send side: bytes buffer plus an absolute stream offset cursor. -/
def CryptoOut.append (c : CryptoOut) (value : List UInt8) (limit : Nat) :
    Except Error CryptoOut := do
  if c.buffer.length + value.length > limit then throw .limit
  return {c with buffer := c.buffer ++ value}

/-- Pop at most `n` bytes from the front of the send buffer. -/
def CryptoOut.take (c : CryptoOut) (n : Nat) : CryptoOut × Nat :=
  let k := min n c.buffer.length
  ({c with buffer := c.buffer.drop k, offset := c.offset + k}, k)

theorem CryptoOut.take_bound (c : CryptoOut) (n : Nat) :
    (c.take n).2 ≤ n ∧ (c.take n).2 = min n c.buffer.length := by
  show min n c.buffer.length ≤ n ∧ (min n c.buffer.length = min n c.buffer.length)
  exact ⟨Nat.min_le_left _ _, rfl⟩

end Libp2pAsm.Spec.Connection
