import Libp2pAsm.Spec.Codec.UnsignedVarint
import Libp2pAsm.Spec.Multistream.Utf8

namespace Libp2pAsm.Spec.Multistream

def header : List UInt8 := "/multistream/1.0.0\n".toUTF8.data.toList
def ping : List UInt8 := "/ipfs/ping/1.0.0\n".toUTF8.data.toList

def frame (text : List UInt8) : List UInt8 :=
  -- The supported advertisements all have single-byte canonical lengths.
  UInt8.ofNat text.length :: text

inductive Role where | dialer | listener deriving DecidableEq, Repr
inductive Phase where | header | proposal | selected | closed deriving DecidableEq, Repr
inductive Error where | framing | unsupported | proposals | deadline deriving DecidableEq, Repr

structure State where
  role : Role
  phase : Phase := .header
  proposalLimit : Nat
  proposals : Nat := 0
  byteLimit : Nat
  deadline : Nat
  pending : List UInt8 := []
  deriving DecidableEq, Repr

structure Result where
  state : State
  consumed : Nat
  response : List UInt8
  selected : Bool
  deriving DecidableEq, Repr

/-- Semantic complete-message decision, independent of the ASM matcher. -/
def select (s : State) (message : List UInt8) : Except Error (State × List UInt8) := do
  match s.phase with
  | .closed => throw .unsupported
  | .selected => return (s, [])
  | .header =>
    unless message = header do throw .framing
    return ({s with phase := .proposal}, [])
  | .proposal =>
    if s.role = .dialer then
      unless message = ping do throw .unsupported
      return ({s with phase := .selected}, [])
    unless s.proposals < s.proposalLimit do throw .proposals
    let chosen := message = ping
    return ({s with
      phase := if chosen then .selected else .proposal
      proposals := s.proposals+1}, frame (if chosen then ping else [110,97,10]))

/-- Canonical unsigned varint, at most 9 bytes (multiformats u63). -/
def lengthPrefix : Nat → Nat → Nat → List UInt8 → Except Error (Option (Nat × Nat))
  | 0, _, _, _ => .error .framing
  | _+1, _, _, [] => .ok none
  | fuel+1, shift, acc, x::xs =>
    let payload := x.toNat % 128
    let value := acc + payload * 2^shift
    if x.toNat < 128 then
      if shift > 0 && payload = 0 then .error .framing
      else .ok (some (value,shift/7+1))
    else lengthPrefix fuel (shift+7) value xs

private def parse (s : State) (bytes : List UInt8) : Except Error (Option (List UInt8)) := do
  let some (n,width) ← lengthPrefix 9 0 0 bytes | return none
  unless 0 < n ∧ n ≤ s.byteLimit do throw .framing
  let body := bytes.drop width
  unless body.length ≤ n do throw .framing
  unless validUtf8Prefix [] body do throw .framing
  unless !(body.take (n-1)).contains 10 do throw .framing
  if body.length < n then return none
  unless body.getLast? = some 10 ∧ !(body.take (n-1)).contains 10 do throw .framing
  unless (String.fromUTF8? ⟨body.toArray⟩).isSome do throw .framing
  return some body

private def scan (s : State) : Nat → List UInt8 → List UInt8 → Except Error Result
  | used, pending, [] => .ok ⟨{s with pending},used,[],s.phase = .selected⟩
  | used, pending, x::xs => do
    let next := pending ++ [x]
    match ← parse s next with
    | none => scan s (used+1) next xs
    | some message =>
      let (t,response) ← select s message
      return ⟨{t with pending := []},used+1,response,t.phase = .selected⟩

def feed (s : State) (bytes : List UInt8) (now : Nat) : Except Error Result := do
  unless now < s.deadline do throw .deadline
  if s.phase = .closed then throw .unsupported
  if s.phase = .selected then return ⟨s,0,[],true⟩
  scan s 0 s.pending bytes

theorem selection_only_ping (s : State) (m : List UInt8)
    (hphase : s.phase = .proposal) (hrole : s.role = .dialer)
    (h : select s m = .ok ({s with phase := .selected}, [])) : m = ping := by
  simp [select, hphase, hrole] at h
  split at h
  · assumption
  · contradiction

theorem header_length : header.length = 19 := by decide
theorem ping_length : ping.length = 17 := by decide
theorem advertisement_canonical : (frame ping).head? = some 17 := by decide

end Libp2pAsm.Spec.Multistream
