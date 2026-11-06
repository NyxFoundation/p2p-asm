import Libp2pAsm.Spec.Tls.Basic

namespace Libp2pAsm.Spec.Tls.Bounds

/-- Structural bounds used by callers before admitting a non-yielding operation.
These are conservative engineering budgets, not an instruction-count proof.
Input byte count includes the 4-byte header. Bitmap clear costs for every
certificate entry are included by charging 200000 steps per input byte. -/
def decodeSteps (bytes : Nat) : Nat := 2000000+200000*bytes

def encodeWorkspace (body : Nat) : Nat := (body+11)/8*8+17472

def encodeSteps (body : Nat) : Nat := decodeSteps (body+4)+100*(encodeWorkspace body+body+1)

def vectorSteps (bytes : Nat) : Nat := 1000+16*bytes

def transcriptSteps (bytes : Nat) : Nat := 2000000+100000*(bytes/64+2)

/-- SHA256's mathematical length bound is separate from a scheduler's budget.
Reject before converting this Nat admission result to a machine word. -/
def admit (required budget : Nat) : Except Error Unit := do
  if required > budget || required ≥ 2^64 then throw .limit

end Libp2pAsm.Spec.Tls.Bounds
