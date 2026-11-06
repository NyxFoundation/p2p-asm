import Libp2pAsm.Spec.Tls.Cursor

namespace Libp2pAsm.Spec.Tls

/-- Slot numbers are stable 64-bit little-endian output words. Every slice
is relative to the first input handshake byte, never to a TLS record. -/
inductive Field where
  | random | session | suites | compression | extensions | versions | groups
  | shares | signatures | certSignatures | alpn | transportParams | cookie
  | requestContext | certificates | certificate | certificateExtensions
  | signature | verifyData | ticketNonce | ticket | x25519 | p256
  deriving BEq, DecidableEq, Repr

def Field.index : Field → Nat
  | .random => 0 | .session => 1 | .suites => 2 | .compression => 3
  | .extensions => 4 | .versions => 5 | .groups => 6 | .shares => 7
  | .signatures => 8 | .certSignatures => 9 | .alpn => 10 | .transportParams => 11
  | .cookie => 12 | .requestContext => 13 | .certificates => 14 | .certificate => 15
  | .certificateExtensions => 16 | .signature => 17 | .verifyData => 18
  | .ticketNonce => 19 | .ticket => 20 | .x25519 => 21 | .p256 => 22

def Field.slot (f : Field) : Nat := if f.index < 21 then 12+2*f.index else 56+2*(f.index-21)

structure View where
  kind : Nat := 0
  consumed : Nat := 0
  hrr : Bool := false
  obligations : Nat := 0
  legacyVersion : Nat := 0
  cipherSuite : Nat := 0
  compression : Nat := 0
  signatureScheme : Nat := 0
  lifetime : Nat := 0
  ageAdd : Nat := 0
  certificateCount : Nat := 0
  shareCount : Nat := 0
  slices : Array Slice := Array.replicate 23 ⟨0,0⟩
  selectedGroup : Nat := 0
  sniPresent : Bool := false
  signatureMask : Nat := 0
  groupMask : Nat := 0
  versionMask : Nat := 0
  alpnMatches : Nat := 0
  deriving Repr

def View.get (v : View) (f : Field) : Slice := v.slices[f.index]!
def View.set (v : View) (f : Field) (s : Slice) : View :=
  {v with slices := v.slices.set! f.index s}

def View.words (v : View) : List Nat :=
  [v.kind,v.consumed,if v.hrr then 1 else 0,v.obligations,v.legacyVersion,
   v.cipherSuite,v.compression,v.signatureScheme,v.lifetime,v.ageAdd,
   v.certificateCount,v.shareCount] ++
  (v.slices.toList.take 21).flatMap (fun s => [s.offset,s.length]) ++
  [v.selectedGroup,if v.sniPresent then 1 else 0] ++ (v.slices.toList.drop 21).flatMap (fun s => [s.offset,s.length]) ++
  [v.signatureMask,v.groupMask,v.versionMask,v.alpnMatches]

/-- Typed endpoint views preserve offers as source slices; unknown values stay
available to the caller. Masks describe supported values, not authorization. -/
structure Offer where
  session : Slice
  suites : Slice
  versions : Slice
  groups : Slice
  shares : Slice
  signatures : Slice
  certSignatures : Slice
  alpn : Slice
  params : Slice
  deriving Repr

def View.offer (v : View) : Except Error Offer := do
  if v.kind != 1 then throw .malformed
  return ⟨v.get .session,v.get .suites,v.get .versions,v.get .groups,v.get .shares,
    v.get .signatures,v.get .certSignatures,v.get .alpn,v.get .transportParams⟩

structure Selection where
  retry : Bool
  cipherSuite : Nat
  group : Nat
  session : Slice
  share : Slice
  cookie : Slice
  extensions : Slice
  deriving Repr

def View.selection (v : View) : Except Error Selection := do
  if v.kind != 2 then throw .malformed
  return ⟨v.hrr,v.cipherSuite,v.selectedGroup,v.get .session,v.get .shares,
    v.get .cookie,v.get .extensions⟩

def hrrRandom : Bytes := #[
  0xcf,0x21,0xad,0x74,0xe5,0x9a,0x61,0x11,0xbe,0x1d,0x8c,0x02,0x1e,0x65,0xb8,0x91,
  0xc2,0xa2,0x11,0x16,0x7a,0xbb,0x8c,0x5e,0x07,0x9e,0x09,0xe2,0xc8,0xa8,0x33,0x9c]

end Libp2pAsm.Spec.Tls
