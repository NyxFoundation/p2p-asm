import Libp2pAsm.Spec.Tls.Codec

namespace Libp2pAsm.Spec.Tls.Encode

structure Ext where
  kind : Nat
  data : Bytes
  deriving Repr

def extensions (items : Array Ext) : Except Error Bytes := do
  let mut bytes := #[]
  let mut seen : List Nat := []
  for e in items do
    if e.kind > 65535 then throw .malformed
    if seen.contains e.kind then throw .duplicate
    seen := e.kind :: seen
    bytes := bytes ++ be 2 e.kind ++ (← vector 2 0 e.data)
  vector 2 0 bytes

structure ClientHello where
  random : Bytes
  session : Bytes
  cipherSuites : Bytes
  extensions : Array Ext
  deriving Repr

def clientHello (m : ClientHello) (limit : Nat) : Except Error Bytes := do
  if m.random.size != 32 || m.session.size > 32 then throw .malformed
  let body := #[3,3] ++ m.random ++ (← vector 1 0 m.session) ++
    (← vector 2 2 m.cipherSuites) ++ #[1,0] ++ (← extensions m.extensions)
  Tls.encode 1 body limit

structure ServerHello where
  random : Bytes
  session : Bytes
  extensions : Array Ext
  deriving Repr

def serverHello (m : ServerHello) (limit : Nat) : Except Error Bytes := do
  if m.random.size != 32 || m.session.size > 32 then throw .malformed
  Tls.encode 2 (#[3,3] ++ m.random ++ (← vector 1 0 m.session) ++
    #[0x13,1,0] ++ (← extensions m.extensions)) limit

def retry (session : Bytes) (group : Option Nat) (cookie : Option Bytes)
    (limit : Nat) : Except Error Bytes := do
  let mut es := #[Ext.mk 43 #[3,4]]
  if let some g := group then
    if g != 23 && g != 29 then throw .profile
    es := es.push ⟨51,be 2 g⟩
  if let some bytes := cookie then es := es.push ⟨44,← vector 2 1 bytes⟩
  serverHello ⟨hrrRandom,session,es⟩ limit

def encryptedExtensions (es : Array Ext) (limit : Nat) : Except Error Bytes := do
  Tls.encode 8 (← extensions es) limit

def certificateRequest (es : Array Ext) (limit : Nat) : Except Error Bytes := do
  Tls.encode 13 (#[0] ++ (← extensions es)) limit

/-- The final profile always emits exactly one opaque certificate. -/
def certificate (der : Bytes) (es : Array Ext) (limit : Nat) : Except Error Bytes := do
  let entry := (← vector 3 1 der) ++ (← extensions es)
  Tls.encode 11 (#[0] ++ (← vector 3 0 entry)) limit

def certificateVerify (scheme : Nat) (signature : Bytes) (limit : Nat) : Except Error Bytes := do
  if scheme > 65535 then throw .malformed
  Tls.encode 15 (be 2 scheme ++ (← vector 2 1 signature)) limit

def finished (verifyData : Bytes) (limit : Nat) : Except Error Bytes :=
  Tls.encode 20 verifyData limit

/-- Parser/discard is the runtime profile; this constructor supports test peers.
No ticket is used for key scheduling or resumption by this implementation. -/
def newSessionTicket (lifetime ageAdd : Nat) (nonce ticket : Bytes)
    (es : Array Ext) (limit : Nat) : Except Error Bytes := do
  if lifetime > 604800 || ageAdd ≥ 2^32 then throw .malformed
  Tls.encode 4 (be 4 lifetime ++ be 4 ageAdd ++ (← vector 1 0 nonce) ++
    (← vector 2 1 ticket) ++ (← extensions es)) limit

end Libp2pAsm.Spec.Tls.Encode
