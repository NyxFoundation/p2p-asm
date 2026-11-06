import Libp2pAsm.Spec.Crypto.SHA256

/-!
HMAC construction from RFC 2104 section 2, instantiated with SHA-256 (B=64,
L=32). Independent transcription of the construction, not of the sample C code.
https://www.rfc-editor.org/rfc/rfc2104.html#section-2
Conformance vectors: https://www.rfc-editor.org/rfc/rfc4231.html#section-4
-/

namespace Libp2pAsm.Spec.Crypto.HMAC

/-- Hash keys longer than one block, then zero-pad to exactly one block.
Empty keys are supported by the construction, without a security endorsement.
-/
def normalizeKey (key : List UInt8) : Except Error (List UInt8) := do
  let shortKey ← if key.length > 64 then SHA256.hash key else pure key
  return shortKey ++ List.replicate (64 - shortKey.length) 0

/-- RFC 2104 H((K0 xor opad) || H((K0 xor ipad) || message)).
SHA-256 length errors propagate, including the 64-byte inner prefix.
The result is the full 32-byte MAC; any protocol truncation is the caller's job.
-/
def sha256 (key message : List UInt8) : Except Error (List UInt8) := do
  let keyBlock ← normalizeKey key
  let inner ← SHA256.hash (keyBlock.map (fun b => b ^^^ 0x36) ++ message)
  SHA256.hash (keyBlock.map (fun b => b ^^^ 0x5c) ++ inner)

end Libp2pAsm.Spec.Crypto.HMAC
