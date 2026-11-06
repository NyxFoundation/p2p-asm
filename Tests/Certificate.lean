import Libp2pAsm.Spec.Identity.X509.Certificate
import Libp2pAsm.Codegen.Protocols
import Libp2pAsm.Rv64.Encoding

namespace Libp2pAsm.Tests.CertificateUnit
open Spec.Identity.X509

private def tlv (tag : Nat) (body : List UInt8) : List UInt8 :=
  let length := Spec.Codec.Der.significantBytes body.length
  [tag.toUInt8] ++
    (if body.length < 128 then [body.length.toUInt8] else (128+length.length).toUInt8 :: length) ++ body

private def seq (body : List UInt8) := tlv 48 body
private def algorithm : List UInt8 := [48,5,6,3,43,101,112]
private def binding : List UInt8 :=
  seq (tlv 6 libp2pOid ++ tlv 1 [255] ++
    tlv 4 (seq (tlv 4 ([8,1,18,32] ++ List.replicate 32 1) ++ tlv 4 (List.replicate 64 0))))

private def sample (extensions : List UInt8 := binding) : List UInt8 :=
  let tbs := seq (tlv 160 (tlv 2 [2]) ++ tlv 2 [1] ++ algorithm ++ seq [] ++
    seq (tlv 23 "700101000000Z".toUTF8.data.toList ++
      tlv 24 "99991231235959Z".toUTF8.data.toList) ++ seq [] ++
    seq (algorithm ++ tlv 3 (0 :: List.replicate 32 1)) ++ tlv 163 (seq extensions))
  seq (tbs ++ algorithm ++ tlv 3 (List.replicate 65 0))

private def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError label)
  IO.println s!"PASS: {label}"

def run : IO Unit := do
  let result := certificate sample
  check "should decode structural certificate views without claiming authentication"
    (match result with
    | .ok c => c.key.kind == 1 && c.signatureKind == 1 && c.key.data.length == 32 &&
      c.signature.length == 64 && c.hostKey.length == 36 && c.usage == 3 &&
      c.notBefore == 0 && c.notAfter == 253402300799
    | _ => false)
  check "should reject a missing libp2p binding"
    (match certificate (sample []) with | .error .missingIdentity => true | _ => false)
  check "should reject repeated identity extensions"
    (match certificate (sample (binding ++ binding)) with | .error .duplicate => true | _ => false)
  check "should reject a truncated certificate header"
    (match certificate [48] with | .error .truncated => true | _ => false)
  for name in Codegen.protocolNames do
    let some (.ok body) := Codegen.protocolRoutine name
      | throw (IO.userError s!"protocol routine unavailable: {name}")
    check s!"should lower and encode the advertised {name} routine"
      (match body.lower with | .ok code => (Rv64.encodeProgram code).isOk | _ => false)
  check "should reject unknown protocol routine names"
    ((Codegen.protocolRoutine "not-a-routine").isNone)

end Libp2pAsm.Tests.CertificateUnit
