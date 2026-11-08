import Libp2pAsm
import Libp2pAsm.Refinement.Codec.Axioms
import Tests.AsmCodecProof.Axioms
import Tests.AsmCrypto.ProofAudit
import Tests.HashCrypto.ProofAudit
import Tests.Aead.ProofAudit
import Tests.Curve25519.ProofAudit
import Tests.AbiProof.Axioms
import Tests.Weierstrass.ProofAudit
import Tests.AbiProof.ClockAxioms
import Tests.QuicCrypto.ProofAudit
import Tests.RSA.ProofAudit
import Tests.Tls.ProofAudit
import Tests.CertificateAuth.ProofAudit
import Tests.Kernel.ProofAudit

run_cmd do
  let env ← Lean.getEnv
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for (name, info) in env.constants.toList do
    if (`Libp2pAsm).isPrefixOf name && info.isTheorem then
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "Unexpected proof dependency in {name}: {dependency}"

#print axioms Libp2pAsm.Refinement.Codec.Der.decode_bounds
#print axioms Libp2pAsm.Refinement.Codec.Der.encode_overflow
#print axioms Libp2pAsm.Refinement.Codec.Der.context_zero

#print axioms Libp2pAsm.Spec.Limits.defaults_valid
#print axioms Libp2pAsm.Spec.Limits.defaults_reservations

#print axioms Libp2pAsm.Rv64.SAsm.Cond.neg_neg
#print axioms Libp2pAsm.Rv64.SAsm.Stmt.flatten_length
#print axioms Libp2pAsm.Rv64.State.getReg_setReg_same
#print axioms Libp2pAsm.Rv64.State.getReg_setReg_other
#print axioms Libp2pAsm.Refinement.addWords_sequence_correct
#print axioms Libp2pAsm.Refinement.addWords_run_correct
#print axioms Libp2pAsm.Refinement.buffer_bounds
#print axioms Libp2pAsm.Refinement.resolveBuffer_sound
#print axioms Libp2pAsm.Spec.Crypto.SHA256.hash
#print axioms Libp2pAsm.Spec.Crypto.SHA512.hash
#print axioms Libp2pAsm.Spec.Crypto.HMAC.sha256
#print axioms Libp2pAsm.Spec.Crypto.HKDF.derive
