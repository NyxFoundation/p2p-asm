import Libp2pAsm.Refinement.AsmDer.Specification
import Libp2pAsm.Refinement.AsmCodec.EncodeArithmetic

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic AsmCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem tag_low (b : UInt8) :
    BitVec.ofNat 64 b.toNat &&& (31 : Word)=BitVec.ofNat 64 (b.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.toNat_lt
  simp only [BitVec.toNat_and,byte_word_nat]
  change b.toNat &&& 31=(b.toNat%32)%2^64
  rw [show b.toNat &&& 31=b.toNat%32 from Nat.and_two_pow_sub_one_eq_mod b.toNat 5]
  omega

theorem tag_zero (b : UInt8) :
    BitVec.ofNat 64 b.toNat &&& (18446744073709551583 : Word)=0 ↔ b.toNat=0 ∨ b.toNat=32 := by
  have all : ∀ n : Fin 256,
      BitVec.ofNat 64 n.val &&& (18446744073709551583 : Word)=0 ↔ n.val=0 ∨ n.val=32 := by decide
  exact all ⟨b.toNat,b.toNat_lt⟩

theorem byte_high_zero (b : UInt8) : BitVec.ofNat 64 b.toNat >>> (8 : Nat)=0 := by
  apply (word_shift_zero_iff _ 8).mpr
  simpa [byte_word_nat] using b.toNat_lt

theorem tag_supported (b : UInt8) : Spec.Codec.Der.supportedTag b.toNat=true ↔
    b.toNat%32 ≠ 31 ∧ b.toNat ≠ 0 ∧ b.toNat ≠ 32 := by
  have hb := b.toNat_lt
  simp [Spec.Codec.Der.supportedTag,hb]
  omega

theorem long_flag (b : UInt8) :
    BitVec.ofNat 64 b.toNat &&& (128 : Word)=0 ↔ b.toNat < 128 := by
  have all : ∀ n : Fin 256, BitVec.ofNat 64 n.val &&& (128 : Word)=0 ↔ n.val<128 := by decide
  exact all ⟨b.toNat,b.toNat_lt⟩

theorem word_byte_eq (b : UInt8) (n : Nat) (hn : n < 256) :
    BitVec.ofNat 64 b.toNat=BitVec.ofNat 64 n ↔ b.toNat=n := by
  rw [← BitVec.toNat_inj]
  simp [byte_word_nat,Nat.mod_eq_of_lt (show n < 2^64 by omega)]

end Libp2pAsm.Refinement.AsmDer
