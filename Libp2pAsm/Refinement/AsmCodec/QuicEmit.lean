import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Refinement.AsmCodec.QuicLoop
import Libp2pAsm.Rv64.Logic.Writes
import Libp2pAsm.Refinement.AsmCodec.QuicOutput

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

def QuicEmitInv (s : State) (value shift tag : Word) (count : Nat)
    (base : Word) (offset : Nat) (bytes : Array UInt8) (frame : List Region) : Prop :=
  s.getReg .x10 = value ∧ s.getReg .x5 = BitVec.ofNat 64 count ∧
  s.getReg .x6 = shift ∧ s.getReg .x7 = tag ∧
  s.getReg .x11 = base + BitVec.ofNat 64 offset ∧ s.memory = heap base bytes true frame

theorem quic_emit_prepare (s : State) (value shift tag base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k < 8)
    (hs : QuicEmitInv s value shift tag (k+1) base offset bytes frame) :
    ∃ t, WriteTrace quicEncode 0 lower upper 4 (atPC s 65668) t ∧ t.pc = 65684 ∧
      QuicEmitInv t value shift tag (k+1) base offset bytes frame ∧
      t.getReg .x28 = quicByte value shift tag ∧ t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hshift, htag, hptr, hmemory⟩
  have hn := word_length_nonzero (k+1) (by omega) (by omega)
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BEQ .x5 .x0 40)
    write_step (.SRL .x28 .x10 .x6)
    write_step (.ANDI .x28 .x28 255)
    write_step (.OR .x28 .x28 .x7)
    exact .nil _
  case post => simp_all [QuicEmitInv, quicByte, getReg_setReg]

theorem quic_emit_write (s : State) (value shift tag base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region)
    (hi : offset < bytes.size) (hb : base.toNat + bytes.size ≤ 2^64)
    (hv : (heap base bytes true frame).valid = true)
    (hs : QuicEmitInv s value shift tag (k+1) base offset bytes frame)
    (hbyte : s.getReg .x28 = quicByte value shift tag)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ upper) :
    ∃ t, WriteTrace quicEncode 0 lower upper 1 (atPC s 65684) t ∧ t.pc = 65688 ∧
      QuicEmitInv t value shift tag (k+1) base offset
        (bytes.setIfInBounds offset (quicByte value shift tag).toNat.toUInt8) frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hshift, htag, hptr, hmemory⟩
  have hstore := heap_store_at base (quicByte value shift tag) bytes frame offset hv hb hi
  have hsafe : lower ≤ (s.getReg .x11).toNat ∧ (s.getReg .x11).toNat + 1 ≤ upper := by
    rw [hptr]; exact write_address_bounds base offset bytes.size lower upper hb hi hl hh
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.SB .x11 .x28 0)
    exact .nil _
  case post => simp_all [QuicEmitInv]

theorem quic_emit_advance (s : State) (value shift tag base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region)
    (hs : QuicEmitInv s value shift tag (k+1) base offset bytes frame) :
    ∃ t, WriteTrace quicEncode 0 lower upper 5 (atPC s 65688) t ∧ t.pc = 65668 ∧
      QuicEmitInv t value (shift + (-8)) 0 k base (offset+1) bytes frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hshift, htag, hptr, hmemory⟩
  have hd : BitVec.ofNat 64 (k+1) + 18446744073709551615#64 = BitVec.ofNat 64 k := word_succ_decrement k
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step_plain (.ADDI .x11 .x11 1)
    write_step_plain (.ADDI .x5 .x5 (-1))
    write_step_plain (.ADDI .x6 .x6 (-8))
    write_step_plain (.ADDI .x7 .x0 0)
    write_step_plain (.JAL .x0 (-36))
    exact .nil _
  case post =>
    simp [QuicEmitInv, getReg_setReg]
    refine ⟨hvalue, ?_, hshift, ?_, hmemory⟩
    · rw [hcount]; exact hd
    · rw [hptr, BitVec.ofNat_add, BitVec.add_assoc]

theorem quic_emit_store (s : State) (value shift tag base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region)
    (hi : offset < bytes.size) (hb : base.toNat + bytes.size ≤ 2^64)
    (hv : (heap base bytes true frame).valid = true)
    (hs : QuicEmitInv s value shift tag (k+1) base offset bytes frame)
    (hbyte : s.getReg .x28 = quicByte value shift tag)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ upper) :
    ∃ t, WriteTrace quicEncode 0 lower upper 6 (atPC s 65684) t ∧ t.pc = 65668 ∧
      QuicEmitInv t value (shift + (-8)) 0 k base (offset+1)
        (bytes.setIfInBounds offset (quicByte value shift tag).toNat.toUInt8) frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  obtain ⟨a, ha, hapc, hai, haw⟩ := quic_emit_write (lower := lower) (upper := upper) s value shift tag base k offset bytes frame hi hb hv hs hbyte hl hh
  obtain ⟨t, ht, htpc, hti, htw⟩ := quic_emit_advance (lower := lower) (upper := upper) a value shift tag base k offset _ frame hai
  have hjoin : atPC a 65688 = a := by rw [← hapc, atPC_self]
  rw [hjoin] at ht
  exact ⟨t, ha.append ht, htpc, hti, htw.trans haw⟩

theorem quic_emit_iteration (s : State) (value shift tag base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k < 8)
    (hi : offset < bytes.size) (hb : base.toNat + bytes.size ≤ 2^64)
    (hv : (heap base bytes true frame).valid = true)
    (hs : QuicEmitInv s value shift tag (k+1) base offset bytes frame)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ upper) :
    ∃ t, WriteTrace quicEncode 0 lower upper 10 (atPC s 65668) t ∧ t.pc = 65668 ∧
      QuicEmitInv t value (shift + (-8)) 0 k base (offset+1)
        (bytes.setIfInBounds offset (quicByte value shift tag).toNat.toUInt8) frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  obtain ⟨a, ha, hapc, hai, hab, haw⟩ := quic_emit_prepare (lower := lower) (upper := upper) s value shift tag base k offset bytes frame hk hs
  obtain ⟨t, ht, htpc, hti, htw⟩ := quic_emit_store (lower := lower) (upper := upper) a value shift tag base k offset bytes frame hi hb hv hai hab hl hh
  have hjoin : atPC a 65684 = a := by rw [← hapc, atPC_self]
  rw [hjoin] at ht
  exact ⟨t, ha.append ht, htpc, hti, htw.trans haw⟩

theorem quic_emit_loop (k : Nat) (s : State) (value shift tag base : Word) (offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k ≤ 8)
    (hi : offset + k ≤ bytes.size) (hb : base.toNat + bytes.size ≤ 2^64)
    (hv : (heap base bytes true frame).valid = true)
    (hs : QuicEmitInv s value shift tag k base offset bytes frame)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + k ≤ upper) :
    ∃ t, WriteTrace quicEncode 0 lower upper (10*k+1) (atPC s 65668) t ∧ t.pc = 65708 ∧
      t.memory = heap base (patchBytes bytes offset (quicOutput k value shift tag)) true frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  induction k generalizing s shift tag offset bytes with
  | zero =>
    rcases hs with ⟨hvalue, hcount, hshift, htag, hptr, hmemory⟩
    refine ⟨?t, ?trace, ?post⟩
    case trace =>
      write_step (.BEQ .x5 .x0 40)
      exact .nil _
    case post => simp [quicOutput, patchBytes, hmemory]
  | succ k ih =>
    obtain ⟨a, ha, hapc, hai, haw⟩ := quic_emit_iteration (lower := lower) (upper := upper) s value shift tag base k offset
      bytes frame (by omega) (by omega) hb hv hs hl (by omega)
    have hav : (heap base (bytes.setIfInBounds offset (quicByte value shift tag).toNat.toUInt8) true frame).valid = true := by
      rw [← heap_valid_congr base bytes _ true frame (by simp)]; exact hv
    obtain ⟨t, ht, htpc, htm, htw⟩ := ih a (shift + (-8)) 0 (offset+1) _ (by omega)
      (by simp; omega) (by simpa using hb) hav hai (by omega) (by omega)
    have hjoin : atPC a 65668 = a := by rw [← hapc, atPC_self]
    rw [hjoin] at ht
    refine ⟨t, ?_, htpc, htm, htw.trans haw⟩
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha.append ht

end Libp2pAsm.Refinement.AsmCodec
