import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Refinement.AsmCodec.UnsignedOutput
import Libp2pAsm.Refinement.AsmCodec.QuicEmit
import Libp2pAsm.Refinement.AsmCodec.QuicCorrect

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

def UnsignedEmitInv (s : State) (v : Word) (count : Nat) (base : Word) (offset : Nat)
    (bytes : Array UInt8) (frame : List Region) : Prop :=
  s.getReg .x10 = v ∧ s.getReg .x6 = BitVec.ofNat 64 count ∧
  s.getReg .x11 = base + BitVec.ofNat 64 offset ∧ s.memory = heap base bytes true frame

theorem unsigned_emit_prepare (s : State) (v base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k < 9)
    (hs : UnsignedEmitInv s v (k+1) base offset bytes frame) :
    ∃ n t, n ≤ 6 ∧ WriteTrace unsignedEncode 0 lower upper n (atPC s 65620) t ∧ t.pc = 65644 ∧
      UnsignedEmitInv t (v >>> (7 : Nat)) (k+1) base offset bytes frame ∧
      t.getReg .x28 = unsignedByte v ∧ t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hptr, hmemory⟩
  have hn := word_length_nonzero (k+1) (by omega) (by omega)
  by_cases hz : v >>> (7 : Nat) = 0
  · refine ⟨4, ?first, by decide, ?trace, ?post⟩
    case trace =>
      write_step (.BEQ .x6 .x0 40)
      write_step (.ANDI .x28 .x10 127)
      write_step (.SRLI .x10 .x10 7)
      write_step (.BEQ .x10 .x0 12)
      exact .nil _
    case post => simp_all [UnsignedEmitInv, unsignedByte, getReg_setReg]
  · refine ⟨6, ?second, by decide, ?trace, ?post⟩
    case trace =>
      write_step (.BEQ .x6 .x0 40)
      write_step (.ANDI .x28 .x10 127)
      write_step (.SRLI .x10 .x10 7)
      write_step (.BEQ .x10 .x0 12)
      write_step (.ORI .x28 .x28 128)
      write_step (.JAL .x0 4)
      exact .nil _
    case post => simp_all [UnsignedEmitInv, unsignedByte, getReg_setReg]

theorem unsigned_emit_write (s : State) (v out base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hi : offset < bytes.size)
    (hb : base.toNat + bytes.size ≤ 2^64) (hv : (heap base bytes true frame).valid = true)
    (hs : UnsignedEmitInv s v k base offset bytes frame) (hout : s.getReg .x28 = out)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ upper) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 1 (atPC s 65644) t ∧ t.pc = 65648 ∧
      UnsignedEmitInv t v k base offset (bytes.setIfInBounds offset out.toNat.toUInt8) frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hptr, hmemory⟩
  have hstore := heap_store_at base out bytes frame offset hv hb hi
  have hsafe : lower ≤ (s.getReg .x11).toNat ∧ (s.getReg .x11).toNat + 1 ≤ upper := by
    rw [hptr]; exact write_address_bounds base offset bytes.size lower upper hb hi hl hh
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.SB .x11 .x28 0)
    exact .nil _
  case post => simp_all [UnsignedEmitInv]

theorem unsigned_emit_advance (s : State) (v base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region)
    (hs : UnsignedEmitInv s v (k+1) base offset bytes frame) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 3 (atPC s 65648) t ∧ t.pc = 65620 ∧
      UnsignedEmitInv t v k base (offset+1) bytes frame ∧ t.getReg .x31 = s.getReg .x31 := by
  rcases hs with ⟨hvalue, hcount, hptr, hmemory⟩
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step_plain (.ADDI .x11 .x11 1)
    write_step_plain (.ADDI .x6 .x6 (-1))
    write_step_plain (.JAL .x0 (-36))
    exact .nil _
  case post =>
    simp [UnsignedEmitInv, getReg_setReg]
    refine ⟨hvalue, ?_, ?_, hmemory⟩
    · rw [hcount]; exact word_succ_decrement k
    · rw [hptr, BitVec.ofNat_add, BitVec.add_assoc]

theorem unsigned_emit_iteration (s : State) (v base : Word) (k offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k < 9) (hi : offset < bytes.size)
    (hb : base.toNat + bytes.size ≤ 2^64) (hv : (heap base bytes true frame).valid = true)
    (hs : UnsignedEmitInv s v (k+1) base offset bytes frame)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ upper) :
    ∃ n t, n ≤ 10 ∧ WriteTrace unsignedEncode 0 lower upper n (atPC s 65620) t ∧ t.pc = 65620 ∧
      UnsignedEmitInv t (v >>> (7 : Nat)) k base (offset+1)
        (bytes.setIfInBounds offset (unsignedByte v).toNat.toUInt8) frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  obtain ⟨n, a, hn, ha, hapc, hai, hao, haw⟩ := unsigned_emit_prepare (lower := lower) (upper := upper) s v base k offset bytes frame hk hs
  obtain ⟨b, hbtrace, hbpc, hbi, hbw⟩ := unsigned_emit_write (lower := lower) (upper := upper) a _ _ base (k+1) offset bytes frame hi hb hv hai hao hl hh
  obtain ⟨t, ht, htpc, hti, htw⟩ := unsigned_emit_advance (lower := lower) (upper := upper) b _ base k offset _ frame hbi
  exact ⟨n+1+3, t, by omega, (ha.append (writeTrace_at_pc hapc hbtrace)).append (writeTrace_at_pc hbpc ht),
    htpc, hti, htw.trans (hbw.trans haw)⟩

theorem unsigned_emit_loop (k : Nat) (s : State) (v base : Word) (offset : Nat)
    (bytes : Array UInt8) (frame : List Region) (hk : k ≤ 9) (hi : offset+k ≤ bytes.size)
    (hb : base.toNat + bytes.size ≤ 2^64) (hv : (heap base bytes true frame).valid = true)
    (hs : UnsignedEmitInv s v k base offset bytes frame)
    (hl : lower ≤ base.toNat + offset) (hh : base.toNat + offset + k ≤ upper) :
    ∃ n t, n ≤ 10*k+1 ∧ WriteTrace unsignedEncode 0 lower upper n (atPC s 65620) t ∧ t.pc = 65660 ∧
      t.memory = heap base (patchBytes bytes offset (unsignedOutput k v)) true frame ∧
      t.getReg .x31 = s.getReg .x31 := by
  induction k generalizing s v offset bytes with
  | zero =>
    rcases hs with ⟨hvalue, hcount, hptr, hmemory⟩
    refine ⟨1, ?t, by decide, ?trace, ?post⟩
    case trace =>
      write_step (.BEQ .x6 .x0 40)
      exact .nil _
    case post => simp [unsignedOutput, patchBytes, hmemory]
  | succ k ih =>
    obtain ⟨n, a, hn, ha, hapc, hai, haw⟩ := unsigned_emit_iteration (lower := lower) (upper := upper) s v base k offset bytes frame
      (by omega) (by omega) hb hv hs hl (by omega)
    have hav : (heap base (bytes.setIfInBounds offset (unsignedByte v).toNat.toUInt8) true frame).valid = true := by
      rw [← heap_valid_congr base bytes _ true frame (by simp)]; exact hv
    obtain ⟨m, t, hm, ht, htpc, htm, htw⟩ := ih a (v >>> (7 : Nat)) (offset+1) _ (by omega)
      (by simp; omega) (by simpa using hb) hav hai (by omega) (by omega)
    exact ⟨n+m, t, by omega, ha.append (writeTrace_at_pc hapc ht), htpc, htm, htw.trans haw⟩

end Libp2pAsm.Refinement.AsmCodec
