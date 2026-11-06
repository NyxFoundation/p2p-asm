import Libp2pAsm.Spec.Tls.Schedule
import Libp2pAsm.Spec.Tls.Cursor
import Libp2pAsm.Asm.Tls.Schedule
import Libp2pAsm.Asm.Tls.Cursor
import Libp2pAsm.Refinement.Registers
import Libp2pAsm.Rv64.Execution

/-! These are helper/leaf-fragment claims. They do not prove a TLS state
machine, identities, crypto security, full refinement, fetch, or constant time. -/
namespace Libp2pAsm.Refinement.Tls
open Rv64

theorem take_success_bounds (c : Spec.Tls.Cursor) (n : Nat)
    (s : Spec.Tls.Slice) (next : Spec.Tls.Cursor) (h : c.take n = .ok (s,next)) :
    s.offset = c.pos ∧ s.length = n ∧ next.pos = c.pos+n ∧ next.stop = c.stop ∧
    s.valid c.input.size ∧ next.valid := by
  unfold Spec.Tls.Cursor.take at h
  dsimp at h
  split at h
  · change (Except.error Spec.Tls.Error.malformed : Except Spec.Tls.Error _) = .ok (s,next) at h
    cases h
  · simp [pure, Except.pure] at h
    rcases h with ⟨rfl,rfl⟩
    simp_all [Spec.Tls.Slice.valid, Spec.Tls.Cursor.valid]
    omega

theorem take_remaining (pos stop n : Nat) (hp : pos ≤ stop) (hn : n ≤ stop-pos) :
    pos+n ≤ stop ∧ stop-(pos+n) = (stop-pos)-n := by omega

theorem vector24_bounds (n : Nat) (hn : n < 2^24) :
    n+4 < 2^25 ∧ n+4 < 2^64 := by omega

theorem header24_roundtrip (n : Nat) (h : n < 2^24) :
    (Spec.Tls.be 3 n).foldl (fun a b => 256*a+b.toNat) 0 = n := by
  simp [Spec.Tls.be, Spec.Crypto.Sha2.encodeBE, List.range_succ, Nat.toUInt8]
  omega

theorem bitmap_address_bound (id : Nat) (h : id < 2^16) :
    id/8 < 8192 ∧ id%8 < 8 ∧ 8704+id/8 < Asm.Tls.Cursor.workspaceBytes := by
  unfold Asm.Tls.Cursor.workspaceBytes
  omega

theorem distinct_bitmap_position (a b : Nat)
    (hbyte : a/8 = b/8) (hbit : a%8 = b%8) : a = b := by omega

theorem span_nonwrap_last (ptr size : Nat) (hp : ptr < 2^64) (hs : 0 < size) :
    size-1 ≤ (2^64-1)-ptr ↔ ptr+size ≤ 2^64 := by omega

theorem staged_regions_separate : 224 ≤ 256 ∧ 256+54 ≤ 384 ∧ 384+32 ≤ 416 ∧
    416+32 ≤ 512 ∧ 512+1024 = Asm.Tls.Schedule.workspaceBytes := by decide

theorem schedule_label_handshake :
    Asm.Tls.Schedule.labelPrefix "c hs traffic" 32 =
      [0,32,18,116,108,115,49,51,32,99,32,104,115,32,116,114,97,102,102,105,99,32] := by decide

theorem schedule_label_finished :
    Asm.Tls.Schedule.labelPrefix "finished" 0 =
      [0,32,14,116,108,115,49,51,32,102,105,110,105,115,104,101,100,0] := by decide

theorem finished_context_empty (secret digest : Spec.Tls.Bytes) :
    Spec.Tls.Schedule.finished secret digest = do
      if secret.size != 32 || digest.size != 32 then throw .malformed
      let key ← Spec.Tls.Schedule.expandLabel secret "finished" #[]
      let tag ← Spec.Crypto.HMAC.sha256 key.toList digest.toList
        |>.mapError (fun _ => Spec.Tls.Error.crypto)
      return key ++ tag.toArray := by rfl

theorem hrr_synthetic_header (ch : Spec.Tls.Bytes) (limit : Nat) :
    Spec.Tls.Schedule.messageHash ch limit = do
      return #[254,0,0,32] ++ (← Spec.Tls.Schedule.hash ch limit) := by rfl

/-- Correspondence for the ACTUAL two-instruction cursor remaining fragment,
under symbolic registers and memory; execution effects include the PC. -/
theorem remaining_fragment (s : State) :
    execSequence [.SUB .x5 .x18 .x9] s =
      .ok ((s.setReg .x5 (s.getReg .x18-s.getReg .x9)).advance) := by rfl

theorem remaining_in_need :
    (Asm.Tls.Cursor.need .x11).flatten.take 1 = [.SUB .x5 .x18 .x9] := by decide

theorem cursor_subtraction_exact (pos stop : Nat) (hp : pos ≤ stop) (hs : stop < 2^64) :
    ((BitVec.ofNat 64 stop)-(BitVec.ofNat 64 pos)).toNat = stop-pos := by
  simp [BitVec.toNat_sub]
  omega

end Libp2pAsm.Refinement.Tls
