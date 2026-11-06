import Libp2pAsm.Rv64.Logic.WordHeap
import Libp2pAsm.Rv64.Logic.WriteFrame

namespace Libp2pAsm.Rv64.Logic

theorem WriteTrace.empty_reframe {p stop n s t} (h : WriteTrace p stop 0 0 n s t) (lo hi : Nat) :
    WriteTrace p stop lo hi n s t := by
  induction h with
  | nil => exact .nil _
  | @cons n s t u i hn hf he hw tail ih =>
    apply WriteTrace.cons hn hf he _ ih
    have hh := hw.empty
    cases i <;> simp_all [writesMemory, WritesWithin]

theorem ByteFrame.trans {lo count : Nat} {a b c : Array UInt8}
    (hab : ByteFrame lo count a b) (hbc : ByteFrame lo count b c) : ByteFrame lo count a c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro i ha hc hout
  have hb : i < b.size := by rw [← hab.1]; exact ha
  exact (hbc.2 i hb hc hout).trans (hab.2 i ha hb hout)

theorem ByteFrame.widen {lo count lower upper : Nat} {a b : Array UInt8}
    (h : ByteFrame lo count a b) (hl : lower ≤ lo) (hu : lo+count ≤ lower+upper) :
    ByteFrame lower upper a b := by
  exact ⟨h.1, fun i ha hb hout => h.2 i ha hb (by omega)⟩

theorem ByteFrame.write_word {lo count offset : Nat} {before after : Array UInt8} (value : Word)
    (h : ByteFrame lo count before after) (hl : lo ≤ offset) (hu : offset+8 ≤ lo+count) :
    ByteFrame lo count before (writeLE64 after offset value) :=
  h.trans ((writeLE64_frame after offset value).widen hl hu)

theorem readLE64_write_other (bytes : Array UInt8) (offset atOffset : Nat) (value : Word)
    (hb : atOffset+8 ≤ bytes.size) (hd : atOffset+8 ≤ offset ∨ offset+8 ≤ atOffset) :
    readLE64 (writeLE64 bytes offset value) atOffset = readLE64 bytes atOffset :=
  readLE64_frame (writeLE64_frame bytes offset value) hb hd

end Libp2pAsm.Rv64.Logic
