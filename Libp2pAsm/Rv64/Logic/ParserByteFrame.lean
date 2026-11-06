import Libp2pAsm.Rv64.Logic.ParserDisjoint
import Libp2pAsm.Rv64.Logic.Writes

namespace Libp2pAsm.Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

/-- Disjoint views may share a mapped region; only the writable byte interval must be separate. -/
theorem BytesAtRegion.heap_frame {base ptr : Word} {before after : Array UInt8} {frame : List Region}
    {data : List UInt8} {index count : Nat}
    (h : BytesAtRegion (heap base before true frame) ptr data index)
    (hf : ByteFrame 0 count before after) (hs : DisjointSpans base count ptr data.length) :
    BytesAtRegion (heap base after true frame) ptr data index := by
  cases index with
  | zero =>
    have hl : base.toNat≤ptr.toNat := h.lower
    have hb : ptr.toNat-base.toNat+data.length≤before.size := h.fits
    refine ⟨by simpa [heap] using h.present,hl,?_,h.nonwrap,?_⟩
    · change ptr.toNat-base.toNat+data.length≤after.size
      have := hf.1
      omega
    · intro i hi
      have hiold : ptr.toNat-base.toNat+i<before.size := by omega
      have hinew : ptr.toNat-base.toNat+i<after.size := by have := hf.1; omega
      have hout : count≤ptr.toNat-base.toNat+i := by unfold DisjointSpans at hs; omega
      change after[ptr.toNat-base.toNat+i]=data[i]
      exact (hf.2 _ hiold hinew (Or.inr (by omega))).trans (h.contents i hi)
  | succ index =>
    refine ⟨by simpa [heap] using h.present,?_,?_,h.nonwrap,?_⟩
    · simpa [heap] using h.lower
    · simpa [heap] using h.fits
    · intro i hi; simpa [heap] using h.contents i hi

theorem BytesAt.heap_frame {base ptr : Word} {before after : Array UInt8} {frame : List Region}
    {data : List UInt8} {count : Nat}
    (h : BytesAt (heap base before true frame) ptr data)
    (hf : ByteFrame 0 count before after) (hs : DisjointSpans base count ptr data.length) :
    BytesAt (heap base after true frame) ptr data := by
  obtain ⟨index,h⟩ := h
  exact ⟨index,h.heap_frame hf hs⟩

theorem BytesAt.patch {base ptr : Word} {before : Array UInt8} {frame : List Region}
    {data out : List UInt8} (h : BytesAt (heap base before true frame) ptr data)
    (hs : DisjointSpans base out.length ptr data.length) :
    BytesAt (heap base (patchBytes before 0 out) true frame) ptr data :=
  h.heap_frame (patchBytes_frame before 0 out) hs

end Libp2pAsm.Rv64.Logic.Parser
