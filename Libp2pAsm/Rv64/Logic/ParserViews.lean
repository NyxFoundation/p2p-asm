import Libp2pAsm.Rv64.Logic.ParserByteFrame

namespace Libp2pAsm.Rv64.Logic.Parser

/-- An exhausted view requires no mapping; its cursor may be the wrapped exclusive end. -/
def View (m : Memory) (ptr : Word) (bytes : List UInt8) : Prop := bytes≠[] → BytesAt m ptr bytes

theorem View.reads {m ptr bytes} (h : View m ptr bytes) (hv : m.valid=true) : Reads m ptr bytes := by
  by_cases he : bytes=[]
  · subst bytes; intro i hi; simp at hi
  · exact (h he).reads hv

theorem BytesAt.view {m ptr bytes} (h : BytesAt m ptr bytes) : View m ptr bytes := fun _ => h

theorem View.tail {m ptr b bytes} (h : View m ptr (b::bytes)) : View m (ptr+1) bytes := by
  intro hn
  obtain ⟨index,h⟩ := h (by simp)
  have hindex := h.present
  have hl := h.lower
  have hb := h.nonwrap
  have hf := h.fits
  have hnonempty : 0<bytes.length := List.length_pos_iff.mpr hn
  have hpn : (ptr+1).toNat=ptr.toNat+1 := by
    have hi : ptr.toNat+1<2^64 := by simp only [List.length_cons] at hb; omega
    simp [BitVec.toNat_add,Nat.mod_eq_of_lt hi]
  refine ⟨index,h.present,?_,?_,?_,?_⟩
  · omega
  · simp only [List.length_cons] at hf; omega
  · simp only [List.length_cons] at hb; omega
  · intro i hi
    have he := h.contents (i+1) (by simpa using hi)
    have hp : (ptr+1).toNat-m.regions[index].base.toNat+i=ptr.toNat-m.regions[index].base.toNat+(i+1) := by omega
    simpa only [hp,List.getElem_cons_succ] using he

theorem View.heap_frame {base ptr : Word} {before after : Array UInt8} {frame : List Region}
    {data : List UInt8} {count : Nat}
    (h : View (heap base before true frame) ptr data)
    (hf : ByteFrame 0 count before after) (hs : DisjointSpans base count ptr data.length) :
    View (heap base after true frame) ptr data := fun hn => (h hn).heap_frame hf hs

theorem View.nonwrap {m ptr bytes} (h : View m ptr bytes) : ptr.toNat+bytes.length≤2^64 := by
  by_cases he : bytes=[]
  · subst bytes; have := ptr.isLt; simp; omega
  · exact (h he).nonwrap

theorem DisjointSpans.tail {base ptr : Word} {count : Nat} {b : UInt8} {bytes : List UInt8}
    (h : DisjointSpans base count ptr (b::bytes).length) (hb : ptr.toNat+(b::bytes).length≤2^64) :
    DisjointSpans base count (ptr+1) bytes.length := by
  simp only [List.length_cons] at hb h
  by_cases he : ptr.toNat+1=2^64
  · have hz : bytes.length=0 := by omega
    right
    simp [BitVec.toNat_add,he,hz]
  · have hp : (ptr+1).toNat=ptr.toNat+1 := by
      have hi : ptr.toNat+1<2^64 := by omega
      simp [BitVec.toNat_add,Nat.mod_eq_of_lt hi]
    unfold DisjointSpans at *
    omega

theorem ByteFrame.setIfInBounds {lo count i : Nat} {before : Array UInt8} (v : UInt8)
    (hl : lo≤i) (hu : i<lo+count) : ByteFrame lo count before (before.setIfInBounds i v) := by
  refine ⟨by simp,?_⟩
  intro j hj ha hout
  have hne : i≠j := by omega
  exact Array.getElem_setIfInBounds_ne hj hne

end Libp2pAsm.Rv64.Logic.Parser
