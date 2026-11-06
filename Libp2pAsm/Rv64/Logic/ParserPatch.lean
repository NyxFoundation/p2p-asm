import Libp2pAsm.Rv64.Logic.Writes

namespace Libp2pAsm.Rv64.Logic.Parser

theorem patch_append (before : Array UInt8) (offset : Nat) (xs ys : List UInt8) :
    patchBytes before offset (xs++ys)=patchBytes (patchBytes before offset xs) (offset+xs.length) ys := by
  induction xs generalizing before offset with
  | nil => simp [patchBytes]
  | cons x xs ih =>
    simp only [List.cons_append,patchBytes,ih,List.length_cons]
    congr 1; omega

theorem patch_set_outside (before : Array UInt8) (offset index : Nat) (bytes : List UInt8) (b : UInt8)
    (h : index<offset ∨ offset+bytes.length≤index) :
    patchBytes (before.setIfInBounds index b) offset bytes=
      (patchBytes before offset bytes).setIfInBounds index b := by
  induction bytes generalizing before offset with
  | nil => rfl
  | cons x xs ih =>
    have hne : index≠offset := by simp only [List.length_cons] at h; omega
    have ht : index<offset+1 ∨ offset+1+xs.length≤index := by simp only [List.length_cons] at h; omega
    simp only [patchBytes]
    rw [Array.setIfInBounds_comm b x hne]
    exact ih (before.setIfInBounds offset x) (offset+1) ht

def beBytes : Nat → Nat → List UInt8
  | 0,_ => []
  | n+1,v => beBytes n (v/256)++[v.toUInt8]

@[simp] theorem beBytes_length (n v : Nat) : (beBytes n v).length=n := by
  induction n generalizing v <;> simp [beBytes, *]

def reversePatch : Array UInt8 → Nat → Nat → Nat → Array UInt8
  | before,_,_,0 => before
  | before,offset,value,n+1 => reversePatch
      (before.setIfInBounds (offset+n) value.toUInt8) offset (value/256) n

theorem reversePatch_eq (before : Array UInt8) (offset value n : Nat) :
    reversePatch before offset value n=patchBytes before offset (beBytes n value) := by
  induction n generalizing before value with
  | zero => rfl
  | succ n ih =>
    simp only [reversePatch,ih,beBytes,patch_append,beBytes_length,patchBytes]
    exact patch_set_outside before offset (offset+n) (beBytes n (value/256)) value.toUInt8
      (Or.inr (by simp))

end Libp2pAsm.Rv64.Logic.Parser
