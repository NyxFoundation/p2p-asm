import Libp2pAsm.Refinement.Identity.PeerHeader
import Libp2pAsm.Rv64.Logic.ParserSequential

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def canonical (kind : Word) (data : List UInt8) : List UInt8 :=
  [0,(data.length+4).toUInt8,8,kind.toNat.toUInt8,18,data.length.toUInt8]++data

theorem canonical_spec (kind : Word) (data : List UInt8) (hk : kind.toNat=1 ∨ kind.toNat=2)
    (hl : data.length=31+kind.toNat) : Spec.Identity.PublicKey.peerId kind.toNat data=.ok (canonical kind data) := by
  have hs := Identity.canonical_peerId kind.toNat data hk hl
  have he : data.length+4=35+kind.toNat := by omega
  rw [canonical,he,hl]
  exact hs

theorem header_canonical (kind length : Word) (data : List UInt8)
    (hl : length.toNat=data.length) (hb : data.length≤33) : header kind length++data=canonical kind data := by
  have hs : length.toNat+4<2^64 := by omega
  simp [header,canonical,BitVec.toNat_add,hl,Nat.mod_eq_of_lt (show data.length+4<2^64 by omega)]

theorem body (s : State) (kind key length out : Word) (data : List UInt8) (bytes : Array UInt8) (frame : List Region)
    (hi : HeaderInv s kind key length out (length+6) bytes frame)
    (hlen : length.toNat=data.length) (hsmall : data.length≤33)
    (hinput : BytesAt (heap out bytes true frame) key data)
    (hsep : DisjointSpans out (data.length+6) key data.length)
    (hsize : data.length+6≤bytes.size) (hspan : out.toNat+bytes.size≤2^64) :
    ∃ t, AccessTrace program 0 (byteReads key data.length) (byteReads out (data.length+6))
      (30+7*data.length) (atPC s 66136) t ∧ t.pc=0 ∧ t.getReg .x11=BitVec.ofNat 64 (data.length+6) ∧ Clear t ∧
      t.memory=heap out (patchBytes bytes 0 (canonical kind data)) true frame := by
  obtain ⟨a,ha,hapc,hai⟩ := write_header s kind key length out (length+6) bytes frame hi (by omega) hspan
  have hsep6 : DisjointSpans out (header kind length).length key data.length := by
    unfold DisjointSpans at *; simp only [header,List.length_cons,List.length_nil]; omega
  have hview := (hinput.patch hsep6).view
  have hlword : length=BitVec.ofNat 64 data.length := by rw [←hlen]; simp
  obtain ⟨b,hb,hbpc,hbi⟩ := setup_copy a kind key length out (length+6) data _ frame hai hlword hview
  have hm : (heap out (patchBytes bytes 0 (header kind length)) true frame).valid=true := by
    rw [←hai.2.2.2.2.2.2.1]; exact hai.2.2.2.2.2.2.2
  obtain ⟨c,hc,hcpc,hc29,hc1,hcm⟩ := copy_loop data b out key 6 (data.length+6) (length+6) _ frame
    (by omega) (by simpa using hspan) (by omega) (by simpa using hsize) hsep hm hbi
  obtain ⟨t,ht,hret,hw,hcl,htm⟩ := finish c (length+6) hc29 hc1
  refine ⟨t,?_,hret,?_,hcl,?_⟩
  · have path := ((ha.append (accessTrace_at_pc hapc hb)).append (accessTrace_at_pc hbpc hc)).append
      (accessTrace_at_pc hcpc ht)
    have hn : 9+4+(7*data.length+1)+16=30+7*data.length := by omega
    have hwrites : byteReads out 6++byteReads (out+6#64) data.length=byteReads out (data.length+6) := by
      simpa [Nat.add_comm] using (byteReads_add out 6 data.length).symm
    simpa only [List.nil_append,List.append_nil,hn,BitVec.ofNat_eq_ofNat,hwrites] using path
  · rw [hw,hlword,BitVec.ofNat_add]; rfl
  · rw [htm,hcm]
    have he := patch_append bytes 0 (header kind length) data
    have hlength : (header kind length).length=6 := rfl
    simp only [hlength,Nat.zero_add] at he
    rw [←he,header_canonical kind length data hlen hsmall]

end Libp2pAsm.Refinement.Identity.Peer
