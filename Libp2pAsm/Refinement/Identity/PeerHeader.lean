import Libp2pAsm.Refinement.Identity.PeerHeaderBlocks

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def header (kind length : Word) : List UInt8 :=
  [0,(length+4).toNat.toUInt8,8,kind.toNat.toUInt8,18,length.toNat.toUInt8]

theorem write_header (s : State) (kind key length out written : Word) (bytes : Array UInt8) (frame : List Region)
    (hi : HeaderInv s kind key length out written bytes frame)
    (hs : 6≤bytes.size) (hb : out.toNat+bytes.size≤2^64) :
    ∃ t, AccessTrace program 0 [] (byteReads out 6) 9 (atPC s 66136) t ∧ t.pc=66172 ∧
      HeaderInv t kind key length out written (patchBytes bytes 0 (header kind length)) frame := by
  obtain ⟨a0,h0,p0,i0⟩ := put 0 s kind key length out written 0 bytes frame hi (by simp [putReg]) hs hb
  obtain ⟨a1,h1,p1,i1,v1⟩ := mark 0 a0 kind key length out written _ frame i0
  obtain ⟨a2,h2,p2,i2⟩ := put 1 a1 kind key length out written (length+4) _ frame i1 v1
    (by simpa using hs) (by simpa using hb)
  obtain ⟨a3,h3,p3,i3,v3⟩ := mark 1 a2 kind key length out written _ frame i2
  obtain ⟨a4,h4,p4,i4⟩ := put 2 a3 kind key length out written 8 _ frame i3 v3
    (by simpa using hs) (by simpa using hb)
  obtain ⟨a5,h5,p5,i5⟩ := put 3 a4 kind key length out written kind _ frame i4 i4.1
    (by simpa using hs) (by simpa using hb)
  obtain ⟨a6,h6,p6,i6,v6⟩ := mark 2 a5 kind key length out written _ frame i5
  obtain ⟨a7,h7,p7,i7⟩ := put 4 a6 kind key length out written 18 _ frame i6 v6
    (by simpa using hs) (by simpa using hb)
  obtain ⟨t,h8,p8,i8⟩ := put 5 a7 kind key length out written length _ frame i7 i7.2.2.1
    (by simpa using hs) (by simpa using hb)
  refine ⟨t,?_,p8,?_⟩
  · have path := (((((((h0.append (accessTrace_at_pc p0 h1)).append (accessTrace_at_pc p1 h2)).append
      (accessTrace_at_pc p2 h3)).append (accessTrace_at_pc p3 h4)).append (accessTrace_at_pc p4 h5)).append
      (accessTrace_at_pc p5 h6)).append (accessTrace_at_pc p6 h7)).append (accessTrace_at_pc p7 h8)
    simpa [byteReads,putPC,BitVec.add_assoc,
      show (3 : Fin 6).val=3 by rfl,show (4 : Fin 6).val=4 by rfl,show (5 : Fin 6).val=5 by rfl] using path
  · simpa [header,patchBytes,
      show (3 : Fin 6).val=3 by rfl,show (4 : Fin 6).val=4 by rfl,show (5 : Fin 6).val=5 by rfl] using i8

theorem setup_copy (s : State) (kind key length out written : Word) (data : List UInt8)
    (bytes : Array UInt8) (frame : List Region) (hi : HeaderInv s kind key length out written bytes frame)
    (hl : length=BitVec.ofNat 64 data.length) (hview : View (heap out bytes true frame) key data) :
    ∃ t, AccessTrace program 0 [] [] 4 (atPC s 66172) t ∧ t.pc=66188 ∧
      CopyInv t out key 6 data written bytes frame := by
  rcases hi with ⟨hk,hkey,hlen,hout,hw,hra,hmem,hvalid⟩
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp_all [CopyInv,getReg_setReg]

abbrev Clear := AsmDer.Encode.Clear

theorem finish (s : State) (written : Word) (hw : s.getReg .x29=written) (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace program 0 [] [] 16 (atPC s 66216) t ∧ t.pc=0 ∧
      t.getReg .x11=written ∧ Clear t ∧ t.memory=s.memory := by
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp [getReg_setReg,Clear,AsmDer.Encode.Clear,Asm.Crypto.Sha2.cleared]

end Libp2pAsm.Refinement.Identity.Peer
