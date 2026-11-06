import Libp2pAsm.Asm.Crypto.Link

/-! Radix 2^51 arithmetic modulo 2^255-19. Algorithms follow the Field51
carry/fold scheme read in HACL* and the RFC 7748 field. See Tests/Curve25519/README.md.
Private ABI: a0=destination, a1/a2=canonical five-limb operands (40 bytes).
Exact aliasing is supported; partial overlaps are not. Preserves all s-regs.
Every operation returns canonical limbs; fixed instruction/address trace.
No external calls, special instructions, lookup tables or spec evaluation. -/
namespace Libp2pAsm.Asm.Crypto.Curve25519.Field
open Rv64 Util

def limbs : List Reg := [.x13, .x14, .x15, .x16, .x17]
def mask : Nat := 2^51-1

private def carry : List Instr :=
  ((limbs.zip (limbs.drop 1)).flatMap fun (a,b) =>
    [.SRLI .x5 a 51, .AND a a .x31, .ADD b b .x5]) ++
  [.SRLI .x5 .x17 51, .AND .x17 .x17 .x31, .ADDI .x6 .x0 19,
   .MUL .x5 .x5 .x6, .ADD .x13 .x13 .x5]

/-- Input limbs <2^63 with only limb zero potentially >2^51. Three full carry
passes precede a branchless conditional subtraction using overflow of x+19. -/
def normalize : List Instr :=
  let sums : List Reg := [.x5, .x6, .x7, .x28, .x29]
  load .x31 mask ++ carry ++ carry ++ carry ++ [.ADDI .x30 .x0 19] ++
  ((limbs.zip sums).flatMap fun (a,b) =>
    [.ADD b a .x30, .SRLI .x30 b 51, .AND b b .x31]) ++
  [.SUB .x30 .x0 .x30] ++
  ((limbs.zip sums).flatMap fun (a,b) =>
    [.XOR b a b, .AND b b .x30, .XOR a a b])

def store : List Instr := limbs.zipIdx.map fun (r,i) => .SD .x10 r (imm (8*i))

def add : SAsm.Stmt := sequence [block <|
  ((limbs.zipIdx).flatMap fun (r,i) =>
    [.LD r .x11 (imm (8*i)), .LD .x5 .x12 (imm (8*i)), .ADD r r .x5]) ++
  normalize ++ store, .ret]

def sub : SAsm.Stmt := sequence [block <|
  load .x7 (2*mask) ++ ((limbs.zipIdx).flatMap fun (r,i) =>
    [.LD r .x11 (imm (8*i)), .LD .x5 .x12 (imm (8*i)), .ADD r r .x7] ++
    (if i == 0 then [.ADDI r r (-36)] else []) ++ [.SUB r r .x5]) ++
  normalize ++ store, .ret]

private def product (column i : Nat) : List Instr :=
  let j := (column+5-i)%5
  [.LD .x5 .x11 (imm (8*i)), .LD .x6 .x12 (imm (8*j))] ++
  (if i+j ≥ 5 then [.MUL .x6 .x6 .x7] else []) ++
  [.MUL .x28 .x5 .x6, .MULHU .x29 .x5 .x6,
   .ADD .x13 .x13 .x28, .SLTU .x30 .x13 .x28,
   .ADD .x14 .x14 .x29, .ADD .x14 .x14 .x30]

/-- Five cyclic convolution columns; sum <95*2^102<2^109. Carry <2^58.
MUL/MULHU form each 128-bit product; SLTU propagates every low-word carry.
48-byte stack scratch is wiped before return; all inputs read before output. -/
def mul : SAsm.Stmt := sequence [block <|
  [.ADDI .x2 .x2 (-48), .ADDI .x17 .x0 0, .ADDI .x7 .x0 19] ++ load .x31 mask ++
  ((List.range 5).flatMap fun c =>
    [.ADDI .x13 .x17 0, .ADDI .x14 .x0 0] ++
    ((List.range 5).flatMap (product c)) ++
    [.AND .x5 .x13 .x31, .SD .x2 .x5 (imm (8*c)),
     .SRLI .x17 .x13 51, .SLLI .x14 .x14 13, .OR .x17 .x17 .x14]) ++
  [.MUL .x28 .x17 .x7] ++
  (limbs.zipIdx.map fun (r,i) => .LD r .x2 (imm (8*i))) ++
  [.ADD .x13 .x13 .x28] ++ normalize ++ store ++
  ((List.range 6).map fun i => .SD .x2 .x0 (imm (8*i))) ++
  [.ADDI .x2 .x2 48], .ret]

/-- RFC decoding: ignore bit 255 and reduce noncanonical inputs. -/
def decode : SAsm.Stmt := sequence [block <|
  ((limbs.zipIdx).flatMap fun (r,i) =>
    let start := (51*i)/8
    let shift := (51*i)%8
    [.ADDI r .x0 0] ++ ((List.range ((51+shift+7)/8)).flatMap fun j =>
      [.LBU .x5 .x11 (imm (start+j)), .SLLI .x5 .x5 (BitVec.ofNat 6 (8*j)), .OR r r .x5]) ++
    [.SRLI r r (BitVec.ofNat 6 shift), .SLLI r r 13, .SRLI r r 13]) ++
  normalize ++ store, .ret]

def encode : SAsm.Stmt := sequence [block <|
  (List.range 32).flatMap fun i =>
    let limb := (8*i)/51
    let shift := (8*i)%51
    [.LD .x5 .x11 (imm (8*limb)), .SRLI .x5 .x5 (BitVec.ofNat 6 shift)] ++
    (if shift > 43 && limb < 4 then
      [.LD .x6 .x11 (imm (8*(limb+1))), .SLLI .x6 .x6 (BitVec.ofNat 6 (51-shift)),
       .OR .x5 .x5 .x6] else []) ++ [.SB .x10 .x5 (imm i)], .ret]

/-- a0/a1=two five-limb elements, a2=bit in {0,1}. -/
def swap : SAsm.Stmt := sequence [block <|
  [.SUB .x7 .x0 .x12] ++ ((List.range 5).flatMap fun i =>
    [.LD .x5 .x10 (imm (8*i)), .LD .x6 .x11 (imm (8*i)), .XOR .x28 .x5 .x6,
     .AND .x28 .x28 .x7, .XOR .x5 .x5 .x28, .XOR .x6 .x6 .x28,
     .SD .x10 .x5 (imm (8*i)), .SD .x11 .x6 (imm (8*i))]), .ret]

end Libp2pAsm.Asm.Crypto.Curve25519.Field
