import Libp2pAsm.Asm.Identity.X509.Common

namespace Libp2pAsm.Asm.Identity.X509.Strings
open Rv64 Crypto.Util

private def input : SAsm.Stmt := block [
  .ADD .x10 .x9 .x25, .ADDI .x11 .x26 0]

private def advance : SAsm.Stmt := block [
  .ADDI .x10 .x10 1, .ADDI .x11 .x11 (-1)]

private def scalar : SAsm.Stmt := sequence [
  block (load .x5 0x10ffff), require (.geu .x5 .x12),
  block (load .x5 0xd800),
  .ite (.geu .x12 .x5) (sequence [block (load .x5 0xe000),
    require (.geu .x12 .x5)]) empty]

def wide (width : Nat) : SAsm.Stmt := sequence [input,
  block [.ANDI .x5 .x11 (imm (width-1))], require (.eq .x5 .x0),
  .loop (.ne .x11 .x0) (sequence (
    [tick, block [.ADDI .x12 .x0 0]] ++
    ((List.range width).map fun i => block [.LBU .x13 .x10 (imm i),
      .SLLI .x12 .x12 8, .OR .x12 .x12 .x13]) ++
    [scalar, block [.ADDI .x10 .x10 (imm width), .ADDI .x11 .x11 (BitVec.ofInt 12 (-(width : Int)))]]))]

private def rangeFlag (lo hi : Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 (imm lo)],
  .ite (.geu .x12 .x5) (sequence [block [.ADDI .x5 .x0 (imm (hi+1))],
    .ite (.ltu .x12 .x5) (block [.ADDI .x13 .x0 1]) empty]) empty]

private def printable : SAsm.Stmt := sequence (
  [block [.ADDI .x13 .x0 0], rangeFlag 65 90, rangeFlag 97 122, rangeFlag 48 57] ++
  ([32,39,40,41,43,44,45,46,47,58,61,63].map fun n => sequence [
    block [.ADDI .x5 .x0 (imm n)],
    .ite (.eq .x12 .x5) (block [.ADDI .x13 .x0 1]) empty]) ++
  [require (.ne .x13 .x0)])

def ascii (tag : Nat) : SAsm.Stmt := sequence [input,
  .loop (.ne .x11 .x0) (sequence [tick, block [.LBU .x12 .x10 0],
    if tag == 19 then printable else if tag == 22 then sequence [
      block [.ADDI .x5 .x0 128], require (.ltu .x12 .x5)]
    else sequence [block [.ADDI .x5 .x0 32],
      .ite (.ne .x12 .x5) (sequence [
        block [.ADDI .x5 .x0 48], require (.geu .x12 .x5),
        block [.ADDI .x5 .x0 58], require (.ltu .x12 .x5)]) empty],
    advance])]

private def utfLead : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 128],
  .ite (.geu .x15 .x5) (sequence [
    block [.ADDI .x5 .x0 194], require (.geu .x15 .x5),
    block [.ADDI .x5 .x0 224, .ADDI .x12 .x0 1,
      .ADDI .x13 .x0 128, .ADDI .x14 .x0 191],
    .ite (.geu .x15 .x5) (sequence [
      block [.ADDI .x12 .x0 2, .ADDI .x5 .x0 240],
      .ite (.ltu .x15 .x5) (sequence [
        block [.ADDI .x5 .x0 224],
        .ite (.eq .x15 .x5) (block [.ADDI .x13 .x0 160]) empty,
        block [.ADDI .x5 .x0 237],
        .ite (.eq .x15 .x5) (block [.ADDI .x14 .x0 159]) empty]) (sequence [
        block [.ADDI .x5 .x0 245], require (.ltu .x15 .x5),
        block [.ADDI .x12 .x0 3, .ADDI .x5 .x0 240],
        .ite (.eq .x15 .x5) (block [.ADDI .x13 .x0 144]) empty,
        block [.ADDI .x5 .x0 244],
        .ite (.eq .x15 .x5) (block [.ADDI .x14 .x0 143]) empty])]) empty]) empty]

def utf8 : SAsm.Stmt := sequence [input, block [.ADDI .x12 .x0 0],
  .loop (.ne .x11 .x0) (sequence [tick, block [.LBU .x15 .x10 0],
    .ite (.eq .x12 .x0) utfLead (sequence [
      require (.geu .x15 .x13), require (.geu .x14 .x15),
      block [.ADDI .x12 .x12 (-1), .ADDI .x13 .x0 128, .ADDI .x14 .x0 191]]),
    advance]), require (.eq .x12 .x0)]

end Libp2pAsm.Asm.Identity.X509.Strings
