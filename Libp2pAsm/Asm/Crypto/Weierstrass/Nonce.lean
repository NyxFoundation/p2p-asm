import Libp2pAsm.Asm.Crypto.Weierstrass.Keys

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

/-- HMAC always uses the actual shared SHA256 instructions. Key at800, V at832,
seed d at864,z at896, concat928..1025, work1088..2049 (961 bytes maximum).
These ranges are disjoint; output may alias input K/V because HMAC normalizes
and consumes its entire message before writing its final digest. -/
def mac (message length output : Nat) : Part := .seq [
  .asm (block [.ADDI .x10 .x8 800, .ADDI .x11 .x0 32,
    .ADDI .x12 .x8 (imm message), .ADDI .x13 .x0 (imm length),
    .ADDI .x14 .x8 (imm output), .ADDI .x15 .x8 1088,
    .ADDI .x16 .x0 961, .LD .x17 .x9 96]), .call 12]

/-- bits2octets: exactly one subtraction suffices for a 256-bit SHA256 digest
because both group orders are >2^255. Ordinary arithmetic via modular addition0. -/
def digestScalar : Part := .seq [
  .asm (block [.LD .x11 .x9 32]), .asm (decode .x8 .x11 32 0),
  .asm (zeroWords .x8 640 4), op 4 32 32 640]

def seedMessage (tag : Nat) : Part := .asm <| sequence [
  wordsCopy .x8 .x8 928 832,
  block [.ADDI .x5 .x0 (imm tag), .SB .x8 .x5 960,
    .ADDI .x10 .x8 961, .ADDI .x11 .x8 864, .ADDI .x12 .x0 64],
  copy .x10 .x11 .x12]

def acceptCandidate (c : Curve) : Part := .seq [
  .asm (canonical .x8 128 c.order .x23 true),
  .asm (block [.SUB .x22 .x0 .x23, .ADDI .x10 .x8 128,
    .ADDI .x11 .x8 128, .ADDI .x12 .x8 544]),
  .asm (maskSelect .x10 .x11 .x12 .x22)]

/-- RFC6979 section3.2, one bounded candidate. No reduction of the candidate.
The signer reports10 for out-of-range k or zero r/s, with no signature output.
Applications must propagate this explicit error; resubmitting the same tuple is
deterministic. There is no random fallback, nonce substitution or biased output.
Invalid candidates are replaced internally by1 solely to keep the trace fixed;
the result is always suppressed. No retry branch reveals private state. -/
def nonce (c : Curve) : Part := .seq [
  digestScalar, .asm (encode .x8 .x8 864 0), .asm (encode .x8 .x8 896 32),
  .asm (zeroWords .x8 800 4),
  .asm (constant .x8 832 ((2^256-1)/255)),
  seedMessage 0, mac 928 97 800, mac 832 32 832,
  seedMessage 1, mac 928 97 800, mac 832 32 832, mac 832 32 832,
  .asm (block [.ADDI .x11 .x8 832]), .asm (decode .x8 .x11 128 0),
  acceptCandidate c]

end Libp2pAsm.Asm.Crypto.Weierstrass
