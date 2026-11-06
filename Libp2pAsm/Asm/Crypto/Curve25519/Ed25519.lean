import Libp2pAsm.Asm.Crypto.Curve25519.Edwards

namespace Libp2pAsm.Asm.Crypto.Curve25519.Ed25519
open Rv64 Util Link Edwards

/-- a0=seed,a1=32,a2=out,a3=outCapacity,a4=work,a5=capacity.
32-byte public key. Required workspace 4160; stack 384. Caller supplies seed. -/
def publicKey : Except String SAsm.Stmt := program (.seq [
  .asm (block [.ADDI .x16 .x14 0, .ADDI .x17 .x15 0,
    .ADDI .x14 .x12 0, .ADDI .x15 .x13 0, .ADDI .x12 .x0 0, .ADDI .x13 .x0 0]),
  setup false true, expandKey, publish 1760 32]) callees

/-- a0=seed,a1=32,a2=message,a3=messageLen,a4=signatureOut,a5=outCapacity,
a6=work,a7=capacity. Output 64; work=messageLen+4160, stack=384.
No tiny message cap; arithmetic/resource errors precede secret reads and writes.
Status 8=length,5=capacity,4=range/alignment/overlap,1=workspace length overflow. -/
def sign : Except String SAsm.Stmt := program (.seq [
  setup false false, expandKey, reduce 1664 1600 32,
  copyAt 4096 1632 32, hashMessage 32, reduce 1696 1856 64,
  multiply 2080 1920 1696, encode 1792 2080,
  copyAt 4096 1792 32, copyAt 4128 1760 32,
  hashMessage 64, reduce 1728 1856 64,
  .asm (block (ptr .x10 .x19 1824 ++ ptr .x11 .x19 1728 ++
    ptr .x12 .x19 1664 ++ ptr .x13 .x19 1696)), .call 12,
  publish 1792 64]) callees

end Libp2pAsm.Asm.Crypto.Curve25519.Ed25519
