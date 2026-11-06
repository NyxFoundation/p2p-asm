import Libp2pAsm.Asm.Crypto.GCM.Api
open Libp2pAsm
#eval [("sbox", Asm.Crypto.AES.subBytes 16), ("core", Asm.Crypto.AES.encryptCore),
  ("expand", Asm.Crypto.AES.expand), ("encrypt", Asm.Crypto.AES.encrypt),
  ("ghash", Asm.Crypto.GCM.update), ("ctr", Asm.Crypto.GCM.ctr),
  ("seal", Asm.Crypto.GCM.seal), ("open", Asm.Crypto.GCM.open)].map fun (n,s) => (n,s.size, s.validate)
