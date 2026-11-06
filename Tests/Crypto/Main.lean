import Tests.Crypto

/- Standalone test-only entry point:
   lake build Tests/Crypto/Main.lean
   lake env lean --run Tests/Crypto/Main.lean
   Uncaught IO exceptions cause a nonzero exit status on assertion failure.
-/
def main : IO Unit := Libp2pAsm.Tests.Crypto.run
