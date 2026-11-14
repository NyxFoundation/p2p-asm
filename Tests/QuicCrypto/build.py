"""Native compiled Lean model/spec; all generated files in ignored build/quic."""
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'build/quic'

def run(command, *, env=None, binary=False, timeout=3600):
    result=subprocess.run(command,cwd=ROOT,env=env,check=False,capture_output=True,
                          text=not binary,timeout=timeout)
    if result.returncode: raise RuntimeError(f'{command}:\n{result.stdout}\n{result.stderr}')
    return result.stdout

def build():
    directory=OUT/'native'
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'lakefile.lean').write_text('''import Lake
open Lake DSL
require LeanAsm from git "https://github.com/NyxFoundation/LeanAsm" @ "c55ebfef6eb0a44149deb4110654f71f4fd35543"
package quicTests where
  srcDir := "../../.."
  buildDir := "../lake"
lean_lib Libp2pAsm where
  globs := #[.submodules `Libp2pAsm]
  roots := #[`Libp2pAsm.Asm.Crypto.Quic.Kdf, `Libp2pAsm.Asm.Crypto.Quic.Packet,
    `Libp2pAsm.Asm.Crypto.Quic.Retry, `Libp2pAsm.Spec.Crypto.Quic.Packet]
lean_lib Tests where
  globs := #[.submodules `Tests]
  roots := #[`Tests.QuicCrypto.Support]
lean_exe quicProbe where
  root := `Tests.QuicCrypto.Probe
''')
    print(run(['lake','-d',str(directory),'--no-cache','build','quicProbe']),flush=True)
    return str(OUT/'lake/bin/quicProbe'),dict(os.environ)
