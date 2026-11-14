"""Lake owns native compilation of the actual Lean instruction model and Specs."""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'Tests/Tls/.build'


def run(command, *, env=None, binary=False, timeout=3600):
    result = subprocess.run(command, cwd=ROOT, env=env, check=False,
                            capture_output=True, text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{command}:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def build():
    directory = OUT / 'native'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'lakefile.lean').write_text('''import Lake
open Lake DSL
require LeanAsm from git "https://github.com/NyxFoundation/LeanAsm" @ "c55ebfef6eb0a44149deb4110654f71f4fd35543"
package tlsTests where
  srcDir := "../../../.."
  buildDir := "../lake"
lean_lib Libp2pAsm where
  globs := #[.submodules `Libp2pAsm]
  roots := #[`Libp2pAsm.Asm.Tls.Schedule, `Libp2pAsm.Spec.Tls.Schedule]
lean_lib Tests where
  globs := #[.submodules `Tests]
  roots := #[`Tests.Tls.Support]
lean_exe tlsProbe where
  root := `Tests.Tls.Probe
''')
    print(run(['lake', '-d', str(directory), '--no-cache', 'build', 'tlsProbe']), flush=True)
    return str(OUT / 'lake/bin/tlsProbe'), dict(os.environ)
