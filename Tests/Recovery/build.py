"""Isolated Lake build; never writes another worker's build artifacts."""
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'Tests/Recovery/.build'


def run(command, *, env=None, binary=False, timeout=3600):
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                            text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{command}:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def build():
    directory = OUT / 'native'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'lakefile.lean').write_text('''import Lake
open Lake DSL
require LeanAsm from git "https://github.com/NyxFoundation/LeanAsm" @ "f8be877a3018dd4338589a00f41d76d1b36a1876"
package recoveryTests where
  srcDir := "../../../.."
  buildDir := "../lake"
lean_lib Libp2pAsm
lean_lib Tests
lean_exe recoveryProbe where
  root := `Tests.Recovery.Probe
''')
    print(run(['lake', '-d', str(directory), '--no-cache', 'build', 'recoveryProbe']), flush=True)
    return str(OUT / 'lake/bin/recoveryProbe'), dict(os.environ)
