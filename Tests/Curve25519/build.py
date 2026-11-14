"""Lake owns all dependencies. Artifacts are under the ignored root build/."""
import os
from pathlib import Path
import subprocess
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'build/curve25519'


def run(command, *, env=None, binary=False, timeout=3600):
    result = subprocess.run(command, cwd=ROOT, env=env, check=False,
                            capture_output=True, text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def native_config():
    directory=OUT/'native'
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'lakefile.lean').write_text("""import Lake
open Lake DSL
require LeanAsm from git "https://github.com/NyxFoundation/LeanAsm" @ "f8be877a3018dd4338589a00f41d76d1b36a1876"
package curveTests where
  srcDir := "../../.."
  buildDir := "../lake"
lean_lib Libp2pAsm where
  globs := #[.submodules `Libp2pAsm]
  roots := #[`Libp2pAsm.Asm.Crypto.Curve25519.X25519,
    `Libp2pAsm.Asm.Crypto.Curve25519.Ed25519,
    `Libp2pAsm.Asm.Crypto.Curve25519.Verify,
    `Libp2pAsm.Spec.Crypto.Curve25519.X25519,
    `Libp2pAsm.Spec.Crypto.Curve25519.Ed25519,
    `Libp2pAsm.Refinement.Crypto.Curve25519.Bounds]
lean_lib Tests where
  globs := #[.submodules `Tests]
  roots := #[`Tests.Curve25519.Support]
lean_exe curve25519Probe where
  root := `Tests.Curve25519.Probe
lean_exe curve25519IterateSpec where
  root := `Tests.Curve25519.IterateSpec
""")
    return directory


def build():
    directory=native_config()
    print(run(['lake','-d',str(directory),'--no-cache','build','curve25519Probe']),flush=True)
    return str(OUT/'lake/bin/curve25519Probe'),dict(os.environ)


def audit():
    print(run(['lake','--no-cache','build','+Tests.Curve25519.ProofAudit:olean',
               '+Tests.Curve25519.FieldProbe:olean']),flush=True)
    report=run(['lake','env','lean','Tests/Curve25519/ProofAudit.lean'])
    axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',report)
    assert len(axioms)+report.count('does not depend on any axioms')==15
    for group in axioms:
        assert {s.strip() for s in group.split(',')} <= {'propext','Classical.choice','Quot.sound'}
    (OUT/'proof-audit.txt').write_text(report)
    print(run(['lake','env','lean','--run','Tests/Curve25519/FieldProbe.lean']),end='',flush=True)
