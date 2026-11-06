"""Lake owns the complete native dependency graph; no import walker or object cache."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def compile_probe():
    package = ROOT/'build/rsa/lake-probe'
    package.mkdir(parents=True, exist_ok=True)
    (package/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    (package/'lakefile.toml').write_text('''name = "rsa-probe-package"
version = "0.1.0"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "rsa-probe"
root = "ProbeMain"
''')
    (package/'ProbeMain.lean').write_text(
        'import Tests.RSA.Probe\ndef main := Libp2pAsm.Tests.RSA.main\n')
    subprocess.run(['lake', 'build', 'rsa-probe'], cwd=package, check=True)
    return package/'.lake/build/bin/rsa-probe'
