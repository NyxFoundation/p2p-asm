"""Lake owns the complete native dependency graph; no import walker or object cache."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def compile_probe():
    package = ROOT/'build/quic-wire/lake-probe'
    package.mkdir(parents=True, exist_ok=True)
    (package/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    (package/'lakefile.toml').write_text('''name = "quic-wire-probe-package"
version = "0.1.0"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "quic-wire-probe"
root = "ProbeMain"
''')
    (package/'ProbeMain.lean').write_text(
        'import Tests.QuicWire.Probe\ndef main := Libp2pAsm.Tests.QuicWire.main\n')
    subprocess.run(['lake', 'build', 'quic-wire-probe'], cwd=package, check=True)
    return package/'.lake/build/bin/quic-wire-probe'
