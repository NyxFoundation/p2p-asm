"""Test-only Lake package; parent source and configuration stay untouched."""
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parents[2]

def compile_probe():
    p = ROOT / 'build/streams/lake-probe'
    p.mkdir(parents=True, exist_ok=True)
    (p/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    (p/'lakefile.toml').write_text('''name = "streams-probe-package"
version = "0.1.0"
[[require]]
name = "LeanAsm"
git = "https://github.com/NyxFoundation/LeanAsm"
rev = "f8be877a3018dd4338589a00f41d76d1b36a1876"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "streams-probe"
root = "ProbeMain"
''')
    (p/'ProbeMain.lean').write_text('import Tests.Streams.Probe\ndef main := Libp2pAsm.Tests.Streams.main\n')
    subprocess.run(['lake', 'build', 'streams-probe'], cwd=p, check=True)
    return p/'.lake/build/bin/streams-probe'

if __name__ == '__main__':
    print(compile_probe())
