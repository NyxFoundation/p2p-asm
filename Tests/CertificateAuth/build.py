"""Isolated ignored Lake executable; root Lake configuration remains frozen."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def compile_probe():
    directory = ROOT / 'build/certificate-auth/lake-probe'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
    (directory / 'lakefile.toml').write_text('''name = "certificate-auth-tests"
version = "0.1.0"
[[require]]
name = "LeanAsm"
git = "https://github.com/NyxFoundation/LeanAsm"
rev = "c55ebfef6eb0a44149deb4110654f71f4fd35543"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "certificate-auth-probe"
root = "ProbeMain"
''')
    (directory / 'ProbeMain.lean').write_text(
        'import Tests.CertificateAuth.Probe\n'
        'def main := Libp2pAsm.Tests.CertificateAuth.main\n')
    subprocess.run(['lake', 'build', 'certificate-auth-probe'], cwd=directory, check=True)
    return directory / '.lake/build/bin/certificate-auth-probe'


if __name__ == '__main__':
    print(compile_probe())
