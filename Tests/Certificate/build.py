"""Lake-managed native model, with artifacts only under ignored build/."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def run(command, *, binary=False, timeout=180):
    result = subprocess.run(command, cwd=ROOT, check=True, capture_output=True,
                            text=not binary, timeout=timeout)
    return result.stdout


def compile_probe():
    directory = ROOT/"build/certificate/lake-probe"
    directory.mkdir(parents=True, exist_ok=True)
    (directory/"lean-toolchain").write_bytes((ROOT/"lean-toolchain").read_bytes())
    (directory/"lakefile.toml").write_text('''name = "certificate-probe-package"
version = "0.1.0"
[[require]]
name = "LeanAsm"
git = "https://github.com/NyxFoundation/LeanAsm"
rev = "f8be877a3018dd4338589a00f41d76d1b36a1876"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "certificate-probe"
root = "ProbeMain"
''')
    (directory/"ProbeMain.lean").write_text(
        "import Tests.Certificate.Probe\ndef main := Libp2pAsm.Tests.Certificate.main\n")
    subprocess.run(["lake", "build", "certificate-probe"], cwd=directory, check=True)
    return directory/".lake/build/bin/certificate-probe"
