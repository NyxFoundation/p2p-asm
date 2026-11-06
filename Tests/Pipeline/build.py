"""Isolated Lake build of the chain probe; artifacts only under ignored build/."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def compile_probe():
    directory = ROOT / "build/pipeline/lake-probe"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
    (directory / "lakefile.toml").write_text('''name = "pipeline-probe-package"
version = "0.1.0"
[[require]]
name = "libp2p-asm"
path = "../../.."
[[lean_exe]]
name = "pipeline-probe"
root = "ProbeMain"
''')
    (directory / "ProbeMain.lean").write_text(
        "import Tests.Pipeline.Probe\ndef main := Libp2pAsm.Tests.Pipeline.main\n")
    result = subprocess.run(["lake", "build", "pipeline-probe"], cwd=directory,
                            capture_output=True, text=True, timeout=1800)
    if result.returncode:
        raise RuntimeError(f"lake build failed:\n{result.stdout}\n{result.stderr}")
    return directory / ".lake/build/bin/pipeline-probe"
