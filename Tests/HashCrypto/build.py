"""Use Lake's module build graph; keep test artifacts in the ignored directory."""

import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "build/native/hashes"


def run(command, *, env=None, binary=False, timeout=180):
    result = subprocess.run(command, cwd=ROOT, env=env, check=False,
                            capture_output=True, text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed:\n{result.stdout}\n{result.stderr}")
    return result.stdout


def lean_environment():
    prefix = Path(run(["lake", "env", "lean", "--print-prefix"]).strip())
    lean_path = run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    return str(prefix / "bin/lean"), dict(os.environ, LEAN_PATH=lean_path)


def audit_proofs(output):
    reports = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    reports += [""] * output.count("does not depend on any axioms")
    assert len(reports) == 12, "all composition lemmas must be audited"
    for report in reports:
        axioms = {item.strip() for item in report.split(",") if item.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, report
    (OUT / "proof-audit.txt").write_text(output)


def build(modules):
    OUT.mkdir(parents=True, exist_ok=True)
    targets = [f"+{module}:olean" for module in modules]
    print(run(["lake", "--no-cache", "build", *targets], timeout=300), end="", flush=True)
    lean, env = lean_environment()
    if "Tests.HashCrypto.ProofAudit" in modules:
        source = ROOT / "Tests/HashCrypto/ProofAudit.lean"
        audit = run([lean, str(source)], env=env)
        audit_proofs(audit)
        print(audit, end="", flush=True)
    return lean, env


if __name__ == "__main__":
    build(["Tests.HashCrypto.ProofAudit", "Tests.HashCrypto.Probe"])
