"""Build the SHA-2 probes with Lake; keep generated test artifacts outside source trees."""

import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "build/native/sha2"


def run(command, *, env=None, binary=False, timeout=180):
    result = subprocess.run(command, cwd=ROOT, env=env, check=False,
                            capture_output=True, text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed:\n{result.stdout}\n{result.stderr}")
    return result.stdout


def lean_environment():
    prefix = Path(run(["lake", "env", "lean", "--print-prefix"]).strip())
    paths = (ROOT / ".lake/build/lib/lean", prefix / "lib/lean")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
    return str(prefix / "bin/lean"), env


def audit_proofs(output):
    reports = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    reports += [""] * output.count("does not depend on any axioms")
    if len(reports) != 14:
        raise AssertionError("All word lemmas must be audited")
    for report in reports:
        axioms = {item.strip() for item in report.split(",") if item.strip()}
        if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
            raise AssertionError(f"Unexpected proof dependency: {report}")
    (OUT / "proof-audit.txt").write_text(output)


def build(modules):
    OUT.mkdir(parents=True, exist_ok=True)
    print(run(["lake", "build", *modules]), end="", flush=True)
    lean, env = lean_environment()
    if "Tests.AsmCrypto.ProofAudit" in modules:
        audit_proofs(run([lean, str(ROOT / "Tests/AsmCrypto/ProofAudit.lean")], env=env))
    return lean, env


if __name__ == "__main__":
    build(["Tests.AsmCrypto.Probe"])
