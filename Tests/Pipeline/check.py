#!/usr/bin/env python3
"""Run the ASM-core chain fixture through the lowered leaf instruction sequences."""
from pathlib import Path
from build import compile_probe
import fixtures

ROOT = Path(__file__).resolve().parents[2]


def main():
    directory = ROOT / "build"
    artifacts = directory / "pipeline"
    artifacts.mkdir(parents=True, exist_ok=True)
    case = fixtures.build_case()
    import shutil
    shutil.copy(Path(__file__).resolve().parent / "case.json",
                artifacts / "case.json")
    probe = compile_probe()
    import subprocess
    result = subprocess.run([str(probe), str(artifacts)], cwd=ROOT,
                            capture_output=True, text=True, timeout=1800)
    print(result.stdout, end="")
    if result.returncode:
        raise SystemExit(result.stderr)
    lines = result.stdout.strip().splitlines()
    passing = sum(1 for line in lines if line.startswith("PASS"))
    assert passing == len(case["stages"]) + 1, lines
    print(f"PASS pipeline: {len(case['stages'])} stages through lowered RV64 leaves")


if __name__ == "__main__":
    main()
