"""Compile the Lean test harness; emitted RV64 remains the runtime under test."""
from native import ROOT, run


def compile_probe():
    print(run(['lake', 'build', 'libp2p-asm-weierstrass-probe'], timeout=900), end='', flush=True)
    return str(ROOT/'.lake/build/bin/libp2p-asm-weierstrass-probe')
