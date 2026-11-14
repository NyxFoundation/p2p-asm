"""Build an isolated, ignored Lake package without changing frozen sources."""
import os
from pathlib import Path
import shutil
import subprocess
ROOT=Path(__file__).resolve().parents[2]
PACKAGE=ROOT/'build/kernel/lake-probe'


def prepare():
    PACKAGE.mkdir(parents=True,exist_ok=True)
    for part in ('Libp2pAsm','Tests/Kernel'):
        for p in (ROOT/part).rglob('*.lean'):
            dst=PACKAGE/p.relative_to(ROOT);dst.parent.mkdir(parents=True,exist_ok=True)
            if not dst.exists() or dst.read_bytes()!=p.read_bytes(): shutil.copyfile(p,dst)
    policy=Path(os.environ.get('KERNEL_FROZEN_ROOT',str(ROOT.parent/'p2p-asm')))
    for rel in ('Libp2pAsm/Spec/Limits.lean','Libp2pAsm/Spec/Limits/Types.lean'):
        src=ROOT/rel if (ROOT/rel).exists() else policy/rel
        dst=PACKAGE/rel;dst.parent.mkdir(parents=True,exist_ok=True)
        if not dst.exists() or src.read_bytes()!=dst.read_bytes(): shutil.copyfile(src,dst)
    (PACKAGE/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    (PACKAGE/'lakefile.toml').write_text('''name = "kernel-tests"
version = "0.1.0"
[[require]]
name = "LeanAsm"
git = "https://github.com/NyxFoundation/LeanAsm"
rev = "c55ebfef6eb0a44149deb4110654f71f4fd35543"
[[lean_lib]]
name = "Libp2pAsm"
[[lean_lib]]
name = "Tests"
[[lean_exe]]
name = "kernel-probe"
root = "ProbeMain"
''')
    (PACKAGE/'ProbeMain.lean').write_text('import Tests.Kernel.Probe\ndef main := Libp2pAsm.Tests.Kernel.main\n')
    return PACKAGE


def build(*targets):
    p=prepare()
    subprocess.run(['lake','build',*targets],cwd=p,check=True)
    return p/'.lake/build/bin/kernel-probe'

if __name__=='__main__':
    import sys
    build(*sys.argv[1:])
