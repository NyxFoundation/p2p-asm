"""GNU/QEMU harness; all cryptographic instructions are emitted by Lean."""

from pathlib import Path
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def run(command, *, binary=False, timeout=300):
    result = subprocess.run(command, cwd=ROOT, check=False, capture_output=True,
                            text=not binary, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{command[0]} failed:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def regions(kind, f):
    aligned = f['alignment']
    scratch = 1280 if kind in ('seal', 'open') else 0 if kind == 'ghash' else 1024
    sizes = [112, len(f['key'])+16+aligned, len(f['nonce'])+16+aligned,
             len(f['aad'])+16+aligned, len(f['input'])+16+aligned,
             len(f['output'])+16+aligned, scratch+16, 160]
    return [(f'region{i}', 0x200000+0x10000*i, size, i >= 5) for i, size in enumerate(sizes)]


def assemble(prefix, source, output):
    run([prefix+'as', '-march=rv64im', '-mabi=lp64', '-o', str(output), str(source)])


def linker():
    segments = [('text', 5), *[(f'region{i}', 6 if i >= 5 else 4) for i in range(8)], ('capture', 6)]
    text = ['ENTRY(_start)', 'PHDRS {']
    text += [f'  {name} PT_LOAD FLAGS({flags});' for name, flags in segments]
    text += ['}', 'SECTIONS {', '  . = 0x10000;',
             '  .text.protocol : { *(.text.protocol) } :text',
             '  . = 0x80000;', '  .text.return : { *(.text.return) } :text',
             '  .text.start : { *(.text.start) } :text']
    for i in range(8):
        text += [f'  . = {0x200000+0x10000*i};',
                 f'  .data.region{i} : {{ *(.data.region{i}) }} :region{i}']
    text += ['  . = 0x280000;', '  .data.capture : { *(.data.capture) } :capture', '}']
    return '\n'.join(text)+'\n'


def prepare(prefix, directory):
    assemble(prefix, directory/'protocol.S', directory/'protocol.o')
    source = ('.option norvc\n.section .text.protocol, "ax", @progbits\n'
              '.balign 4\n.global protocol_entry\nprotocol_entry:\n'
              f'.incbin "{directory / "encoded.bin"}"\n')
    (directory/'encoded.S').write_text(source)
    (directory/'link.ld').write_text(linker())
    assemble(prefix, directory/'encoded.S', directory/'encoded.o')


def driver(kind, f, before):
    values = struct.unpack('<32Q', before.read_bytes()[:256])
    code = ['.option norvc', '.option norelax', '.section .text.return, "ax", @progbits', 'returned:']
    code += [f'sd x{i}, {8*i}(gp)' for i in range(32)]
    for _, address, size, _ in [('capture', 0x280000, 256, True), *regions(kind, f)]:
        code += ['li a0, 1', f'li a1, {address}', f'li a2, {size}', 'li a7, 64', 'ecall']
    code += ['li a0, 0', 'li a7, 93', 'ecall', '.section .text.start, "ax", @progbits',
             '.global _start', '_start:']
    code += [f'li x{i}, {values[i]}' for i in range(1, 32)]
    code += ['jal x0, protocol_entry']
    offset = 256
    for name, _, size, writable in regions(kind, f):
        flags = 'aw' if writable else 'a'
        code += [f'.section .data.{name}, "{flags}", @progbits',
                 f'.incbin "{before}", {offset}, {size}']
        offset += size
    assert offset == len(before.read_bytes())
    return '\n'.join(code + ['.section .data.capture, "aw", @progbits', '.zero 256'])+'\n'


def execute(prefix, qemu, directory, kind, i, fixture):
    before = directory/f'case-{i}.before.bin'
    expected = (directory/f'case-{i}.expected.bin').read_bytes()
    assert (directory/f'case-{i}.after.bin').read_bytes() == expected
    (directory/'driver.S').write_text(driver(kind, fixture, before))
    assemble(prefix, directory/'driver.S', directory/'driver.o')
    for variant in ('protocol', 'encoded'):
        elf, binary = directory/f'{variant}.elf', directory/f'{variant}.bin'
        run([prefix+'ld', '--no-relax', '-T', str(directory/'link.ld'), '-o', str(elf),
             str(directory/f'{variant}.o'), str(directory/'driver.o')])
        run([prefix+'objcopy', '-O', 'binary', '--only-section=.text.protocol', str(elf), str(binary)])
        assert binary.read_bytes() == (directory/'encoded.bin').read_bytes(), 'GNU encoding mismatch'
        actual = run([qemu, str(elf)], binary=True)
        (directory/f'case-{i}.{variant}.native.bin').write_bytes(actual)
        assert actual == expected, f'QEMU {kind}/{fixture["label"]}/{variant} snapshot mismatch'
