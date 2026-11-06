"""Execute the exact typed-instruction bytes under QEMU; no native crypto oracle."""
import struct

from build import run


def assemble(prefix, source, output):
    run([prefix + "as", "-march=rv64im", "-mabi=lp64", "-o", str(output), str(source)])


def prepare(prefix, directory):
    assemble(prefix, directory / "protocol.S", directory / "protocol.o")
    (directory / "encoded.S").write_text(
        '.option norvc\n.section .text.protocol, "ax", @progbits\n'
        '.balign 4\n.global protocol_entry\nprotocol_entry:\n'
        f'.incbin "{directory / "encoded.bin"}"\n')
    assemble(prefix, directory / "encoded.S", directory / "encoded.o")
    run([prefix + "objcopy", "-O", "binary", "--only-section=.text.protocol",
         str(directory / "protocol.o"), str(directory / "gnu.bin")])
    assert (directory / "gnu.bin").read_bytes() == (directory / "encoded.bin").read_bytes()


def linker(directory):
    headers = ['text PT_LOAD FLAGS(5);', 'dump PT_LOAD FLAGS(6);']
    sections = ['. = 0x10000; .text.protocol : { *(.text.protocol) } :text',
                '. = 0x80000; .text.return : { *(.text.return) } :text',
                '.text.start : { *(.text.start) } :text']
    for i in range(6):
        flags = 6 if i in (2, 3, 5) else 4
        headers.append(f'r{i} PT_LOAD FLAGS({flags});')
        sections.append(f'. = {(i+1)*0x100000}; .data.r{i} : {{ *(.data.r{i}) }} :r{i}')
    sections.append('. = 0x700000; .data.dump : { *(.data.dump) } :dump')
    path = directory / "link.ld"
    path.write_text('ENTRY(_start)\nPHDRS {\n' + '\n'.join(headers) + '\n}\nSECTIONS {\n'
                    + '\n'.join(sections) + '\n}\n')
    return path


def driver(case_dir):
    before = case_dir / "before.bin"
    registers = struct.unpack("<32Q", before.read_bytes()[:256])
    sizes = struct.unpack("<6Q", (case_dir / "sizes.bin").read_bytes())
    code = ['.option norvc', '.option norelax', '.section .text.return, "ax", @progbits']
    code += [f'sd x{i}, {8*i}(gp)' for i in range(32)]
    for address, size in [(0x700000, 256), *[((i+1)*0x100000, n) for i, n in enumerate(sizes)]]:
        code += ['li a0, 1', f'li a1, {address}', f'li a2, {size}', 'li a7, 64', 'ecall']
    code += ['li a0, 0', 'li a7, 93', 'ecall', '.section .text.start, "ax", @progbits',
             '.global _start', '_start:']
    code += [f'li x{i}, {registers[i]}' for i in range(1, 32)]
    code.append('jal x0, protocol_entry')
    offset = 256
    for i, size in enumerate(sizes):
        flags = 'aw' if i in (2, 3, 5) else 'a'
        code += [f'.section .data.r{i}, "{flags}", @progbits', f'.incbin "{before}", {offset}, {size}']
        offset += size
    code += ['.section .data.dump, "aw", @progbits', '.zero 256']
    return '\n'.join(code) + '\n'


def execute(args, directory, case_dir, expected, script):
    (case_dir / "driver.S").write_text(driver(case_dir))
    assemble(args.prefix, case_dir / "driver.S", case_dir / "driver.o")
    for kind in ("protocol", "encoded"):
        elf = case_dir / f"{kind}.elf"
        run([args.prefix + "ld", "--no-relax", "-T", str(script), "-o", str(elf),
             str(directory / f"{kind}.o"), str(case_dir / "driver.o")])
        binary = case_dir / f"{kind}.program.bin"
        run([args.prefix + "objcopy", "-O", "binary", "--only-section=.text.protocol",
             str(elf), str(binary)])
        assert binary.read_bytes() == (directory / "encoded.bin").read_bytes(), "linked code differs"
        actual = run([args.qemu, str(elf)], binary=True)
        (case_dir / f"{kind}.native.bin").write_bytes(actual)
        assert actual == expected, f'{case_dir.name} {kind}: native snapshot mismatch'
