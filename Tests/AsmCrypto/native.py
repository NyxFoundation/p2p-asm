"""Native harness only: the crypto routine always comes from typed Lean emission."""

from pathlib import Path
import struct

from build import ROOT, run

PRESERVED = (1, 2, 3, 4, 8, 9, *range(18, 28))


def regions(width, case):
    rounds = 64 if width == 32 else 80
    return (("state", 0x20000, 80, True),
            ("input", 0x30000, 2 * width + 16 + case % 8, False),
            ("constants", 0x40000, rounds * 8 + 16, False),
            ("scratch", 0x50000, rounds * 8 + 16, True),
            ("stack", 0x60000, 96, True))


def expected_snapshot(before, result, width, case):
    registers = struct.unpack("<32Q", before[:256])
    output = struct.pack("<32Q", *(value if i in PRESERVED else 0
                                   for i, value in enumerate(registers)))
    offset = 256
    for name, _, size, _ in regions(width, case):
        original = before[offset:offset + size]
        if name == "state":
            original = original[:8] + struct.pack("<8Q", *result) + original[-8:]
        elif name == "scratch":
            original = original[:8] + bytes(size - 16) + original[-8:]
        elif name == "stack":
            original = original[:16] + bytes(64) + original[-16:]
        output += original
        offset += size
    assert offset == len(before)
    return output


def return_code(width, case):
    code = ['.section .text.return, "ax", @progbits', "returned:"]
    code += [f"sd x{i}, {8 * i}(gp)" for i in range(32)]
    buffers = (("output", 0x70000, 256, True), *regions(width, case))
    for _, address, size, _ in buffers:
        code += ["li a0, 1", f"li a1, {address}", f"li a2, {size}", "li a7, 64", "ecall"]
    return code + ["li a0, 0", "li a7, 93", "ecall"]


def data_code(before_path, width, case):
    code, offset = [], 256
    for name, _, size, writable in regions(width, case):
        section = ".data" if writable else ".rodata"
        flags = "aw" if writable else "a"
        code += [f'.section {section}.{name}, "{flags}", @progbits',
                 f'.incbin "{before_path}", {offset}, {size}']
        offset += size
    return code + ['.section .data.output, "aw", @progbits', ".zero 256"]


def driver(before_path, width, case):
    registers = struct.unpack("<32Q", before_path.read_bytes()[:256])
    code = [".option norvc", ".option norelax", *return_code(width, case),
            '.section .text.start, "ax", @progbits', ".global _start", "_start:"]
    code += [f"li x{i}, {registers[i]}" for i in range(1, 32)]
    code += ["jal x0, protocol_entry", *data_code(before_path, width, case)]
    return "\n".join(code) + "\n"


def assemble(prefix, source, output):
    run([prefix + "as", "-march=rv64im", "-mabi=lp64", "-o", str(output), str(source)])


def prepare(prefix, directory):
    assemble(prefix, directory / "protocol.S", directory / "protocol.o")
    source = ('.option norvc\n.section .text.protocol, "ax", @progbits\n'
              '.balign 4\n.global protocol_entry\nprotocol_entry:\n'
              f'.incbin "{directory / "encoded.bin"}"\n')
    (directory / "encoded.S").write_text(source)
    assemble(prefix, directory / "encoded.S", directory / "encoded.o")


def execute(args, directory, width, case, expected):
    source = directory / "driver.S"
    source.write_text(driver(directory / f"case-{case}.before.bin", width, case))
    assemble(args.prefix, source, directory / "driver.o")
    for kind in ("protocol", "encoded"):
        elf = directory / f"{kind}.elf"
        run([args.prefix + "ld", "--no-relax", "-T", str(ROOT / "Tests/AsmCrypto/link.ld"),
             "-o", str(elf), str(directory / f"{kind}.o"), str(directory / "driver.o")])
        binary = directory / f"{kind}.bin"
        run([args.prefix + "objcopy", "-O", "binary", "--only-section=.text.protocol",
             str(elf), str(binary)])
        assert binary.read_bytes() == (directory / "encoded.bin").read_bytes(), "GNU bytes differ"
        actual = run([args.qemu, str(elf)], binary=True)
        (directory / f"case-{case}.{kind}.native.bin").write_bytes(actual)
        assert actual == expected, f"QEMU {kind} snapshot differs for case {case}"
