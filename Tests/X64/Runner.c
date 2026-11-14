#define _GNU_SOURCE
#include "p2p_asm.h"
#include <dlfcn.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

struct region {
    void *base;
    size_t size;
};

static void fail(const char *message)
{
    fputs(message, stderr);
    fputc('\n', stderr);
    exit(10);
}

static struct region load_region(FILE *input, const char *description)
{
    uint64_t address;
    size_t size;
    unsigned writable;
    char tail;
    const long page = sysconf(_SC_PAGESIZE);
    if (sscanf(description, "%" SCNx64 ":%zu:%u%c",
               &address, &size, &writable, &tail) != 3 ||
        page <= 0 || address < 0x10000 || address % (uint64_t)page != 0 ||
        size == 0 || size > 0x1000000 || writable > 1)
        fail("Invalid test region");
    void *base = mmap((void *)(uintptr_t)address, size, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (base == MAP_FAILED)
        fail("Could not map test region without replacing an existing mapping");
    if (fread(base, 1, size, input) != size)
        fail("Truncated test snapshot");
    if (!writable && mprotect(base, size, PROT_READ) != 0)
        fail("Could not protect test region");
    return (struct region){base, size};
}

int main(int argc, char **argv)
{
    if (argc < 4 || argc > 11)
        fail("Usage: runner LIBRARY SNAPSHOT ADDRESS_HEX:SIZE:WRITABLE ...");
    void *library = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (library == NULL)
        fail("Could not load generated library");
    typedef uint64_t (*entry_fn)(struct p2p_asm_registers *);
    typedef uint64_t (*checked_fn)(struct p2p_asm_registers *, entry_fn);
    const entry_fn entry = (entry_fn)dlsym(library, "protocol_entry");
    const checked_fn checked = (checked_fn)dlsym(library, "checked_call");
    if (entry == NULL || checked == NULL)
        fail("Missing generated entry or ABI checker");
    FILE *input = fopen(argv[2], "rb");
    struct p2p_asm_registers registers;
    if (input == NULL || fread(&registers, 1, sizeof(registers), input) != sizeof(registers))
        fail("Could not read test registers");
    struct region regions[8];
    for (int i = 3; i < argc; ++i)
        regions[i - 3] = load_region(input, argv[i]);
    if (fgetc(input) != EOF || ferror(input))
        fail("Unexpected snapshot length");
    fclose(input);
    if (checked(&registers, entry) != P2P_ASM_RETURNED)
        fail("Generated execution or System V ABI check failed");
    if (fwrite(&registers, 1, sizeof(registers), stdout) != sizeof(registers))
        fail("Could not write register snapshot");
    for (int i = 3; i < argc; ++i)
        if (fwrite(regions[i - 3].base, 1, regions[i - 3].size, stdout) != regions[i - 3].size)
            fail("Could not write memory snapshot");
    return fflush(stdout) == 0 ? 0 : 10;
}
