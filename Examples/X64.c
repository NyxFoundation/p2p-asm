#include "p2p_asm.h"

int main(void)
{
    const uint8_t input[] = {0x40, 0x25};
    struct p2p_asm_registers registers = {0};
    registers.x[10] = (uintptr_t)input;
    registers.x[11] = sizeof(input);
    if (protocol_entry(&registers) != P2P_ASM_RETURNED)
        return 1;
    return registers.x[10] != 0 || registers.x[11] != 37 || registers.x[12] != 2;
}
