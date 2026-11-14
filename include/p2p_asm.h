#ifndef P2P_ASM_H
#define P2P_ASM_H

#include <stdint.h>

struct p2p_asm_registers {
    uint64_t x[32];
};

enum p2p_asm_execution {
    P2P_ASM_RETURNED = 0,
    P2P_ASM_BAD_PC = 1
};

#ifdef __cplusplus
extern "C" {
#endif

/* Linux x86-64: x10..x17 carry a0..a7, x2 is the caller-owned stack,
 * and x1 is an out-of-image return sentinel (normally zero).
 * The context must not overlap any buffer accessible by the routine.
 * The execution status is separate from the routine's status in x10. */
uint64_t protocol_entry(struct p2p_asm_registers *registers);

#ifdef __cplusplus
}
#endif

#endif
