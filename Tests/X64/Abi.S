.intel_syntax noprefix
.text
.globl checked_call
.type checked_call, @function
checked_call:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    sub rsp, 24
    mov rax, rsi
    mov ebx, 0x11223344
    mov ebp, 0x22334455
    mov r12d, 0x33445566
    mov r13d, 0x44556677
    mov r14d, 0x55667788
    mov r15d, 0x66778899
    call rax
    cmp rbx, 0x11223344
    jne bad_abi
    cmp rbp, 0x22334455
    jne bad_abi
    cmp r12, 0x33445566
    jne bad_abi
    cmp r13, 0x44556677
    jne bad_abi
    cmp r14, 0x55667788
    jne bad_abi
    cmp r15, 0x66778899
    jne bad_abi
    jmp done
bad_abi:
    mov eax, 2
done:
    add rsp, 24
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
.size checked_call, . - checked_call
.section .note.GNU-stack,"",@progbits
