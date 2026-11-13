/*
 * QEMU single-step fixture for SBCS (tools/check.sh step 7b). Not library code.
 * sbcs_fixture runs SBCS with carry in 0 and 1, carry out 0 and 1, signed overflow,
 * a zero result and Rdn = Rm, so the model's flags are compared with QEMU's on each.
 */
    .syntax unified
    .cpu cortex-m0plus
    .thumb
    .section .text.sbcs_fixture, "ax", %progbits
    .p2align 2
    .global sbcs_fixture
    .type sbcs_fixture, %function
    .thumb_func
sbcs_fixture:
    push {r4-r7, lr}
    movs r0, #5
    movs r1, #7
    cmp  r0, r0          /* C = 1 */
    sbcs r0, r1          /* 5 - 7 = -2, borrow: C = 0, N = 1 */
    sbcs r1, r1          /* C = 0: 7 - 7 - 1 = -1, C = 0 */
    movs r2, #9
    movs r3, #3
    sbcs r2, r3          /* C = 0: 9 - 3 - 1 = 5, C = 1 */
    sbcs r3, r3          /* C = 1: 0, Z = 1, C = 1 */
    movs r4, #1
    lsls r4, r4, #31     /* 0x80000000 */
    movs r5, #1
    cmp  r5, r5          /* C = 1 */
    sbcs r4, r5          /* 0x80000000 - 1: V = 1, C = 1 */
    movs r6, #0
    movs r7, #1
    sbcs r6, r7          /* C = 1: 0 - 1 = -1, C = 0 */
    sbcs r7, r6          /* C = 0: 1 - (-1) - 1 = 1, C = 0 */
    sbcs r5, r5          /* C = 0: -1 */
    pop  {r4-r7, pc}
    .size sbcs_fixture, .-sbcs_fixture

    .text
    .global main
    .type main, %function
    .thumb_func
main:                    /* 987 calls: qemu_steps.py stops tracing at its last sampled call */
    push {r4, lr}
    ldr  r4, =987
1:  bl   sbcs_fixture
    subs r4, #1
    bne  1b
    movs r0, #0
    pop  {r4, pc}
    .ltorg
