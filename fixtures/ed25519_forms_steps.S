/*
 * QEMU single-step fixture for the forms the Ed25519 unit adds to the model (tools/check.sh
 * step 7b). Not library code. ed25519_forms_fixture runs:
 * - LSLS and LSRS by register with amounts 0 (carry in 0 and 1), 1, 31, 32, 33, 255, and
 *   0x121 and 0x100 (only the bottom byte counts), carry out 0 and 1, Rdn != Rm and Rdn = Rm;
 * - ASRS (immediate) by 1, 24, 31 and 32 on negative and positive values, Rd = Rm and Rd != Rm;
 * - REV with Rd = Rm and Rd != Rm;
 * - ADD Rdn, PC with Rdn = r0, r1, r2, r7, at addresses 0 and 2 mod 4, with a wrapping sum.
 * Flags are set before REV and ADD Rdn, PC, which must leave them unchanged.
 * Every form also runs once more with V = 1 (from a signed overflow), with C = 0 and C = 1 for
 * the shifts by zero: no form writes V (DDI 0419E A6.7.3, A6.7.8, A6.7.36, A6.7.38, A6.7.51).
 */
    .macro setv_c0       /* V = 1, N = 1, Z = 0, C = 0; clobbers r6 */
    ldr  r6, =0x7fffffff
    adds r6, #1
    .endm
    .macro setv_c1       /* V = 1, N = 0, Z = 1, C = 1; clobbers r6 */
    ldr  r6, =0x80000000
    adds r6, r6, r6
    .endm
    .syntax unified
    .cpu cortex-m0plus
    .thumb
    .section .text.ed25519_forms_fixture, "ax", %progbits
    .p2align 2
    .global ed25519_forms_fixture
    .type ed25519_forms_fixture, %function
    .thumb_func
ed25519_forms_fixture:
    push {r4-r7, lr}

    /* LSLS Rdn, Rm */
    ldr  r0, =0x80000001
    movs r1, #0
    cmp  r1, r1          /* C = 1 */
    lsls r0, r1          /* 0: value and C = 1 kept */
    adds r2, r1, #0      /* C = 0 */
    lsls r0, r1          /* 0: C = 0 kept */
    movs r1, #1
    lsls r0, r1          /* 1: 0x00000002, C = 1 */
    lsls r0, r1          /* 1: 0x00000004, C = 0 */
    ldr  r0, =0x00000003
    movs r1, #31
    lsls r0, r1          /* 31: 0x80000000, N = 1, C = 1 */
    ldr  r0, =0x80000001
    movs r1, #32
    lsls r0, r1          /* 32: 0, Z = 1, C = bit 0 = 1 */
    ldr  r0, =0xfffffffe
    lsls r0, r1          /* 32: 0, C = 0 */
    ldr  r0, =0xffffffff
    movs r1, #33
    lsls r0, r1          /* 33: 0, C = 0 */
    ldr  r0, =0xffffffff
    movs r1, #255
    lsls r0, r1          /* 255: 0, C = 0 */
    ldr  r0, =0x12345678
    ldr  r1, =0x121
    lsls r0, r1          /* bottom byte 33: 0, C = 0 */
    ldr  r0, =0x12345678
    ldr  r1, =0x100
    cmp  r1, r1          /* C = 1 */
    lsls r0, r1          /* bottom byte 0: value and C = 1 kept */
    movs r2, #4
    lsls r2, r2          /* Rdn = Rm: 4 << 4 = 0x40 */
    movs r3, #33
    lsls r3, r3          /* Rdn = Rm: 0, C = 0 */

    /* LSRS Rdn, Rm */
    ldr  r4, =0x80000001
    movs r5, #0
    cmp  r5, r5          /* C = 1 */
    lsrs r4, r5          /* 0: value and C = 1 kept */
    adds r6, r5, #0      /* C = 0 */
    lsrs r4, r5          /* 0: C = 0 kept */
    movs r5, #1
    lsrs r4, r5          /* 1: 0x40000000, C = 1 */
    lsrs r4, r5          /* 1: 0x20000000, C = 0 */
    ldr  r4, =0xc0000000
    movs r5, #31
    lsrs r4, r5          /* 31: 1, C = bit 30 = 1 */
    ldr  r4, =0x80000000
    movs r5, #32
    lsrs r4, r5          /* 32: 0, Z = 1, C = bit 31 = 1 */
    ldr  r4, =0x7fffffff
    lsrs r4, r5          /* 32: 0, C = 0 */
    ldr  r4, =0xffffffff
    movs r5, #33
    lsrs r4, r5          /* 33: 0, C = 0 */
    ldr  r4, =0xffffffff
    movs r5, #255
    lsrs r4, r5          /* 255: 0, C = 0 */
    ldr  r4, =0x87654321
    ldr  r5, =0x121
    lsrs r4, r5          /* bottom byte 33: 0, C = 0 */
    ldr  r4, =0x87654321
    ldr  r5, =0x100
    cmp  r5, r5          /* C = 1 */
    lsrs r4, r5          /* bottom byte 0: value and C = 1 kept */
    movs r6, #2
    lsrs r6, r6          /* Rdn = Rm: 2 >> 2 = 0, C = bit 1 = 1 */
    ldr  r7, =0x80000020
    lsrs r7, r7          /* Rdn = Rm: amount 0x20 = 32: 0, C = 1 */

    /* ASRS Rd, Rm, #imm */
    ldr  r1, =0x81000000
    asrs r1, r1, #24     /* 0xffffff81, N = 1, C = bit 23 = 0 */
    ldr  r1, =0x7f800000
    asrs r1, r1, #24     /* 0x0000007f, C = bit 23 = 1 */
    ldr  r3, =0x80000001
    asrs r2, r3, #1      /* 0xc0000000, C = 1 */
    ldr  r5, =0x40000000
    asrs r4, r5, #31     /* 0, Z = 1, C = bit 30 = 1 */
    ldr  r7, =0x80000000
    asrs r6, r7, #32     /* 0xffffffff, C = 1 */
    ldr  r7, =0x7fffffff
    asrs r6, r7, #32     /* 0, Z = 1, C = 0 */

    /* REV Rd, Rm */
    ldr  r1, =0x11223344
    movs r0, #0
    subs r0, #1          /* N = 1, C = 0 */
    rev  r1, r1          /* 0x44332211 */
    ldr  r5, =0x80ff0001
    cmp  r5, r5          /* Z = 1, C = 1 */
    rev  r4, r5          /* 0x0100ff80 */

    /* ADD Rdn, PC at both halfword alignments */
    ldr  r0, =0x100
    ldr  r1, =0x200
    ldr  r2, =0xffffffff
    ldr  r7, =0x10
    movs r3, #0
    subs r3, #1          /* N = 1, C = 0 */
    add  r0, pc
    add  r1, pc
    add  r2, pc          /* wraps */
    add  r7, pc
    cmp  r3, r3          /* Z = 1, C = 1 */
    add  r0, pc
    add  r1, pc
    add  r2, pc
    add  r7, pc
    adds r3, #0
    add  r7, pc

    /* The same forms with V = 1 on entry */
    ldr  r0, =0x12345678
    movs r1, #4
    setv_c0
    lsls r0, r1          /* 4: 0x23456780, C = 1, V = 1 kept */
    movs r1, #0
    setv_c1
    lsls r0, r1          /* 0: value, C = 1 and V = 1 kept */
    movs r1, #32
    setv_c0
    lsls r0, r1          /* 32: 0, C = bit 0 = 0, V = 1 kept */
    ldr  r2, =0x87654321
    movs r3, #4
    setv_c0
    lsrs r2, r3          /* 4: 0x08765432, C = 0, V = 1 kept */
    movs r3, #0
    setv_c1
    lsrs r2, r3          /* 0: value, C = 1 and V = 1 kept */
    ldr  r2, =0x80000000
    movs r3, #32
    setv_c0
    lsrs r2, r3          /* 32: 0, C = 1, V = 1 kept */
    ldr  r5, =0x81000000
    setv_c0
    asrs r4, r5, #24     /* 0xffffff81, C = 0, V = 1 kept */
    setv_c1
    asrs r4, r5, #32     /* 0xffffffff, C = 1, V = 1 kept */
    ldr  r5, =0x11223344
    setv_c0
    rev  r4, r5          /* 0x44332211, flags kept */
    ldr  r0, =0x100
    ldr  r7, =0x10
    setv_c1
    add  r0, pc          /* flags kept */
    add  r7, pc          /* the other halfword alignment, flags kept */

    pop  {r4-r7, pc}
    .ltorg
    .size ed25519_forms_fixture, .-ed25519_forms_fixture

    .text
    .global main
    .type main, %function
    .thumb_func
main:                    /* 987 calls: qemu_steps.py stops tracing at its last sampled call */
    push {r4, lr}
    ldr  r4, =987
1:  bl   ed25519_forms_fixture
    subs r4, #1
    bne  1b
    movs r0, #0
    pop  {r4, pc}
    .ltorg
