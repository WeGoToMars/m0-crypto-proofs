/*
 * ChaCha20 quarter round, register-only standalone fragment.
 *
 * This is a straight-line FRAGMENT, not an AAPCS function. It has no return
 * instruction.
 * The proved region is exactly the bytes of the symbol below (st_value with the
 * Thumb bit cleared, length st_size).
 *
 * Internal convention:
 *   in:   r0 = a, r1 = b, r2 = c, r3 = d
 *   out:  r0, r1, r2, r3 = RFC 8439 QUARTERROUND(a, b, c, d)
 *   clobbers: r4 (rotation count), APSR.N/Z/C/V (ADDS writes V)
 *   preserves: r5-r14, all memory
 *   exit: falls through to the address after the fragment
 *
 * ARMv6-M has no immediate rotate, so each left rotation by n is RORS by the
 * register count 32 - n (16, 20, 24, 25).
 */
    .syntax unified
    .thumb
    .text
    .p2align 1
    .global m0c_chacha20_qr_frag
    .type m0c_chacha20_qr_frag, %function
    .thumb_func
m0c_chacha20_qr_frag:
    movs r4, #16
    adds r0, r0, r1     /* a += b          */
    eors r3, r0         /* d ^= a          */
    rors r3, r4         /* d <<<= 16       */
    adds r2, r2, r3     /* c += d          */
    eors r1, r2         /* b ^= c          */
    movs r4, #20
    rors r1, r4         /* b <<<= 12       */
    adds r0, r0, r1     /* a += b          */
    eors r3, r0         /* d ^= a          */
    movs r4, #24
    rors r3, r4         /* d <<<= 8        */
    adds r2, r2, r3     /* c += d          */
    eors r1, r2         /* b ^= c          */
    movs r4, #25
    rors r1, r4         /* b <<<= 7        */
    .size m0c_chacha20_qr_frag, . - m0c_chacha20_qr_frag
