/*
 * ChaCha20 double round (column round + diagonal round).
 * Proof fixture (not part of the library); see README.md.
 *
 * Straight-line FRAGMENT, not an AAPCS function: no return instruction. It will be
 * inlined or looped inside the block function. The proved region is exactly the
 * bytes of the symbol below.
 *
 * Internal convention:
 *   in:   x[0..15] = 16 state words at [sp, #0] .. [sp, #60]
 *         r4 = 16, r5 = 20, r6 = 24, r7 = 25 (RORS counts for <<< 16, 12, 8, 7)
 *         sp word-aligned
 *   out:  x[0..15] = RFC 8439 inner_block(x) at the same addresses
 *   clobbers: r0-r3, APSR.N/Z/C/V
 *   preserves: r4-r14, all memory outside [sp, sp+64)
 *   exit: falls through to the address after the fragment
 */
    .syntax unified
    .thumb

/* QUARTERROUND(x[a], x[b], x[c], x[d]) on stack words. */
.macro QR a, b, c, d
    ldr  r0, [sp, #4*\a]
    ldr  r1, [sp, #4*\b]
    ldr  r2, [sp, #4*\c]
    ldr  r3, [sp, #4*\d]
    adds r0, r0, r1     /* a += b          */
    eors r3, r0         /* d ^= a          */
    rors r3, r4         /* d <<<= 16       */
    adds r2, r2, r3     /* c += d          */
    eors r1, r2         /* b ^= c          */
    rors r1, r5         /* b <<<= 12       */
    adds r0, r0, r1     /* a += b          */
    eors r3, r0         /* d ^= a          */
    rors r3, r6         /* d <<<= 8        */
    adds r2, r2, r3     /* c += d          */
    eors r1, r2         /* b ^= c          */
    rors r1, r7         /* b <<<= 7        */
    str  r0, [sp, #4*\a]
    str  r1, [sp, #4*\b]
    str  r2, [sp, #4*\c]
    str  r3, [sp, #4*\d]
.endm

    .text
    .p2align 1
    .global m0c_chacha20_dround_frag
    .type m0c_chacha20_dround_frag, %function
    .thumb_func
m0c_chacha20_dround_frag:
    /* column round */
    QR 0, 4,  8, 12
    QR 1, 5,  9, 13
    QR 2, 6, 10, 14
    QR 3, 7, 11, 15
    /* diagonal round */
    QR 0, 5, 10, 15
    QR 1, 6, 11, 12
    QR 2, 7,  8, 13
    QR 3, 4,  9, 14
    .size m0c_chacha20_dround_frag, . - m0c_chacha20_dround_frag
