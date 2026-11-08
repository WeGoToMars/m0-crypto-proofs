/*
 * ChaCha20 double round, version 2 (schedule-change replay of version 1).
 * Proof fixture (not part of the library); see README.md.
 *
 * Identical to version 1 except that x[15] stays in r3 across the column ->
 * diagonal boundary: quarter round 4 (3,7,11,15) doesn't store it and quarter
 * round 5 (0,5,10,15) doesn't reload it. 158 instructions.
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

#include "chacha20_round.inc"

    .text
    .p2align 1
    .global m0c_chacha20_dround_v2_frag
    .type m0c_chacha20_dround_v2_frag, %function
    .thumb_func
m0c_chacha20_dround_v2_frag:
    DOUBLE_ROUND
    .size m0c_chacha20_dround_v2_frag, . - m0c_chacha20_dround_v2_frag
