import M0Crypto.Release.Blake2sLocals

/-!
# Frame sizes and slots of the BLAKE2s entries

Macros that expand, at elaboration time, to numerals computed from `localsBytes`
(`Blake2sLocals.lean`). The elaborated terms are plain numbers, so `omega`, `bv_omega` and
`decide` see literals, while the proofs name what the number means.

* `COMPRESS_FRAME`: bytes the compression pushes below its entry `sp` (`LOCALS` + saved).
* `LOCALS_WORDS`, `LOCALS_BYTES`: the `sub sp`/`add sp` immediate, in words and in bytes.
* `HPTR_SLOT`: byte offset of the saved `H_PTR` word.
* `SAVED_k` (bytes) and `SLOTW_k` (words): the k-th word above the locals, k = 0..8 for r8-r11,
  r4-r7, lr, and k = 9 for the `f0` argument.
* `STREAM_FRAME`, `STREAM_LOCALS`: the `update`/`final` stack bound and locals.
-/

open Lean in
/-- Numeral syntax for a computed natural number. -/
private def numStx (n : Nat) : TSyntax `term := Syntax.mkNumLit (toString n)

macro "COMPRESS_FRAME" : term => return numStx (localsBytes + savedBytes)
macro "COMPRESS_FRAME_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + savedBytes)))
macro "LOCALS_WORDS" : term => return numStx (localsBytes / 4)
macro "LOCALS_BYTES" : term => return numStx localsBytes
macro "LOCALS_W" : term => do `(BitVec.ofNat 32 $(numStx localsBytes))
/-- Words in the frame including the `f0` argument slot. -/
macro "FRAME_SLOTS" : term => return numStx (localsBytes / 4 + 10)
macro "HPTR_SLOT" : term => return numStx hptrBytes
macro "HPTR_WORDS" : term => return numStx (hptrBytes / 4)
macro "HPTR_SLOT_W" : term => do `(BitVec.ofNat 32 $(numStx hptrBytes))
macro "SAVED_0" : term => return numStx (localsBytes + 0)
macro "SAVED_0_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 0)))
macro "SAVED_1" : term => return numStx (localsBytes + 4)
macro "SAVED_1_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 4)))
macro "SAVED_2" : term => return numStx (localsBytes + 8)
macro "SAVED_2_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 8)))
macro "SAVED_3" : term => return numStx (localsBytes + 12)
macro "SAVED_3_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 12)))
macro "SAVED_4" : term => return numStx (localsBytes + 16)
macro "SAVED_4_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 16)))
macro "SAVED_5" : term => return numStx (localsBytes + 20)
macro "SAVED_5_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 20)))
macro "SAVED_6" : term => return numStx (localsBytes + 24)
macro "SAVED_6_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 24)))
macro "SAVED_7" : term => return numStx (localsBytes + 28)
macro "SAVED_7_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 28)))
macro "SAVED_8" : term => return numStx (localsBytes + 32)
macro "SAVED_8_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 32)))
macro "SLOTW_0" : term => return numStx (localsBytes / 4 + 0)
macro "SLOTW_1" : term => return numStx (localsBytes / 4 + 1)
macro "SLOTW_2" : term => return numStx (localsBytes / 4 + 2)
macro "SLOTW_3" : term => return numStx (localsBytes / 4 + 3)
macro "SLOTW_4" : term => return numStx (localsBytes / 4 + 4)
macro "SLOTW_5" : term => return numStx (localsBytes / 4 + 5)
macro "SLOTW_6" : term => return numStx (localsBytes / 4 + 6)
macro "SLOTW_7" : term => return numStx (localsBytes / 4 + 7)
macro "SLOTW_8" : term => return numStx (localsBytes / 4 + 8)
macro "SLOTW_9" : term => return numStx (localsBytes / 4 + 9)

/-- `update`/`final` stack bound: 20 bytes of saved registers, `localsBytes` + 40 of locals (holding
the compression's frame). -/
macro "STREAM_FRAME" : term => return numStx (localsBytes + 60)
macro "STREAM_FRAME_W" : term => do `(BitVec.ofNat 32 $(numStx (localsBytes + 60)))
macro "STREAM_LOCALS" : term => return numStx (localsBytes + 40)
