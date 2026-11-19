import M0Crypto.Release.Ed25519ScReduceCode
import M0Crypto.Release.BlockEffect

/-!
# The sites of `m0c_sc_reduce`

The effect of each block between the calls of `m0c_sc_reduce`, one decided `Eff` each: the
arguments of the two `mp_mul` calls (`a1E`, `a2E`), the starts of the three 9-word subtractions
(`s0E`, `selE`), the `cmov` and `copy` arguments (`tailE`, `finE`). The subtractions themselves
are `Ed25519ScalarChain.chain_run` in the registers `sub9_regs`, and the select mask is
`Ed25519ScalarChain.selMask_run 3`. `lits_ok`: the four pool words, with the pc their `add rd, pc`
adds, address `m0c_ed_mu` and `m0c_ed_l9` in both builds (`litsFailure` names a failing one). The
calls are not composed here.
-/

namespace M0Crypto.Release.Ed25519ScReduce

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Ed25519ScReduceCode
open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SMem)
open M0Crypto.Artifacts

abbrev cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)
def spA (n : Nat) : SExpr := .add (.reg0 13) (cw n)

/-- `ldr rd, =lit; add rd, pc` `d` bytes into a block, at `o`, over the block's memory `m` at the
load: the pool word for `litImm o p`, plus the pc of the `add`. -/
def litE (m : SMem) (d o p : Nat) : SExpr :=
  .add (.ld32 m (.add (.and (.add (.add (.reg0 15) (cw d)) (cw 4)) (.not (cw 3))) (cw (litImm o p % 256 * 4))))
    (.add (.add (.reg0 15) (cw (d + 2))) (cw 4))

/-- `out`, `in` to the frame; `mp_mul(sp + Q2, in + 28, mu, 9)`. -/
def a1E : Eff where
  regs := [(0, spA Q2), (1, .add (.reg0 1) (cw 28)),
    (2, litE (.w32 (.w32 .mem0 (spA OUT) (.reg0 0)) (spA IN) (.reg0 1)) (seqSize a1P) (a1L O) (pl O)),
    (3, cw 9)]
  mem := none
  reads := [(spA OUT, .reg0 0), (spA IN, .reg0 1)]

/-- `mp_mul(sp + Q4, sp + Q2 + 36, L, 9)`. -/
def a2E : Eff where
  regs := [(0, spA Q4), (1, spA (Q2 + 36)), (2, litE .mem0 (seqSize a2P) (a2L O) (pl O + 4)), (3, cw 9)]

/-- The start of `R = in − Q4`: `r1 = in` from the frame, `r2 = sp + Q4`, `r3 = sp + R`. -/
def s0E : Eff where
  regs := [(1, .ld32 .mem0 (spA IN)), (2, spA Q4), (3, spA R)]

/-- The start of round `T = R − L`, its `adr` at `x`, its literal at `p`. -/
def selE (x p : Nat) : Eff where
  regs := [(1, spA R), (2, litE .mem0 (seqSize selP) x p), (3, spA T)]

/-- `cmov(sp + R, sp + T, 8)` after the mask in `r3`. -/
def tailE : Eff where
  regs := [(0, spA R), (1, spA T), (2, cw 8)]

/-- `copy(out, sp + R, 8)`. -/
def finE : Eff where
  regs := [(0, .ld32 .mem0 (spA OUT)), (1, spA R), (2, cw 8)]

theorem a1_ok : effOk (a1 (a1L O) (pl O)) a1E = true := by decide +kernel
theorem a2_ok : effOk (a2 (a2L O) (pl O + 4)) a2E = true := by decide +kernel
theorem s0_ok : effOk s0H s0E = true := by decide +kernel
theorem sel1_ok : effOk (selH (selL (oD O)) (pl O + 8)) (selE (selL (oD O)) (pl O + 8)) = true := by
  decide +kernel
theorem sel2_ok : effOk (selH (selL (oD2 O)) (pl O + 12)) (selE (selL (oD2 O)) (pl O + 12)) = true := by
  decide +kernel
theorem tail_ok : effOk selT tailE = true := by decide +kernel
theorem fin_ok : effOk fin finE = true := by decide +kernel

/-- **The three subtraction sites** `sub9 1 2 3` are `Ed25519ScalarChain.chain_run true false true
1 2 3 4 5 0 9` with these registers: `[r3 …] = [r1 …] − [r2 …]` over 9 words, its borrow, its frame. -/
theorem sub9_regs : Ed25519ScalarChain.Regs true 1 2 3 4 5 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The four `adr` sites: the `ldr`'s offset, its pool word's, and the constant it addresses. -/
def sites : List (Nat × Nat × Nat) :=
  [(a1L O, pl O, Ed25519Compact.ed_mu), (a2L O, pl O + 4, Ed25519Compact.ed_l9),
   (selL (oD O), pl O + 8, Ed25519Compact.ed_l9), (selL (oD2 O), pl O + 12, Ed25519Compact.ed_l9)]

/-- The pc that a site's `add rd, pc` adds. -/
def addPc (x : Nat) : Word := BitVec.ofNat 32 (x + seqSize [Instr.ldrLit 2 0] + 4)

/-- The pool words: each plus the pc of its `add rd, pc` is the constant it addresses. -/
def litsOk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Bool :=
  sites.all fun (x, p, t) => Frame.codeWord (B := B) p + addPc x == BitVec.ofNat 32 t

/-- The first failing site: its pool offset, the address its word and pc give, the constant. -/
def litsFailure (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Option (Nat × Word × Word) :=
  (sites.find? fun (x, p, t) => Frame.codeWord (B := B) p + addPc x != BitVec.ofNat 32 t).map
    fun (x, p, t) => (p, Frame.codeWord (B := B) p + addPc x, BitVec.ofNat 32 t)

theorem litsFailure_eq_none (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] :
    litsFailure B BS = none ↔ litsOk B BS = true := by
  simp [litsFailure, litsOk, List.find?_eq_none, List.all_eq_true]

open M0Crypto.Release.Ed25519 (Build) in
theorem lits_ok (b : Build) : @litsOk b.bytes _ b.codeBytes = true := by
  cases b <;> decide +kernel

end M0Crypto.Release.Ed25519ScReduce
