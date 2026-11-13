import M0Crypto.Release.X25519Diff

set_option linter.unusedSimpArgs false

/-!
The 64-bit absolute difference of `mul128` and `sqr128` (plan `x25519-proofs.md`, phase 8):
`subs x0, y0; sbcs x1, y1; sbcs m, m; eors x0, m; eors x1, m; subs x0, m; sbcs x1, m`. The
pair `x1:x0` becomes `|X - Y|` and `m` the mask of `X < Y`. `m` may be `y0` or `y1`: it is
written only after both are read.
-/

namespace M0Crypto.Release.X25519Absd
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Carry (sbc_pair carry_le)
open M0Crypto.Release.X25519Mul (regs_subs regs_sbcs c_sbcs c_subs ne_lo)
open M0Crypto.Release.Blake2s (toReg_ne15 regs_eors)

theorem not2 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    2 ^ 32 - 1 - a + 2 ^ 32 * (2 ^ 32 - 1 - b) = 2 ^ 64 - 1 - (a + 2 ^ 32 * b) := by omega

/-- Macro text of the generator, inlined in `mul128`/`sqr128`. -/
def absd64 (x0 x1 y0 y1 m : LowReg) : List Instr :=
  [.subReg x0 x0 y0, .dp .sbcs x1 y1, .dp .sbcs m m, .dp .eors x0 m, .dp .eors x1 m,
   .subReg x0 x0 m, .dp .sbcs x1 m]

theorem absd64_exec (s : State) (x0 x1 y0 y1 m : LowReg) (h01 : x0.val ≠ x1.val)
    (h0m : x0.val ≠ m.val) (h1m : x1.val ≠ m.val) (h0y : x0.val ≠ y1.val) :
    let t := execAll (absd64 x0 x1 y0 y1 m) s
    let X : Nat := (s.reg x0).toNat + 2 ^ 32 * (s.reg x1).toNat
    let Y : Nat := (s.reg y0).toNat + 2 ^ 32 * (s.reg y1).toNat
    let R : Nat := (t.reg x0).toNat + 2 ^ 32 * (t.reg x1).toNat
    t.reg m = mask (decide (X < Y)) ∧
      (X : Int) - Y = (if X < Y then -(R : Int) else R) ∧
      t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ x0.toReg → r ≠ x1.toReg → r ≠ m.toReg → t.regs r = s.regs r := by
  intro t X Y R
  have hm : t.mem = s.mem := execAll_mem _ _ (by simp [absd64, Instr.writesMem])
  have ho : ∀ r : Reg, r ≠ 15 → r ≠ x0.toReg → r ≠ x1.toReg → r ≠ m.toReg → t.regs r = s.regs r := by
    intro r h15 a0 a1 am
    simp only [t, absd64, execAll, regs_subs, regs_sbcs, regs_eors, h15, a0, a1, am, ne_eq,
      not_false_eq_true, ite_false]
  refine ⟨?_, ?_, hm, ho⟩ <;>
  simp only [R, t, absd64, execAll, State.reg] <;>
  simp only [regs_subs, regs_sbcs, regs_eors, c_subs, c_sbcs, toReg_ne15, ne_eq,
    not_false_eq_true, State.reg, ne_lo _ _ h01, ne_lo _ _ (Ne.symm h01), ne_lo _ _ h0m,
    ne_lo _ _ (Ne.symm h0m), ne_lo _ _ h1m, ne_lo _ _ (Ne.symm h1m), ne_lo _ _ h0y,
    ne_lo _ _ (Ne.symm h0y), ite_true, ite_false, sbcs_self] <;>
  have p1 := sbc_pair (s.regs x0.toReg) (s.regs x1.toReg) (s.regs y0.toReg) (s.regs y1.toReg) <;>
  generalize hA0 : addWithCarry (s.regs x0.toReg) (~~~s.regs y0.toReg) true = A0 at p1 ⊢ <;>
  generalize hA1 : addWithCarry (s.regs x1.toReg) (~~~s.regs y1.toReg) A0.2.1 = A1 at p1 ⊢
  · have := A1.1.isLt; have := A0.1.isLt
    have hX : X < Y ↔ A1.2.1 = false := by
      simp only [X, Y, State.reg]
      cases hc : A1.2.1 <;> simp only [hc, Bool.toNat_false, Bool.toNat_true] at p1 <;> simp <;>
        omega
    cases hc : A1.2.1 <;> simp only [hc] at hX <;> simp [hX]
  · generalize hn : (!A1.2.1) = neg
    have hb : 1 - A1.2.1.toNat = if neg then 1 else 0 := by rw [← hn]; cases A1.2.1 <;> rfl
    rw [hb] at p1
    have p2 := sbc_pair (A0.1 ^^^ mask neg) (A1.1 ^^^ mask neg) (mask neg) (mask neg)
    generalize hR0 : addWithCarry (A0.1 ^^^ mask neg) (~~~mask neg) true = R0 at p2 ⊢
    generalize hR1 : addWithCarry (A1.1 ^^^ mask neg) (~~~mask neg) R0.2.1 = R1 at p2 ⊢
    have q0 := xor_mask A0.1 neg; have q1 := xor_mask A1.1 neg
    have mk := mask_toNat neg
    have := A0.1.isLt; have := A1.1.isLt; have := R0.1.isLt; have := R1.1.isLt
    have := (s.regs x0.toReg).isLt; have := (s.regs x1.toReg).isLt
    have := (s.regs y0.toReg).isLt; have := (s.regs y1.toReg).isLt
    have hc : R1.2.1.toNat ≤ 1 := Bool.toNat_le _
    have hX : X < Y ↔ neg = true := by
      simp only [X, Y, State.reg]; cases neg <;> simp at p1 ⊢ <;> omega
    have hb1 : ((if neg then 1 else 0) = 1) = (neg = true) := by cases neg <;> simp
    have key := M0Crypto.Release.X25519Kara.absdiff (2 ^ 64) X Y
      (A0.1.toNat + 2 ^ 32 * A1.1.toNat) (if neg then 1 else 0)
      ((A0.1 ^^^ mask neg).toNat + 2 ^ 32 * (A1.1 ^^^ mask neg).toNat)
      (R0.1.toNat + 2 ^ 32 * R1.1.toNat) (1 - R1.2.1.toNat)
      (by simp only [Y, State.reg]; omega) (by omega) (by omega) (by split <;> omega) (by omega)
      (by simp only [X, Y, State.reg]; omega)
      (by simp only [hb1]; rw [q0, q1]; cases neg <;> simp only [Bool.false_eq_true,
        ↓reduceIte]; exact not2 A0.1.isLt A1.1.isLt)
      (by rw [mk] at p2; cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at p2 ⊢ <;>
        omega)
    rw [key]; simp only [hb1]
    by_cases h : X < Y
    · simp only [hX.mp h, h, ite_true]
    · have hn' : neg = false := by cases neg <;> simp_all
      simp only [hn', h, Bool.false_eq_true, ite_false]

end M0Crypto.Release.X25519Absd
