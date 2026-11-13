import M0Crypto.Release.X25519CRBase

set_option linter.unusedSimpArgs false

/-!
Phases A, B and C of `combineReduce` (`X25519Macros.reducePhaseA/B`, `reducePhaseC`): the
Karatsuba middle term `Y = L + H + P'` with `P' = P` (mask `n = 0`) or `P' = -P` (mask all
ones; `sq` always), as a 9-word value `Y0..Y3` (parked in `r8, r10, r11, r12`), `Y4..Y7`
(`r0`-`r3`) and `Y8` (`r6`). Phase C adds `H0..H3` to `Y4..Y7`, stores the sum over `H0..H3`
and parks the top word in `r9`.

`P` is the middle product as `mul128 SPP true`/`sqr128 SPP true` leave it: `P0, P1` in slots
`SPP, SPP + 1`, `P2, P3` in `r0, r1`, `P4..P7` in slots `SPP + 4 ..`. `NOk sq s neg` says
which sign: for `sq` the mask is all ones, otherwise it is the word in slot `SN`.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Macros (sl SH SP_ SPP SN reducePhaseA reducePhaseB reducePhaseC xorN)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds c_adcs c_adds c_movImm c_movHi c_lsr1 regs_lsr)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.Blake2s (toReg_ne15 regs_eors regs_movImm regs_movHi)

/-- The sign of the middle term: all ones for a square, the mask in slot `SN` otherwise. -/
def NOk (sq : Bool) (s : State) (neg : Bool) : Prop :=
  if sq then neg = true else fr s.mem s.sp SN = mask neg

theorem not_xor (x : Word) : ~~~x = x ^^^ mask true := by
  simp only [mask, ite_true]; rw [BitVec.xor_allOnes]

theorem lsb_mask (neg : Bool) : (mask neg).getLsbD 0 = neg := by cases neg <;> rfl

theorem SPP_mod : SPP % 256 = SPP := by decide
theorem SH_mod : SH % 256 = SH := by decide
theorem SP_mod : SP_ % 256 = SP_ := by decide
theorem SN_mod : SN % 256 = SN := by decide

/-- The word identity of phase A: two four-word chains (`P' + L + c`, then `+ H`) and the
carry count. -/
theorem phaseA_close (p0 p1 p2 p3 l0 l1 l2 l3 h0 h1 h2 h3 : Word) (c : Bool) (z : Word)
    (hz : z.toNat = 0) :
    w4 (addWithCarry (addWithCarry p0 l0 c).1 h0 false).1
        (addWithCarry (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).1 h1
          (addWithCarry (addWithCarry p0 l0 c).1 h0 false).2.1).1
        (addWithCarry (addWithCarry p2 l2 (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).2.1).1 h2
          (addWithCarry (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).1 h1
            (addWithCarry (addWithCarry p0 l0 c).1 h0 false).2.1).2.1).1
        (addWithCarry (addWithCarry p3 l3 (addWithCarry p2 l2 (addWithCarry p1 l1
            (addWithCarry p0 l0 c).2.1).2.1).2.1).1 h3
          (addWithCarry (addWithCarry p2 l2 (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).2.1).1 h2
            (addWithCarry (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).1 h1
              (addWithCarry (addWithCarry p0 l0 c).1 h0 false).2.1).2.1).2.1).1 +
      2 ^ 128 * (addWithCarry (addWithCarry (z)
          (z) (addWithCarry p3 l3 (addWithCarry p2 l2
            (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).2.1).2.1).2.1).1
        (z)
        (addWithCarry (addWithCarry p3 l3 (addWithCarry p2 l2 (addWithCarry p1 l1
            (addWithCarry p0 l0 c).2.1).2.1).2.1).1 h3
          (addWithCarry (addWithCarry p2 l2 (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).2.1).1 h2
            (addWithCarry (addWithCarry p1 l1 (addWithCarry p0 l0 c).2.1).1 h1
              (addWithCarry (addWithCarry p0 l0 c).1 h0 false).2.1).2.1).2.1).2.1).1.toNat =
      w4 p0 p1 p2 p3 + (w4 l0 l1 l2 l3 + (w4 h0 h1 h2 h3 + c.toNat)) := by
  generalize ga0 : addWithCarry p0 l0 c = A0
  generalize ga1 : addWithCarry p1 l1 A0.2.1 = A1
  generalize ga2 : addWithCarry p2 l2 A1.2.1 = A2
  generalize ga3 : addWithCarry p3 l3 A2.2.1 = A3
  generalize gb0 : addWithCarry A0.1 h0 false = B0
  generalize gb1 : addWithCarry A1.1 h1 B0.2.1 = B1
  generalize gb2 : addWithCarry A2.1 h2 B1.2.1 = B2
  generalize gb3 : addWithCarry A3.1 h3 B2.2.1 = B3
  generalize gc0 : addWithCarry z z A3.2.1 = C0
  generalize gc1 : addWithCarry C0.1 z B3.2.1 = C1
  have e0 := adc_nat p0 l0 c; have e1 := adc_nat p1 l1 A0.2.1; have e2 := adc_nat p2 l2 A1.2.1
  have e3 := adc_nat p3 l3 A2.2.1; have f0 := adc_nat A0.1 h0 false
  have f1 := adc_nat A1.1 h1 B0.2.1; have f2 := adc_nat A2.1 h2 B1.2.1
  have f3 := adc_nat A3.1 h3 B2.2.1; have g0 := adc_nat z z A3.2.1; have g1 := adc_nat C0.1 z B3.2.1
  rw [ga0] at e0; rw [ga1] at e1; rw [ga2] at e2; rw [ga3] at e3; rw [gb0] at f0; rw [gb1] at f1
  rw [gb2] at f2; rw [gb3] at f3; rw [gc0] at g0; rw [gc1] at g1
  have := carry_le p3 l3 A2.2.1; have := carry_le A3.1 h3 B2.2.1
  rw [ga3] at *; rw [gb3] at *
  have := C1.2.1.toNat.le_refl
  have := C0.1.isLt; have := C1.1.isLt
  simp only [w4, Bool.toNat_false] at *
  omega

theorem phaseA_exec (s : State) (sq neg : Bool) (hN : NOk sq s neg) :
    let t := execAll (reducePhaseA sq) s
    let F := fr s.mem s.sp
    w4 (t.regs 8) (t.regs 10) (t.regs 11) (t.regs 12) + 2 ^ 128 * (t.regs 4).toNat =
        w4 (F SPP ^^^ mask neg) (F (SPP + 1) ^^^ mask neg) (s.regs 0 ^^^ mask neg)
          (s.regs 1 ^^^ mask neg) + w4 (F SP_) (F (SP_ + 1)) (F (SP_ + 2)) (F (SP_ + 3)) +
          w4 (F SH) (F (SH + 1)) (F (SH + 2)) (F (SH + 3)) + neg.toNat ∧
      t.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → (r = 9 ∨ 13 ≤ r.val) → t.regs r = s.regs r := by
  intro t F
  have hm : t.mem = s.mem := execAll_mem _ _ (by cases sq <;> simp [reducePhaseA, xorN, Instr.writesMem])
  refine ⟨?_, hm, ?_⟩
  · simp only [F, State.sp]
    cases sq
    · simp only [NOk, Bool.false_eq_true, ite_false, State.sp] at hN
      simp only [t, reducePhaseA, xorN, execAll, List.cons_append, List.nil_append,
        Bool.false_eq_true, ite_false]
      simp (config := {decide := true}) only [regs_adcs, regs_adds, c_adcs, c_adds, regs_ldm,
        regs_addRdSp, regs_movImm, regs_movHi, regs_eors, regs_lsr, regs_ldrSp, c_ldm, c_addRdSp,
        c_movImm, c_movHi, c_eors, c_lsr1, c_ldrSp, mem_ldm, mem_addRdSp, mem_ldrSp, mem_dp,
        mem_addReg, mem_movImm, mem_movHi, mem_lsr, State.reg,
        toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, listRegs_60, bitCount_60,
        listRegs_03, bitCount_03, List.map, List.idxOf, List.findIdx_cons, List.findIdx_nil,
        beq_self_eq_true, Bool.cond_true, Bool.cond_false, addr2, ite_true, ite_false, ne_eq,
        List.mem_cons, sl_toNat, State.sp]
      simp (disch := omega) only [rd_norm, Nat.add_assoc, div4, div4', Nat.add_zero, Nat.mul_zero,
        Nat.zero_div, Nat.zero_add, Nat.mul_one, Nat.mul_div_cancel_left _ (by decide : 0 < 4),
        Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, SPP_mod, SH_mod, SP_mod, SN_mod]
      rw [hN, lsb_mask]
      exact phaseA_close _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)
    · simp only [NOk, ite_true] at hN
      subst hN
      simp only [t, reducePhaseA, xorN, execAll, List.cons_append, List.nil_append, ite_true]
      simp (config := {decide := true}) only [regs_adcs, regs_adds, c_adcs, c_adds, regs_ldm,
        regs_addRdSp, regs_movImm, regs_movHi, regs_mvns, regs_cmp, c_cmp_self, c_ldm, c_addRdSp,
        c_movImm, c_movHi, c_mvns, mem_ldm, mem_addRdSp, mem_dp,
        mem_addReg, mem_movImm, mem_movHi, State.reg,
        toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, listRegs_60, bitCount_60,
        listRegs_03, bitCount_03, List.map, List.idxOf, List.findIdx_cons, List.findIdx_nil,
        beq_self_eq_true, Bool.cond_true, Bool.cond_false, addr2, ite_true, ite_false, ne_eq,
        List.mem_cons, sl_toNat, State.sp]
      simp (disch := omega) only [rd_norm, Nat.add_assoc, div4, div4', Nat.add_zero, Nat.mul_zero,
        Nat.zero_div, Nat.zero_add, Nat.mul_one, Nat.mul_div_cancel_left _ (by decide : 0 < 4),
        Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, SPP_mod, SH_mod, SP_mod, SN_mod, not_xor]
      exact phaseA_close _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)
  · intro r h15 hr
    have h15' : r.val ≠ 15 := fun e => h15 (Fin.ext e)
    have hr' : r.val = 9 ∨ 13 ≤ r.val := hr.imp (fun h => by rw [h]; rfl) id
    cases sq <;>
    exact execAll_regs_other _ _ _ h15' (by
      simp only [reducePhaseA, xorN, Instr.dsts, listRegs_60, listRegs_03, List.cons_append,
        List.nil_append, Bool.false_eq_true, ite_false, ite_true]
      rcases r with ⟨n, hn⟩; simp only at h15' hr'; simp [LowReg.toReg, show listRegs 3#8 = [0, 1] by decide,
        show listRegs 96#8 = [5, 6] by decide]
      and_intros <;> omega)

end M0Crypto.Release.X25519CR
