import M0Crypto.Release.X25519CRAddH
import M0Crypto.Release.X25519CRWord

set_option linter.unusedSimpArgs false

/-!
Phases B and C of `combineReduce` (`X25519Macros.reducePhaseB`, `reducePhaseC`).

Phase B: `Y4..Y7` in `r0..r3` and `Y8` in `r6` from `P4..P7` (xored with the mask, the mask
word itself on top), the phase-A carry count in `r4`, `L4..L7` and `H4..H7`; the value is
modulo `2^160` (carries out of `r6` are dropped). Phase C adds `H0..H3`, stores the four low
words over `H0..H3` and parks the top word in `r9`.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Macros (sl SH SP_ SPP SN reducePhaseB reducePhaseC xorN)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds c_adcs c_adds c_movImm c_movHi)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.InstrNext (regs_eors regs_movImm regs_movHi)

/-- The first block of phase B: load `P4..P7`, apply the mask, put the mask word in `r6`, add
the phase-A carry count `r4`. -/
def bFront (sq : Bool) : List Instr :=
  [.addRdSp 7 (sl (SPP + 4)), .ldm 7 0x0f] ++
  (if sq then [.dp .mvns 0 0, .dp .mvns 1 1, .dp .mvns 2 2, .dp .mvns 3 3, .movImm 6 0, .dp .mvns 6 6]
   else xorN false 6) ++
  [.movImm 5 0, .addReg 0 0 4, .dp .adcs 1 5, .dp .adcs 2 5, .dp .adcs 3 5, .dp .adcs 6 5]

theorem reducePhaseB_split (sq : Bool) :
    reducePhaseB sq = bFront sq ++ addH (SP_ + 4) ++ addH (SH + 4) := by
  cases sq <;> rfl

theorem reducePhaseC_split :
    reducePhaseC = addH SH ++ [.movHi 9 6, .subImm8 7 16, .stm 7 0x0f] := rfl

theorem not_zero_mask : ~~~(BitVec.setWidth 32 (0 : BitVec 8)) = mask true := by
  simp only [mask, ite_true]; decide

theorem regs_hi_other (is : List Instr) (s : State) (r : Reg) (h15 : r ≠ 15) (h8 : 8 ≤ r.val)
    (h : ∀ i ∈ is, ∀ d ∈ i.dsts, d < 8) : (execAll is s).regs r = s.regs r := by
  have h15' : r.val ≠ 15 := fun e => h15 (Fin.ext e)
  refine execAll_regs_other _ _ _ h15' ?_
  simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  intro i hi hm
  have := h i hi _ hm; omega

/-- The word identity of `bFront`: add a small word to four words, carry into the fifth. -/
theorem front_close (x0 x1 x2 x3 m a z : Word) (hz : z.toNat = 0) :
    w4 (addWithCarry x0 a false).1 (addWithCarry x1 z (addWithCarry x0 a false).2.1).1
        (addWithCarry x2 z (addWithCarry x1 z (addWithCarry x0 a false).2.1).2.1).1
        (addWithCarry x3 z (addWithCarry x2 z (addWithCarry x1 z
          (addWithCarry x0 a false).2.1).2.1).2.1).1 +
      2 ^ 128 * (addWithCarry m z (addWithCarry x3 z (addWithCarry x2 z (addWithCarry x1 z
          (addWithCarry x0 a false).2.1).2.1).2.1).2.1).1.toNat =
      (w4 x0 x1 x2 x3 + (2 ^ 128 * m.toNat + a.toNat)) % 2 ^ 160 := by
  generalize ga0 : addWithCarry x0 a false = A0
  generalize ga1 : addWithCarry x1 z A0.2.1 = A1
  generalize ga2 : addWithCarry x2 z A1.2.1 = A2
  generalize ga3 : addWithCarry x3 z A2.2.1 = A3
  generalize ga4 : addWithCarry m z A3.2.1 = A4
  have e0 := adc_nat x0 a false; have e1 := adc_nat x1 z A0.2.1
  have e2 := adc_nat x2 z A1.2.1; have e3 := adc_nat x3 z A2.2.1
  have e4 := adc_nat m z A3.2.1
  rw [ga0] at e0; rw [ga1] at e1; rw [ga2] at e2; rw [ga3] at e3; rw [ga4] at e4
  have := carry_le m z A3.2.1; rw [ga4] at this
  have := A4.1.isLt; have := A0.1.isLt; have := A1.1.isLt; have := A2.1.isLt; have := A3.1.isLt
  simp only [w4, Bool.toNat_false] at *
  omega

theorem bFront_exec (s : State) (sq neg : Bool) (hN : NOk sq s neg) :
    let t := execAll (bFront sq) s
    let F := fr s.mem s.sp
    w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 128 * (t.regs 6).toNat =
        (w4 (F (SPP + 4) ^^^ mask neg) (F (SPP + 5) ^^^ mask neg) (F (SPP + 6) ^^^ mask neg)
          (F (SPP + 7) ^^^ mask neg) + 2 ^ 128 * (mask neg).toNat + (s.regs 4).toNat) % 2 ^ 160 ∧
      t.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t F
  have hm : t.mem = s.mem := execAll_mem _ _ (by cases sq <;> simp [bFront, xorN, Instr.writesMem])
  have h15 : (13 : Reg) ≠ 15 := by decide
  refine ⟨?_, hm, fun r h15 h8 => regs_hi_other _ _ _ h15 h8 ?_⟩
  · simp only [F]
    cases sq
    · simp only [NOk, Bool.false_eq_true, ite_false, State.sp] at hN
      simp only [t, bFront, xorN, execAll, List.cons_append, List.nil_append,
        Bool.false_eq_true, ite_false]
      simp (config := {decide := true}) only [regs_adcs, regs_adds, c_adcs, c_adds, regs_ldm,
        regs_addRdSp_sl _ _ _ (by decide : SPP + 4 < 256), regs_ldrSp_sl _ _ _ (by decide : SN < 256),
        regs_movImm, regs_eors, c_ldm, c_addRdSp, c_movImm, c_eors, c_ldrSp, mem_ldm, mem_addRdSp,
        mem_ldrSp, mem_dp, mem_addReg, mem_movImm, State.reg, toReg0, toReg1, toReg2, toReg3,
        toReg4, toReg5, toReg6, toReg7, listRegs_0f, bitCount_0f, List.map, List.idxOf,
        List.findIdx_cons, List.findIdx_nil, beq_self_eq_true, Bool.cond_true, Bool.cond_false,
        ite_true, ite_false, ne_eq, List.mem_cons, State.sp, h15]
      simp only [rd_slot, slot_add, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd]
      simp only [rd_slot0, hN]
      exact front_close _ _ _ _ _ _ _ (by simp)
    · simp only [NOk, ite_true] at hN
      subst hN
      simp only [t, bFront, execAll, List.cons_append, List.nil_append, ite_true]
      simp (config := {decide := true}) only [regs_adcs, regs_adds, c_adcs, c_adds, regs_ldm,
        regs_addRdSp_sl _ _ _ (by decide : SPP + 4 < 256), regs_movImm, regs_mvns, c_ldm,
        c_addRdSp, c_movImm, c_mvns, mem_ldm, mem_addRdSp, mem_dp, mem_addReg, mem_movImm,
        State.reg, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, listRegs_0f,
        bitCount_0f, List.map, List.idxOf, List.findIdx_cons, List.findIdx_nil, beq_self_eq_true,
        Bool.cond_true, Bool.cond_false, ite_true, ite_false, ne_eq, List.mem_cons, State.sp, h15]
      simp only [rd_slot, slot_add, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd]
      simp only [rd_slot0, not_xor, not_zero_mask]
      exact front_close _ _ _ _ _ _ _ (by simp)
  · cases sq <;> simp (config := {decide := true}) [bFront, xorN, Instr.dsts, LowReg.toReg,
      show listRegs 15#8 = [0, 1, 2, 3] by decide]

theorem phaseB_exec (s : State) (sq neg : Bool) (hN : NOk sq s neg) :
    let t := execAll (reducePhaseB sq) s
    let F := fr s.mem s.sp
    w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 128 * (t.regs 6).toNat =
        (w4 (F (SPP + 4) ^^^ mask neg) (F (SPP + 5) ^^^ mask neg) (F (SPP + 6) ^^^ mask neg)
            (F (SPP + 7) ^^^ mask neg) + 2 ^ 128 * (mask neg).toNat + (s.regs 4).toNat +
          w4 (F (SP_ + 4)) (F (SP_ + 5)) (F (SP_ + 6)) (F (SP_ + 7)) +
          w4 (F (SH + 4)) (F (SH + 5)) (F (SH + 6)) (F (SH + 7))) % 2 ^ 160 ∧
      t.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t F
  have h13 : (13 : Reg) ≠ 15 := by decide
  have h13' : 8 ≤ (13 : Reg).val := by decide
  obtain ⟨v1, m1, o1⟩ := bFront_exec s sq neg hN
  obtain ⟨v2, m2, -, o2⟩ := addH_exec (execAll (bFront sq) s) (SP_ + 4) (by decide)
  obtain ⟨v3, m3, -, o3⟩ := addH_exec (execAll (addH (SP_ + 4)) (execAll (bFront sq) s)) (SH + 4)
    (by decide)
  have sp1 := o1 13 h13 h13'; have sp2 := o2 13 h13 h13'
  simp only [State.sp, m1, m2, sp1, sp2] at v2 v3
  simp only [t, reducePhaseB_split, execAll_append]
  refine ⟨?_, by rw [m3, m2, m1], fun r h15 h8 => by rw [o3 r h15 h8, o2 r h15 h8, o1 r h15 h8]⟩
  simp only [F, State.sp] at v1 ⊢
  rw [v3, v2, v1]
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

/-- `subs r7, #16` takes the frame pointer `sp + 4(k + 4)` back to `sp + 4k`. -/
theorem slot_sub16 (sp : Word) (k : Nat) :
    (addWithCarry (slot sp (k + 4)) (~~~((16 : BitVec 8).setWidth 32)) true).1 = slot sp k := by
  unfold slot
  rw [show 4 * (k + 4) = 4 * k + 16 by omega, sub_imm _ _ _ _ (by decide)]
  simp

theorem phaseC_exec (s : State) :
    let t := execAll reducePhaseC s
    let F := fr s.mem s.sp
    ∃ f0 f1 f2 f3 : Word, t.mem = storeWords s.mem (slot s.sp SH) [f0, f1, f2, f3] ∧
      w4 f0 f1 f2 f3 + 2 ^ 128 * (t.regs 9).toNat =
        (w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) + 2 ^ 128 * (s.regs 6).toNat +
          w4 (F SH) (F (SH + 1)) (F (SH + 2)) (F (SH + 3))) % 2 ^ 160 ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 9 → t.regs r = s.regs r := by
  intro t F
  obtain ⟨v1, m1, r7, o1⟩ := addH_exec s SH (by decide)
  generalize hs1 : execAll (addH SH) s = s1 at v1 m1 r7 o1
  refine ⟨s1.regs 0, s1.regs 1, s1.regs 2, s1.regs 3, ?_, ?_, ?_⟩
  · simp only [t, reducePhaseC_split, execAll_append, hs1, execAll]
    simp (config := {decide := true}) only [mem_stm, mem_subImm8, mem_movHi, regs_subImm8,
      regs_movHi, State.reg, toReg0, toReg1, toReg2, toReg3, toReg7, listRegs_0f, List.map,
      ite_true, ite_false, r7, slot_sub16, m1]
  · have h9 : (9 : Reg) ≠ 15 := by decide
    have e9 : t.regs 9 = s1.regs 6 := by
      simp (config := {decide := true}) only [t, reducePhaseC_split, execAll_append, hs1, execAll,
        regs_stm _ _ _ _ h9, regs_subImm8 _ _ _ _ h9, regs_movHi _ _ _ _ h9, toReg7, ite_true,
        ite_false]
    rw [e9]; exact v1
  · intro r h15 h8 h9
    have hn7 : (r = LowReg.toReg 7) = False := hi_ne r h8 7
    have e : t.regs r = s1.regs r := by
      simp only [t, reducePhaseC_split, execAll_append, hs1, execAll, regs_stm _ _ _ _ h15,
        regs_subImm8 _ _ _ _ h15, regs_movHi _ _ _ _ h15, hn7, h9, ite_false]
    rw [e, o1 r h15 h8]

end M0Crypto.Release.X25519CR
