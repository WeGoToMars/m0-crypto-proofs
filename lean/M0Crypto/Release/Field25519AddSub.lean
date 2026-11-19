import M0Crypto.Release.Field25519AddSubChain

set_option linter.unusedSimpArgs false

/-!
`fe_add_body` and `fe_sub_body` (generator `tools/gen_x25519.py`): `dst = a ± b` modulo `p`,
`r0 = dst`, `r1 = a`, `r2 = b`. They are the bodies of `m0c_fe_add` and `m0c_fe_sub` in Ed25519
and are inlined in `m0c_x25519`.

* `sumOp`: the 256-bit chain (`Field25519AddSubChain`).
* `addQ`: `r7 = 19 * (2 c + bit 255 of s)`, bit 255 of `s` cleared; `subQ`: `r7 = 19 * k`,
  `k = (1 - bit 255 of d) + 2 br`, bit 255 of `d` set.
* `outOp`: add or subtract `r7` from the low word, propagate, store the eight words to `dst`.

Every load comes before the first store, so `a`, `b` and `dst` may overlap in any way;
`feAdd_exec` and `feSub_exec` have no aliasing hypothesis.
-/

namespace M0Crypto.Release.Field25519AddSub
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (Region)
open M0Crypto.Release.Field25519Mem (toReg0 toReg1 toReg6 toReg7)
open M0Crypto.Release.Field25519Carry (adc_nat)
open M0Crypto.Release.Field25519Congr
open M0Crypto.Release.Field25519AddSubChain
/-- The fold of `fe_add_body`: `q = 2 c + bit 31 of r6`, `r7 = 19 q`, bit 31 of `r6` cleared. -/
def addQ : List Instr :=
  [.movImm 7 0, .dp .adcs 7 7, .lslImm 7 7 1, .lsrImm 1 6 31, .addReg 7 7 1, .lslImm 6 6 1,
    .lsrImm 6 6 1, .movImm 1 19, .dp .muls 7 1]

def feAddBody : List Instr := sumOp false ++ addQ ++ outOp false

theorem feAddBody_falls : feAddBody.all Instr.falls = true := by decide +kernel

theorem addQ_exec (s : State) :
    let t := execAll addQ s
    (t.regs 7).toNat = 19 * (2 * s.c.toNat + (s.regs 6).toNat / 2 ^ 31) ∧
      (t.regs 6).toNat = (s.regs 6).toNat % 2 ^ 31 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 6, 7] : List Reg) → t.regs r = s.regs r := by
  intro t
  have k1 : (1 : BitVec 5).toNat = 1 := rfl
  have k31 : (31 : BitVec 5).toNat = 31 := rfl
  have k19 : (19 : BitVec 8).setWidth 32 = 19#32 := rfl
  have k0 : (0 : BitVec 8).setWidth 32 = 0#32 := rfl
  have hm : t.mem = s.mem := execAll_mem _ _ (by decide)
  refine ⟨?_, ?_, hm, ?_⟩
  · simp (config := {decide := true}) only [t, addQ, execAll, State.reg, Field25519Mul.regs_lsl,
      Field25519Mul.regs_lsr, Field25519Mul.regs_adds, Field25519Mul.regs_adcs, Field25519Mul.c_adcs,
      Field25519Mul.c_movImm, InstrNext.regs_movImm, Field25519Mul.regs_muls, toReg1, toReg6, toReg7,
      ite_true, ite_false, ne_eq, not_false_eq_true, k0, k19, k1, k31]
    have e1 := adc_nat 0#32 0#32 s.c
    generalize addWithCarry 0#32 0#32 s.c = Z at *
    have e2 := adc_nat (Z.1 <<< 1) (s.regs 6 >>> 31) false
    generalize addWithCarry (Z.1 <<< 1) (s.regs 6 >>> 31) false = Y at *
    have := (s.regs 6).isLt
    have := Bool.toNat_le s.c
    have := Bool.toNat_le Y.2.1
    simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Bool.toNat_false, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.zero_mod] at e1 e2 ⊢
    omega
  · simp (config := {decide := true}) only [t, addQ, execAll, State.reg, Field25519Mul.regs_lsl,
      Field25519Mul.regs_lsr, Field25519Mul.regs_adds, Field25519Mul.regs_adcs, InstrNext.regs_movImm,
      Field25519Mul.regs_muls, toReg1, toReg6, toReg7, ite_true, ite_false, ne_eq, not_false_eq_true,
      k1]
    have := (s.regs 6).isLt
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h6, h7⟩ := hr
    have v : ∀ n : Reg, r ≠ n → r.val ≠ n.val := fun n h e => h (Fin.ext e)
    have v1 : r.val ≠ 1 := v 1 h1
    have v6 : r.val ≠ 6 := v 6 h6
    have v7 : r.val ≠ 7 := v 7 h7
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have l1 : ((1 : LowReg) : Nat) = 1 := rfl
      have l6 : ((6 : LowReg) : Nat) = 6 := rfl
      have l7 : ((7 : LowReg) : Nat) = 7 := rfl
      simp [addQ, Instr.dsts, l1, l6, l7, v1, v6, v7])

theorem val8_lt (w0 w1 w2 w3 w4 w5 w6 w7 : Word) : val8 w0 w1 w2 w3 w4 w5 w6 w7 < 2 ^ 256 := by
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := w4.isLt; have := w5.isLt; have := w6.isLt; have := w7.isLt
  simp only [val8]; omega

theorem opY_false : opY false = id := rfl

/-- The chain value of the add as two field values. Rewrites only: closing the `+ 0` by
`rfl` makes the kernel unfold `feVal`. -/
theorem memVal_add (m : Mem) (p q : Word) :
    memVal m id p + memVal m (opY false) q + false.toNat =
      Field25519Routines.feVal m p + Field25519Routines.feVal m q := by
  rw [opY_false, memVal_id, memVal_id, Bool.toNat_false, Nat.add_zero]

/-- Clearing bit 31 of the top word clears bit 255 of the value. -/
theorem fold_nat (S2 S r6 C R C' : Nat) (hreg : S2 + 2 ^ 224 * (r6 / 2 ^ 31 * 2 ^ 31) = S)
    (hs2 : S2 < 2 ^ 255) (h6 : r6 < 2 ^ 32)
    (ov : R + 2 ^ 256 * C' = S2 + 19 * (2 * C + r6 / 2 ^ 31)) :
    R + 2 ^ 256 * C' = S % 2 ^ 255 + 19 * (2 * C + S / 2 ^ 255) := by
  have hb : r6 / 2 ^ 31 ≤ 1 := by omega
  have e : S = S2 + 2 ^ 255 * (r6 / 2 ^ 31) := by rw [← hreg]; omega
  have h1 : S / 2 ^ 255 = r6 / 2 ^ 31 := by
    rw [e, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hs2, Nat.zero_add]
  have h2 : S % 2 ^ 255 = S2 := by
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs2]
  rw [h1, h2]; exact ov


/-- The arithmetic of `fe_add_body` from the three pieces. -/
theorem add_nat (A Bv S S2 r6 C R C' : Nat) (hA : A < 2 ^ 256) (hB : Bv < 2 ^ 256)
    (sv : S + 2 ^ 256 * C = A + Bv) (hsl : S < 2 ^ 256)
    (hreg : S2 + 2 ^ 224 * (r6 / 2 ^ 31 * 2 ^ 31) = S) (hs2 : S2 < 2 ^ 255) (h6 : r6 < 2 ^ 32)
    (ov : R + 2 ^ 256 * C' = S2 + 19 * (2 * C + r6 / 2 ^ 31)) (hR : R < 2 ^ 256) :
    (R : Int) ≡p (A : Int) + Bv := by
  have h := (Field25519Reduce.fe_add_nat A Bv S C R C' hA hB sv hsl
    (fold_nat _ _ _ _ _ _ hreg hs2 h6 ov) hR).2
  rwa [Int.natCast_add] at h

/-- The whole body: the value at `dst` is `a + b` modulo `p`; bytes outside `dst` and the
registers other than `r0`..`r12` are unchanged. -/
theorem feAdd_exec (s : State) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll feAddBody s
    (Field25519Routines.feVal t.mem (s.regs 0) : Int) ≡p
        Field25519Routines.feVal s.mem (s.regs 1) + Field25519Routines.feVal s.mem (s.regs 2) ∧
      (∀ y, ¬ Region (s.regs 0) 32 y → t.mem y = s.mem y) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t.regs r = s.regs r := by
  intro t
  simp only [t, feAddBody, execAll_append]
  obtain ⟨sv, sm, so⟩ := sumOp_exec s false
  generalize execAll (sumOp false) s = s1 at sv sm so
  obtain ⟨q7, q6, qm, qo⟩ := addQ_exec s1
  generalize execAll addQ s1 = s2 at q7 q6 qm qo
  have e0 : s2.regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  obtain ⟨ov, om, oo⟩ := outOp_exec s2 false (by rw [e0]; exact hf)
  rw [e0] at ov om
  have hreg : regVal s2 + 2 ^ 224 * ((s1.regs 6).toNat / 2 ^ 31 * 2 ^ 31) = regVal s1 := by
    have e : ∀ r : Reg, r ∉ ([1, 6, 7] : List Reg) → r ≠ 15 → s2.regs r = s1.regs r :=
      fun r h h15 => qo r h15 h
    simp only [regVal, val8, e 8 (by decide) (by decide), e 10 (by decide) (by decide),
      e 11 (by decide) (by decide), e 12 (by decide) (by decide), e 3 (by decide) (by decide),
      e 4 (by decide) (by decide), e 5 (by decide) (by decide), q6]
    omega
  have hA := Field25519Facts.feVal_lt s.mem (s.regs 1)
  have hB := Field25519Facts.feVal_lt s.mem (s.regs 2)
  have hR := Field25519Facts.feVal_lt (execAll (outOp false) s2).mem (s.regs 0)
  have hsl : regVal s1 < 2 ^ 256 := val8_lt _ _ _ _ _ _ _ _
  have hs2l : regVal s2 < 2 ^ 255 := by
    have := (s2.regs 8).isLt; have := (s2.regs 10).isLt; have := (s2.regs 11).isLt
    have := (s2.regs 12).isLt; have := (s2.regs 3).isLt; have := (s2.regs 4).isLt
    have := (s2.regs 5).isLt
    simp only [regVal, val8, q6]; omega
  have h6 := (s1.regs 6).isLt
  replace sv := sv.trans (memVal_add _ _ _)
  have hz : (opY false 0#32).toNat = 0 := rfl
  have z0 : (0#32 : Word).toNat = 0 := rfl
  simp only [hz, z0, Nat.zero_mul, Bool.toNat_false, Nat.add_zero, opY_false, id_eq, q7] at ov
  have hc := add_nat _ _ _ _ _ _ _ _ hA hB sv hsl hreg hs2l h6 ov hR
  refine ⟨hc, fun y hy => by rw [om y hy, qm, sm], ?_⟩
  intro r h15 hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12⟩ := hr
  rw [oo r h15 (by simp [h0, h1, h2, h3, h4, h5, h6, h7]), qo r h15 (by simp [h1, h6, h7]),
    so r h15 (by simp [h1, h2, h3, h4, h5, h6, h8, h10, h11, h12])]



/-- The fold of `fe_sub_body`: `k = (1 - bit 31 of r6) + 2 (1 - C)`, `r7 = 19 k`, bit 31 of
`r6` set. -/
def subQ : List Instr :=
  [.dp .sbcs 7 7, .lslImm 7 7 1, .dp .mvns 1 6, .lsrImm 1 1 31, .subReg 7 1 7, .movImm 1 1,
    .lslImm 1 1 31, .dp .orrs 6 1, .movImm 1 19, .dp .muls 7 1]

def feSubBody : List Instr := sumOp true ++ subQ ++ outOp true

theorem feSubBody_falls : feSubBody.all Instr.falls = true := by decide +kernel

/-- Setting bit 31 of a word. -/
theorem or_top (a : Nat) (ha : a < 2 ^ 32) : a ||| 2 ^ 31 = a % 2 ^ 31 + 2 ^ 31 := by
  have hl : a % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have e : a = (a / 2 ^ 31) <<< 31 ||| a % 2 ^ 31 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]; omega
  have r : a % 2 ^ 31 + 2 ^ 31 = 1 <<< 31 ||| a % 2 ^ 31 := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]; omega
  have t : (2 : Nat) ^ 31 = 1 <<< 31 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hb : a / 2 ^ 31 = 0 ∨ a / 2 ^ 31 = 1 := by omega
  rw [r]
  conv => lhs; rw [e]
  rcases hb with h | h <;> rw [h]
  · rw [Nat.zero_shiftLeft, Nat.zero_or, t, Nat.or_comm]
  · rw [t, Nat.or_assoc, Nat.or_comm (a % _), ← Nat.or_assoc, Nat.or_self]

theorem subQ_exec (s : State) :
    let t := execAll subQ s
    (t.regs 7).toNat = 19 * ((1 - (s.regs 6).toNat / 2 ^ 31) + 2 * (1 - s.c.toNat)) ∧
      (t.regs 6).toNat = (s.regs 6).toNat % 2 ^ 31 + 2 ^ 31 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 6, 7] : List Reg) → t.regs r = s.regs r := by
  intro t
  have k1 : (1 : BitVec 5).toNat = 1 := rfl
  have k31 : (31 : BitVec 5).toNat = 31 := rfl
  have k19 : (19 : BitVec 8).setWidth 32 = 19#32 := rfl
  have kb : ((1 : BitVec 8).setWidth 32 : Word) <<< 31 = 0x80000000#32 := by decide
  have hm : t.mem = s.mem := execAll_mem _ _ (by decide)
  refine ⟨?_, ?_, hm, ?_⟩
  · simp (config := {decide := true}) only [t, subQ, execAll, State.reg, Field25519Mul.regs_lsl,
      Field25519Mul.regs_lsr, Field25519Mul.regs_subs, Field25519Mul.regs_sbcs, Field25519Mem.regs_mvns,
      regs_orrs, InstrNext.regs_movImm, Field25519Mul.regs_muls, toReg1, toReg6, toReg7,
      ite_true, ite_false, ne_eq, not_false_eq_true, k19, k1, k31]
    have hx : (~~~(s.regs 6) >>> 31).toNat = 1 - (s.regs 6).toNat / 2 ^ 31 := by
      have := (s.regs 6).isLt
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_not, Nat.shiftRight_eq_div_pow]
      omega
    generalize ~~~(s.regs 6) >>> 31 = X at *
    have e1 := adc_nat (s.regs 7) (~~~(s.regs 7)) s.c
    generalize addWithCarry (s.regs 7) (~~~(s.regs 7)) s.c = W at *
    have e2 := adc_nat X (~~~(W.1 <<< 1)) true
    generalize addWithCarry X (~~~(W.1 <<< 1)) true = Z at *
    have := (s.regs 7).isLt; have := W.1.isLt; have := Z.1.isLt
    have := Bool.toNat_le s.c; have := Bool.toNat_le W.2.1; have := Bool.toNat_le Z.2.1
    simp only [BitVec.toNat_mul, BitVec.toNat_not, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, Bool.toNat_true, Nat.reduceMod] at e1 e2 ⊢
    omega
  · simp (config := {decide := true}) only [t, subQ, execAll, State.reg, Field25519Mul.regs_lsl,
      Field25519Mul.regs_lsr, Field25519Mul.regs_subs, Field25519Mul.regs_sbcs, Field25519Mem.regs_mvns,
      regs_orrs, InstrNext.regs_movImm, Field25519Mul.regs_muls, toReg1, toReg6, toReg7, ite_true,
      ite_false, ne_eq, not_false_eq_true, k1, k31, kb]
    rw [BitVec.toNat_or]
    exact or_top _ (s.regs 6).isLt
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h6, h7⟩ := hr
    have v : ∀ n : Reg, r ≠ n → r.val ≠ n.val := fun n h e => h (Fin.ext e)
    have v1 : r.val ≠ 1 := v 1 h1
    have v6 : r.val ≠ 6 := v 6 h6
    have v7 : r.val ≠ 7 := v 7 h7
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have l1 : ((1 : LowReg) : Nat) = 1 := rfl
      have l6 : ((6 : LowReg) : Nat) = 6 := rfl
      have l7 : ((7 : LowReg) : Nat) = 7 := rfl
      simp [subQ, Instr.dsts, l1, l6, l7, v1, v6, v7])

/-- The arithmetic of `fe_sub_body` from the three pieces: `NB` is the complement of `b`,
`S` the chain value with top word `r6`, `S2` the value after the fold. -/
theorem sub_nat (A Bv NB S S2 r6 C R C' : Nat) (hA : A < 2 ^ 256) (hB : Bv < 2 ^ 256)
    (hnb : NB + Bv + 1 = 2 ^ 256) (sv : S + 2 ^ 256 * C = A + NB + 1) (hsl : S < 2 ^ 256)
    (hlo : 2 ^ 224 * r6 ≤ S) (hhi : S < 2 ^ 224 * r6 + 2 ^ 224) (h6 : r6 < 2 ^ 32)
    (hreg : S2 + 2 ^ 224 * r6 = S + 2 ^ 224 * (r6 % 2 ^ 31 + 2 ^ 31))
    (ov : R + 2 ^ 256 * C' = S2 + (2 ^ 256 - 19 * ((1 - r6 / 2 ^ 31) + 2 * (1 - C))))
    (hR : R < 2 ^ 256) :
    (R : Int) ≡p (A : Int) - Bv := by
  have hC : C ≤ 1 := by omega
  have hd : S + Bv = A + 2 ^ 256 * (1 - C) := by omega
  have hbit : S / 2 ^ 255 = r6 / 2 ^ 31 := by omega
  have hmod : S % 2 ^ 255 + 2 ^ 255 = S2 := by omega
  have hC' : C' ≤ 1 := by omega
  exact (Field25519Reduce.fe_sub_nat A Bv S (1 - C) R (1 - C') hA hB hd hsl
    (by rw [hbit]; omega) hR).2

theorem opY_true : opY true = fun y => ~~~y := rfl

/-- The whole body: the value at `dst` is `a - b` modulo `p`; bytes outside `dst` and the
registers other than `r0`..`r12` are unchanged. -/
theorem feSub_exec (s : State) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll feSubBody s
    (Field25519Routines.feVal t.mem (s.regs 0) : Int) ≡p
        Field25519Routines.feVal s.mem (s.regs 1) - Field25519Routines.feVal s.mem (s.regs 2) ∧
      (∀ y, ¬ Region (s.regs 0) 32 y → t.mem y = s.mem y) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t.regs r = s.regs r := by
  intro t
  simp only [t, feSubBody, execAll_append]
  obtain ⟨sv, sm, so⟩ := sumOp_exec s true
  generalize execAll (sumOp true) s = s1 at sv sm so
  obtain ⟨q7, q6, qm, qo⟩ := subQ_exec s1
  generalize execAll subQ s1 = s2 at q7 q6 qm qo
  have e0 : s2.regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  obtain ⟨ov, om, oo⟩ := outOp_exec s2 true (by rw [e0]; exact hf)
  rw [e0] at ov om
  have e : ∀ r : Reg, r ∉ ([1, 6, 7] : List Reg) → r ≠ 15 → s2.regs r = s1.regs r :=
    fun r h h15 => qo r h15 h
  have hreg : regVal s2 + 2 ^ 224 * (s1.regs 6).toNat =
      regVal s1 + 2 ^ 224 * ((s1.regs 6).toNat % 2 ^ 31 + 2 ^ 31) := by
    simp only [regVal, val8, e 8 (by decide) (by decide), e 10 (by decide) (by decide),
      e 11 (by decide) (by decide), e 12 (by decide) (by decide), e 3 (by decide) (by decide),
      e 4 (by decide) (by decide), e 5 (by decide) (by decide), q6]
    omega
  have hb1 : 2 ^ 224 * (s1.regs 6).toNat ≤ regVal s1 ∧
      regVal s1 < 2 ^ 224 * (s1.regs 6).toNat + 2 ^ 224 := by
    have := (s1.regs 8).isLt; have := (s1.regs 10).isLt; have := (s1.regs 11).isLt
    have := (s1.regs 12).isLt; have := (s1.regs 3).isLt; have := (s1.regs 4).isLt
    have := (s1.regs 5).isLt
    simp only [regVal, val8]; omega
  have hA := Field25519Facts.feVal_lt s.mem (s.regs 1)
  have hB := Field25519Facts.feVal_lt s.mem (s.regs 2)
  have hR := Field25519Facts.feVal_lt (execAll (outOp true) s2).mem (s.regs 0)
  have hsl : regVal s1 < 2 ^ 256 := val8_lt _ _ _ _ _ _ _ _
  have h6 := (s1.regs 6).isLt
  rw [memVal_id, Bool.toNat_true] at sv
  have hY : (s2.regs 7).toNat < 2 ^ 32 := (s2.regs 7).isLt
  have hz : (opY true 0#32).toNat = 2 ^ 32 - 1 := by decide
  have hk : (2 : Nat) ^ 32 - 1 + (2 ^ 32 - 1) * (2 ^ 32 + 2 ^ 64 + 2 ^ 96 + 2 ^ 128 + 2 ^ 160 +
      2 ^ 192 + 2 ^ 224) + 1 = 2 ^ 256 := by decide
  have ho : ∀ y : Word, (opY true y).toNat = 2 ^ 32 - 1 - y.toNat := fun y => by
    rw [opY_true]; exact BitVec.toNat_not
  rw [hz, ho, Bool.toNat_true, q7] at ov
  have hc := sub_nat _ _ _ _ _ _ _ _ (C' := (execAll (outOp true) s2).c.toNat) hA hB
    (memVal_not _ _) sv hsl hb1.1 hb1.2 h6 hreg (by omega) hR
  refine ⟨hc, fun y hy => by rw [om y hy, qm, sm], ?_⟩
  intro r h15 hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12⟩ := hr
  rw [oo r h15 (by simp [h0, h1, h2, h3, h4, h5, h6, h7]), qo r h15 (by simp [h1, h6, h7]),
    so r h15 (by simp [h1, h2, h3, h4, h5, h6, h8, h10, h11, h12])]

end M0Crypto.Release.Field25519AddSub
