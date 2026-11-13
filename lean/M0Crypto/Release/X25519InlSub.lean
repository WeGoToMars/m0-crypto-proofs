import M0Crypto.Release.X25519InlAdd

set_option linter.unusedSimpArgs false

/-!
`fe_sub_body` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = a - b`
modulo `p`, `r0 = dst`, `r1 = a`, `r2 = b`.

* `sumOp true`: the 256-bit difference `d + b = a + 2^256 br`, the borrow `br = 1 - C`.
* `subQ`: `r7 = 19 * k`, `k = (1 - bit 255 of d) + 2 br`; bit 255 of `d` set.
* `outOp true`: subtract `r7` from the low word, propagate, store the eight words to `dst`.

As for the add, every load comes before the first store: no aliasing hypothesis.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region ReachW InRegion)
open M0Crypto.Release.X25519Block (AccAll AccOk accAll_append)
open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg6 toReg7)
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Release.X25519Congr

/-- The fold of `fe_sub_body`: `k = (1 - bit 31 of r6) + 2 (1 - C)`, `r7 = 19 k`, bit 31 of
`r6` set. -/
def subQ : List Instr :=
  [.dp .sbcs 7 7, .lslImm 7 7 1, .dp .mvns 1 6, .lsrImm 1 1 31, .subReg 7 1 7, .movImm 1 1,
    .lslImm 1 1 31, .dp .orrs 6 1, .movImm 1 19, .dp .muls 7 1]

def feSubBody : List Instr := sumOp true ++ subQ ++ outOp true

theorem feSubBody_at : SiteOk feSubBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel

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
  · simp (config := {decide := true}) only [t, subQ, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, X25519Mul.regs_subs, X25519Mul.regs_sbcs, X25519Mem.regs_mvns,
      regs_orrs, Blake2s.regs_movImm, X25519Mul.regs_muls, toReg1, toReg6, toReg7,
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
  · simp (config := {decide := true}) only [t, subQ, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, X25519Mul.regs_subs, X25519Mul.regs_sbcs, X25519Mem.regs_mvns,
      regs_orrs, Blake2s.regs_movImm, X25519Mul.regs_muls, toReg1, toReg6, toReg7, ite_true,
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

theorem subQ_acc {Wr : Word → Prop} (s : State) : AccAll (AccOk Wr) subQ s :=
  X25519MulcWord.accAll_regOnly _ _ (by decide)

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
  exact (X25519Reduce.fe_sub_nat A Bv S (1 - C) R (1 - C') hA hB hd hsl
    (by rw [hbit]; omega) hR).2

theorem opY_true : opY true = fun y => ~~~y := rfl

/-- The whole body: the value at `dst` is `a - b` modulo `p`; bytes outside `dst` and the
registers other than `r0`..`r12` are unchanged. -/
theorem feSub_exec (s : State) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll feSubBody s
    (X25519Routines.feVal t.mem (s.regs 0) : Int) ≡p
        X25519Routines.feVal s.mem (s.regs 1) - X25519Routines.feVal s.mem (s.regs 2) ∧
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
  have hA := X25519MulcFacts.feVal_lt s.mem (s.regs 1)
  have hB := X25519MulcFacts.feVal_lt s.mem (s.regs 2)
  have hR := X25519MulcFacts.feVal_lt (execAll (outOp true) s2).mem (s.regs 0)
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

theorem feSub_acc {Wr : Word → Prop} (s : State) (h0 : (s.regs 0).toNat % 4 = 0)
    (h1 : (s.regs 1).toNat % 4 = 0) (h2 : (s.regs 2).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) feSubBody s := by
  simp only [feSubBody]
  obtain ⟨-, -, so⟩ := sumOp_exec s true
  refine accAll_append (accAll_append (sumOp_acc s true h1 h2) (subQ_acc _)) ?_
  obtain ⟨-, -, -, qo⟩ := subQ_exec (execAll (sumOp true) s)
  have e0 : (execAll subQ (execAll (sumOp true) s)).regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  rw [execAll_append]
  exact outOp_acc _ true (by rw [e0]; exact h0) (by rw [e0]; exact hW)

/-- One `fe_sub_body` block in a `ReachW` proof: `dst = a - b` modulo `p`. `a`, `b`, `dst`
may alias in any way. -/
theorem feSub_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {dst a b : Word}
    (hseq : seqAt B off feSubBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize feSubBody))
    (h0 : t.regs 0 = dst) (h1 : t.regs 1 = a) (h2 : t.regs 2 = b)
    (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0) (hbb : b.toNat % 4 = 0)
    (hf : dst.toNat + 32 ≤ 2 ^ 32)
    (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize feSubBody) →
      (X25519Routines.feVal t'.mem dst : Int) ≡p
          X25519Routines.feVal t.mem a - X25519Routines.feVal t.mem b →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst h0 h1 h2
  obtain ⟨ev, em, eo⟩ := feSub_exec t hf
  refine X25519Block.ReachW.blockAcc hb _ off hpc hoff hseq feSubBody_falls
    (feSub_acc t hd ha hbb hW) hr (k _ ?_ ev em eo)
  rw [execAll_pc _ _ feSubBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
