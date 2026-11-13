import M0Crypto.Release.X25519InlChain
import M0Crypto.Release.X25519Reduce

set_option linter.unusedSimpArgs false

/-!
`fe_add_body` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = a + b`
modulo `p`, `r0 = dst`, `r1 = a`, `r2 = b`.

* `sumOp false`: the 256-bit sum `s + 2^256 c = a + b` (`X25519InlChain`).
* `addQ`: `r7 = 19 * (2 c + bit 255 of s)`, bit 255 of `s` cleared.
* `outOp false`: add `r7` to the low word, propagate, store the eight words to `dst`.

Every load comes before the first store, so `a`, `b` and `dst` may overlap in any way; the
run lemma has no aliasing hypothesis.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region ReachW InRegion)
open M0Crypto.Release.X25519Block (AccAll AccOk accAll_append)
open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg6 toReg7)
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Release.X25519Congr

/-- The fold of `fe_add_body`: `q = 2 c + bit 31 of r6`, `r7 = 19 q`, bit 31 of `r6` cleared. -/
def addQ : List Instr :=
  [.movImm 7 0, .dp .adcs 7 7, .lslImm 7 7 1, .lsrImm 1 6 31, .addReg 7 7 1, .lslImm 6 6 1,
    .lsrImm 6 6 1, .movImm 1 19, .dp .muls 7 1]

def feAddBody : List Instr := sumOp false ++ addQ ++ outOp false

theorem feAddBody_at : SiteOk feAddBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel

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
  · simp (config := {decide := true}) only [t, addQ, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, X25519Mul.regs_adds, X25519Mul.regs_adcs, X25519Mul.c_adcs,
      X25519Mul.c_movImm, Blake2s.regs_movImm, X25519Mul.regs_muls, toReg1, toReg6, toReg7,
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
  · simp (config := {decide := true}) only [t, addQ, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, X25519Mul.regs_adds, X25519Mul.regs_adcs, Blake2s.regs_movImm,
      X25519Mul.regs_muls, toReg1, toReg6, toReg7, ite_true, ite_false, ne_eq, not_false_eq_true,
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

theorem addQ_acc {Wr : Word → Prop} (s : State) : AccAll (AccOk Wr) addQ s :=
  X25519MulcWord.accAll_regOnly _ _ (by decide)

theorem val8_lt (w0 w1 w2 w3 w4 w5 w6 w7 : Word) : val8 w0 w1 w2 w3 w4 w5 w6 w7 < 2 ^ 256 := by
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := w4.isLt; have := w5.isLt; have := w6.isLt; have := w7.isLt
  simp only [val8]; omega

theorem opY_false : opY false = id := rfl

/-- The chain value of the add as two field values. Rewrites only: closing the `+ 0` by
`rfl` makes the kernel unfold `feVal`. -/
theorem memVal_add (m : Mem) (p q : Word) :
    memVal m id p + memVal m (opY false) q + false.toNat =
      X25519Routines.feVal m p + X25519Routines.feVal m q := by
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
  have h := (X25519Reduce.fe_add_nat A Bv S C R C' hA hB sv hsl
    (fold_nat _ _ _ _ _ _ hreg hs2 h6 ov) hR).2
  rwa [Int.natCast_add] at h

/-- The whole body: the value at `dst` is `a + b` modulo `p`; bytes outside `dst` and the
registers other than `r0`..`r12` are unchanged. -/
theorem feAdd_exec (s : State) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll feAddBody s
    (X25519Routines.feVal t.mem (s.regs 0) : Int) ≡p
        X25519Routines.feVal s.mem (s.regs 1) + X25519Routines.feVal s.mem (s.regs 2) ∧
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
  have hA := X25519MulcFacts.feVal_lt s.mem (s.regs 1)
  have hB := X25519MulcFacts.feVal_lt s.mem (s.regs 2)
  have hR := X25519MulcFacts.feVal_lt (execAll (outOp false) s2).mem (s.regs 0)
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

theorem feAdd_acc {Wr : Word → Prop} (s : State) (h0 : (s.regs 0).toNat % 4 = 0)
    (h1 : (s.regs 1).toNat % 4 = 0) (h2 : (s.regs 2).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) feAddBody s := by
  simp only [feAddBody]
  obtain ⟨-, -, so⟩ := sumOp_exec s false
  refine accAll_append (accAll_append (sumOp_acc s false h1 h2) (addQ_acc _)) ?_
  obtain ⟨-, -, -, qo⟩ := addQ_exec (execAll (sumOp false) s)
  have e0 : (execAll addQ (execAll (sumOp false) s)).regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  rw [execAll_append]
  exact outOp_acc _ false (by rw [e0]; exact h0) (by rw [e0]; exact hW)

/-- One `fe_add_body` block in a `ReachW` proof: `dst = a + b` modulo `p`. `a`, `b`, `dst`
may alias in any way. -/
theorem feAdd_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {dst a b : Word}
    (hseq : seqAt B off feAddBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize feAddBody))
    (h0 : t.regs 0 = dst) (h1 : t.regs 1 = a) (h2 : t.regs 2 = b)
    (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0) (hbb : b.toNat % 4 = 0)
    (hf : dst.toNat + 32 ≤ 2 ^ 32)
    (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize feAddBody) →
      (X25519Routines.feVal t'.mem dst : Int) ≡p
          X25519Routines.feVal t.mem a + X25519Routines.feVal t.mem b →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst h0 h1 h2
  obtain ⟨ev, em, eo⟩ := feAdd_exec t hf
  refine X25519Block.ReachW.blockAcc hb _ off hpc hoff hseq feAddBody_falls (feAdd_acc t hd ha hbb hW) hr
    (k _ ?_ ev em eo)
  rw [execAll_pc _ _ feAddBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
