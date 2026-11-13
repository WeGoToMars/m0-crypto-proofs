import M0Crypto.Release.X25519CRWord

set_option linter.unusedSimpArgs false

/-!
The top word of `combineReduce` (`X25519Macros.reduceTop`): `v = L7 + Y3 + 38 * H7` with `Y3`
parked in `r12`, split as `base7 + 2^31 * q`; `r12 := base7`, `r4 := 19 * q`. It also sets
the loop constants `r7 = 38`, `r2 = 0` and loads the output pointer into `r0`.

The macro is split (by `rfl`) into `topA` (load and `L7 + 38 * H7`), the parked-word step
`wY 4 5 3 (some 12)` of the loop (its lemma `wY_exec` is reused) and `topC` (split at bit 31).
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519Macros (sl SH SP_ SDST reduceTop)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds regs_lsr regs_lsl regs_muls regs_uxth
  toReg_inj mul_small lo16 hi16 shl16 c_adds c_adcs c_movImm)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.InstrNext (toReg_ne15 regs_movHi regs_movImm)

def topA : List Instr :=
  [.ldrSp 4 (sl (SH + 7)), .ldrSp 5 (sl (SP_ + 7)), .movImm 7 38, .movImm 2 0,
   .uxth 6 4, .lsrImm 4 4 16, .dp .muls 6 7, .dp .muls 4 7, .lslImm 3 4 16, .lsrImm 4 4 16,
   .addReg 5 5 6, .dp .adcs 4 2, .addReg 5 5 3, .dp .adcs 4 2]

def topC : List Instr :=
  [.lslImm 4 4 1, .lsrImm 3 5 31, .addReg 4 4 3, .lslImm 5 5 1, .lsrImm 5 5 1, .movHi 12 5,
   .movImm 3 19, .dp .muls 4 3, .ldrSp 0 (sl SDST)]

theorem reduceTop_split : reduceTop = topA ++ wY 4 5 3 (some 12) ++ topC := rfl

theorem topA_exec (s : State) :
    let t := execAll topA s
    let F := fr s.mem s.sp
    (t.reg 5).toNat + 2 ^ 32 * (t.reg 4).toNat = (F (SP_ + 7)).toNat + 38 * (F (SH + 7)).toNat ∧
      (t.reg 7).toNat = 38 ∧ (t.reg 2).toNat = 0 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t F
  have hm : t.mem = s.mem := execAll_mem _ _ (by simp [topA, Instr.writesMem])
  have h1 : SH + 7 < 256 := by decide
  have h2 : SP_ + 7 < 256 := by decide
  refine ⟨?_, ?_, ?_, hm, ?_⟩
  rotate_left 3
  · intro r h15 h8
    simp only [t, topA, execAll, regs_ldrSp_sl _ _ _ h1 _ h15, regs_ldrSp_sl _ _ _ h2 _ h15,
      regs_uxth _ _ _ _ h15, regs_lsr _ _ _ 16 (by decide) _ h15, regs_lsl _ _ _ 16 (by decide) _ h15,
      regs_muls _ _ _ _ h15, regs_movImm _ _ _ _ h15, regs_adds _ _ _ _ _ h15,
      regs_adcs _ _ _ _ h15, hi_ne r h8, ite_false]
  all_goals
    simp only [t, F, topA, execAll, State.reg]
    simp (config := {decide := true}) only [regs_ldrSp_sl _ _ _ h1, regs_ldrSp_sl _ _ _ h2,
      regs_uxth, regs_lsr _ _ _ 16 (by decide), regs_lsl _ _ _ 16 (by decide), regs_muls,
      regs_movImm, regs_adds, regs_adcs, c_adds, toReg_ne15, r13_ne, ne_eq, not_false_eq_true,
      State.reg, toReg_inj, ite_true, ite_false, mem_ldrSp, mem_uxth, mem_lsr, mem_movImm,
      State.sp, hi_ne 13 (by decide), t16]
  have hR : (BitVec.setWidth 32 (38 : BitVec 8)).toNat = 38 := by decide
  have hz : (BitVec.setWidth 32 (0 : BitVec 8)).toNat = 0 := by decide
  generalize fr s.mem (s.regs 13) (SP_ + 7) = L
  generalize fr s.mem (s.regs 13) (SH + 7) = W
  have elo := m38_lo _ W hR; have ehi := m38_hi _ W hR
  generalize BitVec.setWidth 32 (38 : BitVec 8) * BitVec.setWidth 32 (BitVec.setWidth 16 W) = A at elo ⊢
  generalize BitVec.setWidth 32 (38 : BitVec 8) * W >>> 16 = B at ehi ⊢
  generalize BitVec.setWidth 32 (0 : BitVec 8) = z at hz ⊢
  have b1 := hi16 B; have b2 := shl16 B
  generalize B >>> 16 = B1 at b1 ⊢; generalize B <<< 16 = B2 at b2 ⊢
  have e1 := adc_nat L A false
  generalize addWithCarry L A false = A1 at e1 ⊢
  have e2 := adc_nat A1.1 B2 false
  generalize addWithCarry A1.1 B2 false = A2 at e2 ⊢
  have e3 := adc_nat B1 z A1.2.1
  generalize addWithCarry B1 z A1.2.1 = A3 at e3 ⊢
  have e4 := adc_nat A3.1 z A2.2.1
  generalize addWithCarry A3.1 z A2.2.1 = A4 at e4 ⊢
  have := W.isLt; have := carry_le A3.1 z A2.2.1; have := A4.1.isLt; have := A3.1.isLt
  have := carry_le L A false; have := carry_le A1.1 B2 false; have := A1.1.isLt
  simp only [Bool.toNat_false, Nat.add_zero] at e1 e2
  omega

theorem topC_exec (s : State) (h4 : (s.reg 4).toNat < 2 ^ 20) :
    let t := execAll topC s
    (t.regs 12).toNat = (s.reg 5).toNat % 2 ^ 31 ∧
      (t.reg 4).toNat = 19 * (2 * (s.reg 4).toNat + (s.reg 5).toNat / 2 ^ 31) ∧
      t.reg 0 = fr s.mem s.sp SDST ∧ t.reg 7 = s.reg 7 ∧ t.reg 2 = s.reg 2 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 12 → t.regs r = s.regs r := by
  intro t
  have hm : t.mem = s.mem := execAll_mem _ _ (by simp [topC, Instr.writesMem])
  have hD : SDST < 256 := by decide
  have k1 : (1 : BitVec 5).toNat ≠ 0 := by decide
  have k31 : (31 : BitVec 5).toNat ≠ 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, hm, ?_⟩
  rotate_left 5
  · intro r h15 h8 h12
    simp only [t, topC, execAll, regs_ldrSp_sl _ _ _ hD _ h15, regs_lsr _ _ _ _ k1 _ h15,
      regs_lsr _ _ _ _ k31 _ h15, regs_lsl _ _ _ _ k1 _ h15, regs_muls _ _ _ _ h15,
      regs_movImm _ _ _ _ h15, regs_adds _ _ _ _ _ h15, regs_movHi _ _ _ _ h15, hi_ne r h8, h12,
      ite_false]
  all_goals
    simp only [t, topC, execAll, State.reg]
    simp (config := {decide := true}) only [regs_ldrSp_sl _ _ _ hD, regs_lsr _ _ _ _ k1,
      regs_lsr _ _ _ _ k31, regs_lsl _ _ _ _ k1, regs_muls, regs_movImm, regs_adds, regs_movHi,
      toReg_ne15, r13_ne, ne_eq, not_false_eq_true, State.reg, toReg_inj, ite_true, ite_false,
      mem_lsl, mem_lsr, mem_movImm, mem_addReg, mem_movHi, mem_dp, State.sp, hi_ne 13 (by decide),
      hi_ne 12 (by decide)]
  · have := (s.regs (LowReg.toReg 5)).isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 5).toNat = 1 from rfl]
    omega
  · simp only [State.reg] at h4
    generalize s.regs (LowReg.toReg 4) = a at h4 ⊢
    generalize s.regs (LowReg.toReg 5) = b
    have e := adc_nat (a <<< BitVec.toNat (1 : BitVec 5)) (b >>> BitVec.toNat (31 : BitVec 5)) false
    have := carry_le (a <<< BitVec.toNat (1 : BitVec 5)) (b >>> BitVec.toNat (31 : BitVec 5)) false
    generalize addWithCarry (a <<< BitVec.toNat (1 : BitVec 5))
      (b >>> BitVec.toNat (31 : BitVec 5)) false = A at e this ⊢
    have := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 5).toNat = 1 from rfl,
      show (31 : BitVec 5).toNat = 31 from rfl, Bool.toNat_false, Nat.add_zero] at e ⊢
    rw [BitVec.toNat_mul, show (BitVec.setWidth 32 (19 : BitVec 8)).toNat = 19 by decide]
    have := A.1.isLt
    omega

/-- The top word: `v = L7 + Y3 + 38 * H7` (`Y3` in `r12`) is `base7 + 2^31 * q`; `r12 := base7`,
`r4 := 19 * q`; `r7 = 38`, `r2 = 0`, `r0` is the output pointer from slot `SDST`. -/
theorem reduceTop_exec (s : State) :
    let t := execAll reduceTop s
    let F := fr s.mem s.sp
    ∃ q : Nat, (t.reg 4).toNat = 19 * q ∧
      (t.regs 12).toNat + 2 ^ 31 * q =
        (F (SP_ + 7)).toNat + (s.regs 12).toNat + 38 * (F (SH + 7)).toNat ∧
      (t.regs 12).toNat < 2 ^ 31 ∧ (t.reg 7).toNat = 38 ∧ (t.reg 2).toNat = 0 ∧
      t.reg 0 = F SDST ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 12 → t.regs r = s.regs r := by
  intro t F
  have et : t = execAll topC (execAll (wY 4 5 3 (some 12)) (execAll topA s)) := by
    simp only [t, reduceTop_split, execAll_append]
  obtain ⟨a1, a7, a2, am, ao⟩ := topA_exec s
  generalize execAll topA s = s1 at a1 a7 a2 am ao et
  have h12 : (12 : Reg) ≠ 15 := by decide
  have hy : ∀ r, (some (12 : Reg)) = some r → 8 ≤ r.val ∧ r ≠ 15 := by
    intro r h; cases h; decide
  have hW := (F (SH + 7)).isLt; have hL := (F (SP_ + 7)).isLt
  have := (s1.reg 5).isLt
  obtain ⟨d1, dm, dO⟩ := wY_exec s1 4 5 3 (some 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) hy a2 (by omega)
  generalize execAll (wY 4 5 3 (some 12)) s1 = s2 at d1 dm dO et
  have y12 : yval s1 (some 12) = (s.regs 12).toNat := by
    simp only [yval]; rw [ao 12 h12 (by decide)]
  rw [y12] at d1
  have hY := (s.regs 12).isLt; have := (s2.reg 5).isLt
  obtain ⟨c12, c4, c0, c7, c2, cm, cO⟩ := topC_exec s2 (by omega)
  rw [← et] at c12 c4 c0 c7 c2 cm cO
  have L := fun (x y : LowReg) (h : x ≠ y) => (mt (toReg_inj x y).mp h : x.toReg ≠ y.toReg)
  have s27 : s2.reg 7 = s1.reg 7 := dO _ (toReg_ne15 _) (L 7 4 (by decide)) (L 7 5 (by decide))
    (L 7 3 (by decide))
  have s22 : s2.reg 2 = s1.reg 2 := dO _ (toReg_ne15 _) (L 2 4 (by decide)) (L 2 5 (by decide))
    (L 2 3 (by decide))
  have hsp : s2.sp = s.sp := by
    simp only [State.sp]
    rw [dO 13 r13_ne (by rw [ne_eq, hi_ne 13 (by decide)]; trivial)
      (by rw [ne_eq, hi_ne 13 (by decide)]; trivial) (by rw [ne_eq, hi_ne 13 (by decide)]; trivial),
      ao 13 r13_ne (by decide)]
  refine ⟨2 * (s2.reg 4).toNat + (s2.reg 5).toNat / 2 ^ 31, c4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c12]; simp only [F] at a1 ⊢; omega
  · rw [c12]; omega
  · rw [c7, s27]; exact a7
  · rw [c2, s22]; exact a2
  · rw [c0, dm, am, hsp]
  · rw [cm, dm, am]
  · intro r h15 h8 h12'
    rw [cO r h15 h8 h12', dO r h15 (by rw [ne_eq, hi_ne r h8]; trivial)
      (by rw [ne_eq, hi_ne r h8]; trivial) (by rw [ne_eq, hi_ne r h8]; trivial), ao r h15 h8]

end M0Crypto.Release.X25519CR
