import SafegcdRow.MatrixCode

namespace SafegcdRow.MatrixCode
open BitVec

set_option linter.unusedSimpArgs false

/-! The bit operations are verified without a native decision procedure.
The arithmetic refinement below can work on three public formulas for one iteration. -/

private theorem sign_mask (x : Word) :
    x.sshiftRight 31 = if x.msb then BitVec.allOnes 32 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hb : (if 31 + i < 32 then x.getLsbD (31 + i) else x.msb) = x.msb := by
    split
    · have e : i = 0 := by omega
      subst i
      exact (BitVec.msb_eq_getLsbD_last x).symm
    · rfl
  rw [hb]
  cases x.msb
  · simp [show ¬32 ≤ i by omega]
  · change (!decide (32 ≤ i) && true) = (BitVec.allOnes 32).getLsbD i
    rw [BitVec.getLsbD_allOnes]
    simp [hi]

private theorem odd_msb (g : Word) : (g <<< 31).msb = g.getLsbD 0 := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  rfl

private theorem conditional_negation (x : Word) :
    (x ^^^ BitVec.allOnes 32) - BitVec.allOnes 32 = -x := by
  rw [BitVec.xor_allOnes, BitVec.not_eq_neg_add, show BitVec.allOnes 32 = -1#32 from rfl]
  bv_omega

private theorem bit_double (x : Word) : x <<< 1 = 2#32 * x := by
  rw [BitVec.mul_comm]
  exact BitVec.shiftLeft_eq_mul_twoPow x 1

theorem advance_even (s : Words) (h : s.g.getLsbD 0 = false) :
    advance s = ⟨s.f, s.g.sshiftRight 1, s.delta + 2, 2*s.top, s.bot⟩ := by
  simp only [advance, sign_mask, odd_msb, h, Bool.false_eq_true, ite_false]
  simp [bit_double]

theorem advance_odd (s : Words) (h : s.g.getLsbD 0 = true) (hd : (-s.delta).msb = false) :
    advance s = ⟨s.f, (s.g+s.f).sshiftRight 1, s.delta + 2, 2*s.top, s.bot+s.top⟩ := by
  simp only [advance, sign_mask, odd_msb, h, hd, Bool.false_eq_true, ite_false, ite_true]
  have hm (x : Word) : x &&& 4294967295#32 = x := BitVec.and_allOnes
  simp [hm, bit_double]

theorem advance_swap (s : Words) (h : s.g.getLsbD 0 = true) (hd : (-s.delta).msb = true) :
    advance s = ⟨s.g, (s.g-s.f).sshiftRight 1, 2-s.delta, 2#32*s.bot, s.bot-s.top⟩ := by
  simp only [advance, sign_mask, odd_msb, h, hd, Bool.true_eq, ite_true,
    BitVec.and_allOnes, conditional_negation, bit_double, ← BitVec.sub_eq_add_neg]
  have hf : s.f + (s.g-s.f) = s.g := by bv_omega
  have hU : s.top + (s.bot-s.top) = s.bot := by bv_omega
  have hD : -s.delta + 2 = 2 - s.delta := by bv_omega
  rw [hf, hU, hD]

theorem lowSigned_eq (x : Word) : lowSigned x = (x.setWidth 16).signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [lowSigned, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases h : i < 16
  · simp [h, hi, BitVec.getLsbD_shiftLeft, show 16 + i < 32 by omega,
      show ¬16 + i < 16 by omega, show ¬32 ≤ i by omega]
  · simp [h, hi, BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last,
      show ¬16 + i < 32 by omega, show ¬32 ≤ i by omega]

end SafegcdRow.MatrixCode
