import SafegcdTermination.Vectors
import SafegcdTermination.MatrixRefine

namespace SafegcdTermination.CoreRows

open M0Crypto.Armv6M (State Mem)
open M0Crypto.Thumb
open SafegcdRow
open SafegcdTermination.FoldRefine (value vec)
open SafegcdTermination.Vectors (LowLimbs well_formed_of_range folded_low)

set_option linter.unusedSimpArgs false

theorem row_words (r : Row) (h : r.norm ≤ batchScale) :
    (BitVec.ofInt 32 r.a).toInt = r.a ∧ (BitVec.ofInt 32 r.b).toInt = r.b := by
  have ha : 0 ≤ magnitude (r.a) := magnitude_nonneg _
  have hb : 0 ≤ magnitude (r.b) := magnitude_nonneg _
  simp only [Row.norm, batchScale, batchSteps] at h
  have ha' := magnitude_le_iff.mp (show magnitude (r.a) ≤ 16384 by omega)
  have hb' := magnitude_le_iff.mp (show magnitude (r.b) ≤ 16384 by omega)
  refine ⟨int_of_word _ ⟨by omega, by omega⟩, int_of_word _ ⟨by omega, by omega⟩⟩

def rowInput (q : Input) (r : Row) : Int :=
  r.apply (value q.mem q.pins.x) (value q.mem q.pins.y)

theorem row_numerator (q : Input) (r : Row) (h : r.norm ≤ batchScale)
    (ha : q.pins.a = BitVec.ofInt 32 r.a) (hb : q.pins.b = BitVec.ofInt 32 r.b) :
    numerator q = rowInput q r := by
  obtain ⟨ha', hb'⟩ := row_words r h
  simp only [numerator, rowInput, ha, hb, ha', hb']
  rfl

theorem exact_correction_zero (r : Row) (x y z : Int)
    (he : r.apply x y = batchScale * z) : correction (r.apply x y) = 0 := by
  unfold correction
  rw [he, Int.mul_assoc, Int.mul_emod_right]

theorem row_args (q : Input) (r : Row) (h : r.norm ≤ batchScale)
    (ha : q.pins.a = BitVec.ofInt 32 r.a) (hb : q.pins.b = BitVec.ofInt 32 r.b)
    (hx : VecWellFormed (vec q.mem q.pins.x)) (hy : VecWellFormed (vec q.mem q.pins.y))
    (ht : (q.pins.t.toNat : Int) = correction (rowInput q r)) : Args q := by
  obtain ⟨ha', hb'⟩ := row_words r h
  refine ⟨hx, hy, ?_, ?_⟩
  · simp only [rowNorm, ha, hb, ha', hb']
    exact h
  · rw [row_numerator q r h ha hb]
    exact ht

theorem quotient_output (q : Input) (r : Row) (v : Int)
    (h : r.norm ≤ batchScale) (ha : q.pins.a = BitVec.ofInt 32 r.a) (hb : q.pins.b = BitVec.ofInt 32 r.b)
    (ht : (q.pins.t.toNat : Int) = correction (rowInput q r))
    (hv : divisor * v = numerator q + (q.pins.t.toNat : Int) * prime) :
    v = rowQuotient (rowInput q r) := by
  rw [row_numerator q r h ha hb, ht] at hv
  have hq := rowQuotient_exact (rowInput q r)
  change batchScale * v = rowInput q r + correction (rowInput q r) * p at hv
  have hs : batchScale = 16384 := by decide
  rw [hs] at hv hq
  omega

theorem exact_output (r : Row) (x y z : Int) (h : r.apply x y = batchScale * z) :
    rowQuotient (r.apply x y) = z := by
  have he := rowQuotient_exact (r.apply x y)
  rw [exact_correction_zero r x y z h, Int.zero_mul, Int.add_zero, h] at he
  rw [h]
  exact Int.eq_of_mul_eq_mul_left (by decide : batchScale ≠ 0) he

theorem prepare_correction_word (a b x y : Word) (r : Row) (X Y : Int)
    (ha : a = BitVec.ofInt 32 r.a) (hb : b = BitVec.ofInt 32 r.b)
    (hx : (x.toNat : Int) ≡ X [ZMOD batchScale]) (hy : (y.toNat : Int) ≡ Y [ZMOD batchScale]) :
    ((((a*x+b*y)*2587#32) <<< 18) >>> 18).toNat = (correction (r.apply X Y)).toNat := by
  have hx' : BitVec.ofInt 32 (x.toNat : Int) = x := by simp
  have hy' : BitVec.ofInt 32 (y.toNat : Int) = y := by simp
  have hi : (((a*x+b*y)*2587#32) <<< 18) >>> 18 =
      ((BitVec.ofInt 32 ((r.apply (x.toNat : Int) (y.toNat : Int)) * 2587)) <<< 18) >>> 18 := by
    simp only [Row.apply, ha, hb, BitVec.ofInt_mul, BitVec.ofInt_add]
    rw [show BitVec.ofInt 32 (x.toNat : Int) = x from hx', show BitVec.ofInt 32 (y.toNat : Int) = y from hy']
    rfl
  rw [hi]
  have h := (((hx.mul_left r.a).add (hy.mul_left r.b)).mul_right 2587)
  have hcong : correction (r.apply (x.toNat : Int) (y.toNat : Int)) = correction (r.apply X Y) := h
  rw [← hcong]
  simp only [correction, batchScale, batchSteps, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofInt, Nat.shiftLeft_eq, Nat.reducePow]
  omega

end SafegcdTermination.CoreRows
