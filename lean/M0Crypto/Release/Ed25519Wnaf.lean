import M0Crypto.Release.Ed25519Order

/-!
The double-scalar multiplication of `m0c_ge_dsm` in the group: `[s]B − [h]A` from the
right-to-left windowed NAF digits of `s` (width 5, odd multiples of `B` from the flash table
`m0c_ed_odd_b`) and of `h` (width 3, odd multiples of `−A` on the stack).

* `dsmStep`: one position `i`: double, then add `[h_i](−A)` if `h_i ≠ 0`, then `[s_i]B` if
  `s_i ≠ 0`.
* `dsmRun k R`: the positions `k − 1, …, 0` from `R`. The code starts from the identity at the
  highest position `I` with a nonzero digit (the top-digit scan), that is `dsmRun (I + 1) 0`,
  or runs no iteration when every digit is zero (`k = 0`).
* `dsmRun_eq`: any tail, for a loop invariant. `dsm_eq`: the whole loop is `[s]B − [h]A`, given
  the digit sums (the integer side, lane 7b) and that the digits from `k` on are zero.
* `oddEntry_eq`: an odd digit `δ` selects entry `|δ| / 2`, the multiple `2 (|δ| / 2) + 1`, and
  negates it when `δ < 0`; this is `[δ]`.
-/

namespace M0Crypto.Release.Ed25519Wnaf

open Lean.Grind M0Crypto.Release.Ed25519Group M0Crypto.Release.Ed25519Bridge

/-- `Σ_{i < k} 2^i d_i`. -/
def digitSum (d : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => digitSum d k + 2 ^ k * d k

/-- The integer side (lane 7b): the 256 digits of `m0c_sc_wnaf` with width `w` are zero or odd
with `|d_i| < 2^(w − 1)`, and `Σ_{i < 256} 2^i d_i = x`. -/
def WnafDigits (w x : Nat) (d : Nat → Int) : Prop :=
  (∀ i < 256, d i = 0 ∨ (d i % 2 = 1 ∧ -2 ^ (w - 1) < d i ∧ d i < 2 ^ (w - 1))) ∧
    digitSum d 256 = x

/-- Position `i` of the loop of `m0c_ge_dsm`. -/
def dsmStep (sd hd : Nat → Int) (A R : EdPt) (i : Nat) : EdPt :=
  let R := R + R
  let R := if hd i = 0 then R else R + hd i • (-A)
  if sd i = 0 then R else R + sd i • Bpt

/-- The positions `k − 1, …, 0` from `R`. -/
def dsmRun (sd hd : Nat → Int) (A : EdPt) : Nat → EdPt → EdPt
  | 0, R => R
  | k + 1, R => dsmRun sd hd A k (dsmStep sd hd A R k)

theorem dsmStep_eq (sd hd : Nat → Int) (A R : EdPt) (i : Nat) :
    dsmStep sd hd A R i = (R + R) + hd i • (-A) + sd i • Bpt := by
  unfold dsmStep
  have z (d : Int) (X Y : EdPt) : (if d = 0 then Y else Y + d • X) = Y + d • X := by
    split
    · rename_i h; rw [h, IntModule.zero_zsmul, AddCommMonoid.add_zero]
    · rfl
  simp only [z]

/-- Any tail of the loop. -/
theorem dsmRun_eq (sd hd : Nat → Int) (A : EdPt) (k : Nat) (R : EdPt) :
    dsmRun sd hd A k R = ((2 ^ k : Nat) : Int) • R + digitSum sd k • Bpt - digitSum hd k • A := by
  induction k generalizing R with
  | zero =>
    rw [dsmRun, digitSum, digitSum, Nat.pow_zero, Int.natCast_one, IntModule.one_zsmul,
      IntModule.zero_zsmul, IntModule.zero_zsmul, AddCommMonoid.add_zero, AddCommGroup.sub_eq_add_neg,
      AddCommGroup.neg_zero, AddCommMonoid.add_zero]
  | succ k ih =>
    rw [dsmRun, ih, dsmStep_eq, digitSum, digitSum, IntModule.add_zsmul, IntModule.add_zsmul,
      IntModule.mul_zsmul, IntModule.mul_zsmul, IntModule.zsmul_neg, Nat.pow_succ, Int.natCast_mul,
      IntModule.mul_zsmul, IntModule.zsmul_add, IntModule.zsmul_add, IntModule.zsmul_add,
      IntModule.zsmul_neg, show ((2 : Nat) : Int) = 1 + 1 from rfl, IntModule.add_zsmul,
      IntModule.one_zsmul]
    have hw : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by rw [Int.natCast_pow]; rfl
    rw [hw]
    generalize ((2 ^ k : Nat) : Int) = w
    rw [IntModule.zsmul_add w R R]
    generalize w • R = a
    generalize w • (sd k • Bpt) = b
    generalize w • (hd k • A) = c
    generalize digitSum sd k • Bpt = e
    generalize digitSum hd k • A = f
    grind

/-- Digits from `k` on are zero, so the sum over `k` positions is the sum over 256. -/
theorem digitSum_top {d : Nat → Int} {k : Nat} (hk : k ≤ 256)
    (htop : ∀ i, k ≤ i → i < 256 → d i = 0) : digitSum d k = digitSum d 256 := by
  suffices ∀ j, k + j ≤ 256 → digitSum d k = digitSum d (k + j) by
    have := this (256 - k) (by omega)
    rwa [Nat.add_sub_cancel' hk] at this
  intro j
  induction j with
  | zero => intro; rfl
  | succ j ih =>
    intro hj
    rw [← Nat.add_assoc, digitSum, htop (k + j) (by omega) (by omega), Int.mul_zero, Int.add_zero]
    exact ih (by omega)

/-- `m0c_ge_dsm` from the top-digit scan: `[s]B − [h]A`. `k` is one more than the highest
position with a nonzero digit, or `0`. -/
theorem dsm_eq {sd hd : Nat → Int} {s h k : Nat} (A : EdPt) (hk : k ≤ 256)
    (htop : ∀ i, k ≤ i → i < 256 → sd i = 0 ∧ hd i = 0)
    (hs : digitSum sd 256 = s) (hh : digitSum hd 256 = h) :
    dsmRun sd hd A k 0 = (s : Int) • Bpt - (h : Int) • A := by
  rw [dsmRun_eq, IntModule.zsmul_zero, AddCommMonoid.zero_add,
    digitSum_top hk (fun i h1 h2 => (htop i h1 h2).1),
    digitSum_top hk (fun i h1 h2 => (htop i h1 h2).2), hs, hh]

/-- An odd digit `δ` selects the entry `|δ| / 2`, which holds `[2 (|δ| / 2) + 1] P`, and
negates it when `δ < 0` (the sign bit): the result is `[δ] P`. -/
theorem oddEntry_eq {δ : Int} (hodd : δ % 2 = 1) (P : EdPt) :
    (if δ < 0 then -(((2 * (δ.natAbs / 2) + 1 : Nat) : Int) • P)
      else ((2 * (δ.natAbs / 2) + 1 : Nat) : Int) • P) = δ • P := by
  have e : ((2 * (δ.natAbs / 2) + 1 : Nat) : Int) = (δ.natAbs : Int) := by omega
  rw [e]
  split
  · rw [← IntModule.neg_zsmul]; congr 1; omega
  · congr 1; omega

end M0Crypto.Release.Ed25519Wnaf
