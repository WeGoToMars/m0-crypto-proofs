import M0Crypto.Release.Ed25519Order

/-!
The signed comb of `m0c_ge_mul_base` in the group, for `n` combs of four teeth spaced
`s = 64 / n` bits apart (`n = 2` in `compact`, `16` in `fast`).

* `combVal n c j`: the multiple of `B` in entry `j < 8` of comb `c`, as the flash table
  `m0c_ed_comb` must hold it (`CombTable`), in Niels form.
* `lookupNiels`: what `m0c_ge_lookup` selects for a digit `δ` with `|δ| ≤ 8`: entry `δ − 1`,
  the negated entry `−δ − 1`, or `(1, 1, 0)`; `lookup_eq` gives the multiple `combTerm n c δ`.
* `combRun`: the loop, one iteration per digit index `q = 63, …, 0`: add the point of digit `q`
  (comb `n − 1 − q % n`), then double when `q` closes a round other than the last
  (`q % n = 0`, `q ≠ 0`). `combRun_eq` evaluates any tail of it, for a loop invariant.
* `mulBase_eq`: with the integer recoding identity `CombRecoding` (the integer side, lane 7b),
  the loop followed by the constant-time subtraction of `B` for an even scalar gives `[e]B`.
-/

namespace M0Crypto.Release.Ed25519Comb

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge

/-- The spacing `64 / n` of the teeth. -/
def spacing (n : Nat) : Nat := 64 / n

/-- `2 b − 1` for a bit `b`: `+1` or `−1`. -/
def sgn (b : Nat) : Int := 2 * (b : Int) - 1

/-- Entry `j < 8` of comb `c`: `2^(s(4c+3)) + Σ_{k<3} (2 j_k − 1) 2^(s(4c+k))`, `s = 64 / n`,
with `j_k` bit `k` of `j`. -/
def combVal (n c j : Nat) : Int :=
  let s := spacing n
  2 ^ (s * (4 * c + 3)) + sgn (j % 2) * 2 ^ (s * (4 * c)) + sgn (j / 2 % 2) * 2 ^ (s * (4 * c + 1))
    + sgn (j / 4 % 2) * 2 ^ (s * (4 * c + 2))

/-- The comb table `m0c_ed_comb` (entry `j` of comb `c` in Niels form) holds `[combVal n c j]B`.
Phase 3 checks this by evaluation (`Ed25519Order.mulExt` evaluates the multiples). -/
def CombTable (n : Nat) (entry : Nat → Nat → Niels Fp) : Prop :=
  ∀ c < n, ∀ j < 8, entry c j = Niels.of d2 ((combVal n c j) • Bpt).pt

/-- The table `m0c_ed_odd_b` (entry `k` in Niels form) holds `[2k + 1]B`. Entry `0` is the `B`
that `m0c_ge_mul_base` subtracts for an even scalar. -/
def OddBTable (entry : Nat → Niels Fp) : Prop :=
  ∀ k < 8, entry k = Niels.of d2 ((2 * (k : Int) + 1) • Bpt).pt

/-- The multiple of `B` that digit `δ` selects from comb `c`. -/
def combTerm (n c : Nat) (δ : Int) : Int :=
  if 0 < δ then combVal n c (δ.toNat - 1)
  else if δ < 0 then -combVal n c ((-δ).toNat - 1) else 0

/-- The output of `m0c_ge_lookup` for the row `row` (eight Niels entries) and the digit `δ`. -/
def lookupNiels (row : Nat → Niels Fp) (δ : Int) : Niels Fp :=
  if 0 < δ then row (δ.toNat - 1)
  else if δ < 0 then (row ((-δ).toNat - 1)).neg else ⟨1, 1, 0⟩

theorem lookup_eq {n c : Nat} {entry : Nat → Nat → Niels Fp} (ht : CombTable n entry)
    (hc : c < n) {δ : Int} (h1 : -8 ≤ δ) (h2 : δ ≤ 8) :
    lookupNiels (entry c) δ = Niels.of d2 ((combTerm n c δ) • Bpt).pt := by
  unfold lookupNiels combTerm
  by_cases hp : 0 < δ
  · simp only [hp, ↓reduceIte]
    exact ht c hc _ (by omega)
  · by_cases hm : δ < 0
    · simp only [hp, hm, ↓reduceIte]
      rw [ht c hc _ (by omega), IntModule.neg_zsmul]
      exact (Niels.of_neg d2 _).symm
    · simp only [hp, hm, ↓reduceIte]
      rw [IntModule.zero_zsmul]
      exact (Niels.of_zero d2).symm

/-- The point added at digit index `q`: digit `δ q` of comb `n − 1 − q % n`. -/
def combPt (n : Nat) (δ : Nat → Int) (q : Nat) : EdPt := combTerm n (n - 1 - q % n) (δ q) • Bpt

/-- Iteration `q` of the comb loop: add the point of digit `q`, then double when `q` closes a
round other than the last. -/
def combStep (n : Nat) (δ : Nat → Int) (H : EdPt) (q : Nat) : EdPt :=
  if q % n = 0 ∧ q ≠ 0 then (H + combPt n δ q) + (H + combPt n δ q) else H + combPt n δ q

/-- The iterations `q − 1, …, 0` from the state `H`. The loop of `m0c_ge_mul_base` is
`combRun n δ 64 0`. -/
def combRun (n : Nat) (δ : Nat → Int) : Nat → EdPt → EdPt
  | 0, H => H
  | q + 1, H => combRun n δ q (combStep n δ H q)

/-- `Σ_{q' < q} 2^(q' / n) · combTerm n (n − 1 − q' % n) (δ q')`. -/
def combSum (n : Nat) (δ : Nat → Int) : Nat → Int
  | 0 => 0
  | q + 1 => combSum n δ q + 2 ^ (q / n) * combTerm n (n - 1 - q % n) (δ q)

/-- The integer side (lane 7b): the digits `δ q` (the bytes of `m0c_sc_recode_comb` minus 8)
are nonzero, at most 8 in absolute value, and their comb-weighted sum is the odd scalar
`2 ⌊e / 2⌋ + 1`. -/
def CombRecoding (n e : Nat) (δ : Nat → Int) : Prop :=
  (∀ q < 64, δ q ≠ 0 ∧ -8 ≤ δ q ∧ δ q ≤ 8) ∧ combSum n δ 64 = 2 * ((e / 2 : Nat) : Int) + 1

/-- The number of doublings: `(q − 1) / n` doublings follow the additions at the indices
below `q`, and iteration `q` doubles exactly when it raises it. -/
theorem div_step {n : Nat} (hn : 0 < n) (q : Nat) :
    (if q % n = 0 ∧ q ≠ 0 then (q - 1) / n + 1 else (q - 1) / n) = q / n := by
  have hd := Nat.div_add_mod q n
  have hm := Nat.mod_lt q hn
  split
  · rename_i h
    have hq : 1 ≤ q / n := by
      rcases Nat.eq_zero_or_pos (q / n) with h0 | h0
      · rw [h0, h.1] at hd; omega
      · exact h0
    have : (q - 1) / n = q / n - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm, Nat.mul_sub_one]; rw [h.1] at hd; omega
      · rw [Nat.sub_add_cancel hq, Nat.mul_comm]; omega
    omega
  · rename_i h
    by_cases hq0 : q = 0
    · subst hq0; simp
    · have h1 : q % n ≠ 0 := fun e => h ⟨e, hq0⟩
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm]; omega
      · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega

theorem zsmul_double (w : Int) (Y : EdPt) : w • (Y + Y) = (w * 2) • Y := by
  rw [IntModule.zsmul_add, show w * 2 = w + w by omega, IntModule.add_zsmul]

/-- Any tail of the loop: from `H` before iteration `q − 1`, the loop ends at
`[2^((q − 1) / n)] H + [combSum n δ q] B`. -/
theorem combRun_eq {n : Nat} (hn : 0 < n) (δ : Nat → Int) (q : Nat) (H : EdPt) :
    combRun n δ q H = ((2 ^ ((q - 1) / n) : Nat) : Int) • H + combSum n δ q • Bpt := by
  induction q generalizing H with
  | zero =>
    rw [combRun, combSum, Nat.zero_sub, Nat.zero_div, Nat.pow_zero, IntModule.zero_zsmul,
      AddCommMonoid.add_zero, Int.natCast_one, IntModule.one_zsmul]
  | succ q ih =>
    rw [combRun, ih, combSum, Nat.add_sub_cancel, IntModule.add_zsmul, combStep, combPt]
    have e := div_step hn q
    have hw : (2 : Int) ^ (q / n) = ((2 ^ (q / n) : Nat) : Int) := by rw [Int.natCast_pow]; rfl
    rw [hw]
    generalize combTerm n (n - 1 - q % n) (δ q) = t
    generalize combSum n δ q • Bpt = c
    by_cases h : q % n = 0 ∧ q ≠ 0
    · rw [ite_eq_left h] at e
      rw [ite_eq_left h, zsmul_double, IntModule.zsmul_add, ← IntModule.mul_zsmul, ← e, Nat.pow_succ,
        Int.natCast_mul]
      generalize ((2 ^ ((q - 1) / n) : Nat) : Int) * ((2 : Nat) : Int) = w
      generalize w • H = a
      generalize (w * t) • Bpt = b
      grind
    · rw [ite_eq_right h] at e
      rw [ite_eq_right h, IntModule.zsmul_add, ← IntModule.mul_zsmul, ← e]
      generalize ((2 ^ ((q - 1) / n) : Nat) : Int) = w
      generalize w • H = a
      generalize (w * t) • Bpt = b
      grind

/-- The comb loop from the identity is `[combSum n δ 64] B`. -/
theorem combRun_zero {n : Nat} (hn : 0 < n) (δ : Nat → Int) :
    combRun n δ 64 0 = combSum n δ 64 • Bpt := by
  rw [combRun_eq hn, IntModule.zsmul_zero, AddCommMonoid.zero_add]

/-- `m0c_ge_mul_base` in the group: the comb loop, then `B` subtracted when `e` is even. -/
def mulBase (n e : Nat) (δ : Nat → Int) : EdPt :=
  combRun n δ 64 0 - (if e % 2 = 0 then Bpt else 0)

/-- The signed comb computes `[e]B`. -/
theorem mulBase_eq {n e : Nat} (hn : 0 < n) {δ : Nat → Int} (h : CombRecoding n e δ) :
    mulBase n e δ = (e : Int) • Bpt := by
  rw [mulBase, combRun_zero hn, h.2]
  have he := Nat.div_add_mod e 2
  by_cases h0 : e % 2 = 0
  · simp only [h0, ↓reduceIte]
    rw [IntModule.add_zsmul, IntModule.one_zsmul, show (e : Int) = 2 * ((e / 2 : Nat) : Int) by omega]
    generalize (2 * ((e / 2 : Nat) : Int)) • Bpt = a
    grind
  · simp only [h0, ↓reduceIte]
    rw [show 2 * ((e / 2 : Nat) : Int) + 1 = (e : Int) by omega]
    grind

end M0Crypto.Release.Ed25519Comb
