import M0Crypto.Release.Ed25519Comb
import M0Crypto.Release.Ed25519Wnaf
import M0Crypto.Release.Ed25519CombDigits
import M0Crypto.Release.Ed25519WnafDigits

/-!
The scalar multiplications from the code's digits: the integer recodings
(`Ed25519CombDigits`, `Ed25519WnafDigits`) meet the group loops (`Ed25519Comb`, `Ed25519Wnaf`).

* `combRecoding_digitAt`: the digits `digitAt n e q` of `m0c_sc_recode_comb` satisfy
  `CombRecoding`. Digit `q` of the group loop is comb `n − 1 − q % n` of round `q / n`, which is
  the integer side's `q = i n + (n − 1 − c)`; `combTerm` and `toothVal` agree on nonzero digits.
* `mulBase_digitAt`: the comb loop over those digits, then `B` subtracted for an even scalar,
  is `[e]B` for `e < 2^255` and any `n` dividing 64 (`compact` `n = 2`, `fast` `n = 16`).
* `wnafDigits_wnaf`: the digits `wnaf w k` of `m0c_sc_wnaf` satisfy `WnafDigits`.
* `dsmTop`: the top-digit scan of `m0c_ge_dsm`. `dsmRun_wnaf`: from it, the loop over the
  width-5 digits of `s` and the width-3 digits of `h` is `[s]B − [h]A` for `s, h < L`.
-/

namespace M0Crypto.Release.Ed25519ScalarMul

open Lean.Grind M0Crypto.Release.Ed25519Group M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519Comb (combSum combTerm combVal CombRecoding mulBase mulBase_eq)
open M0Crypto.Release.Ed25519CombDigits (ssum ssum_succ ssum_congr ssum_add ssum_mul ssum_split
  toothVal combEntry digitAt digitAt_bound comb_identity)
open M0Crypto.Release.Ed25519Wnaf (digitSum WnafDigits dsmRun dsm_eq)
open M0Crypto.Release.Ed25519WnafDigits (isum wnaf wnaf_spec)

/-! ## Signed comb -/

/-- `combSum` is an `ssum`. -/
theorem combSum_ssum (n : Nat) (δ : Nat → Int) (q : Nat) :
    combSum n δ q = ssum (fun q => 2 ^ (q / n) * combTerm n (n - 1 - q % n) (δ q)) q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [combSum, ih, ssum_succ]

/-- A sum read backwards. -/
theorem ssum_rev (g : Nat → Int) (N : Nat) : ssum (fun c => g (N - 1 - c)) N = ssum g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := ssum_add (fun c => g (N + 1 - 1 - c)) 1 N
    rw [Nat.add_comm 1 N] at h
    rw [h, show ssum (fun c => g (N + 1 - 1 - c)) 1 = g N by simp [ssum], ssum_succ g N, ← ih, Int.add_comm]
    congr 1
    exact ssum_congr fun j _ => by congr 1; omega

/-- The table value of a nonzero digit: the integer side's `toothVal` is the group side's
`combTerm` (both are entry `|d| − 1` of comb `c`, negated for `d < 0`). -/
theorem toothVal_eq (n c : Nat) {d : Int} (hd : d ≠ 0) :
    toothVal (64 / n) c d = combTerm n c d := by
  have hv : ∀ j, combEntry (64 / n) c j = combVal n c j := fun j => by
    simp only [combEntry, combVal, Ed25519Comb.spacing, Ed25519Comb.sgn, Int.add_assoc]
  unfold toothVal combTerm
  by_cases hp : 0 < d
  · rw [ite_eq_right (by omega), ite_eq_left hp, hv, show d.natAbs = d.toNat by omega]
  · rw [ite_eq_left (by omega), ite_eq_right hp, ite_eq_left (by omega), hv, show d.natAbs = (-d).toNat by omega]

/-- The digits of `m0c_sc_recode_comb` meet the group loop's premise. -/
theorem combRecoding_digitAt {n : Nat} (hn : 0 < n) (hd : n ∣ 64) {e : Nat} (he : e < 2 ^ 255) :
    CombRecoding n e (digitAt n e) := by
  refine ⟨fun q _ => digitAt_bound n e q, ?_⟩
  obtain ⟨m, hm⟩ := hd
  have hmn : 64 / n = m := by rw [hm, Nat.mul_div_cancel_left _ hn]
  rw [comb_identity hn ⟨m, hm⟩ e he, combSum_ssum, hmn, hm, ssum_split]
  apply ssum_congr
  intro i _
  rw [← ssum_rev, ← ssum_mul]
  apply ssum_congr
  intro c hc
  have h1 : (n - 1 - c + n * i) / n = i := by
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (by omega)]; omega
  have h2 : (n - 1 - c + n * i) % n = n - 1 - c := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, show n - 1 - (n - 1 - c) = c by omega, show n - 1 - c + n * i = i * n + (n - 1 - c) by
    rw [Nat.mul_comm]; omega, ← hmn, toothVal_eq n c (digitAt_bound n e _).1]

/-- `m0c_ge_mul_base` in the group, over the digits of `m0c_sc_recode_comb`: the comb loop and the
even-scalar correction give `[e]B`. -/
theorem mulBase_digitAt {n : Nat} (hn : 0 < n) (hd : n ∣ 64) {e : Nat} (he : e < 2 ^ 255) :
    mulBase n e (digitAt n e) = (e : Int) • Bpt :=
  mulBase_eq hn (combRecoding_digitAt hn hd he)

/-- `compact`: two combs. -/
theorem mulBase_digitAt_2 {e : Nat} (he : e < 2 ^ 255) : mulBase 2 e (digitAt 2 e) = (e : Int) • Bpt :=
  mulBase_digitAt (by decide) (by decide) he

/-- `fast`: sixteen combs. -/
theorem mulBase_digitAt_16 {e : Nat} (he : e < 2 ^ 255) :
    mulBase 16 e (digitAt 16 e) = (e : Int) • Bpt :=
  mulBase_digitAt (by decide) (by decide) he

/-! ## Windowed NAF -/

theorem digitSum_isum (d : Nat → Int) (k : Nat) : digitSum d k = isum d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [digitSum, ih, Ed25519WnafDigits.isum_succ, Int.mul_comm]

/-- The digits of `m0c_sc_wnaf` meet the group loop's premise. -/
theorem wnafDigits_wnaf {w k : Nat} (hw : 2 ≤ w) (hk : k < 2 ^ 255) : WnafDigits w k (wnaf w k) := by
  obtain ⟨hs, hd, -⟩ := wnaf_spec w k hw hk
  exact ⟨fun i _ => hd i, by rw [digitSum_isum, hs]⟩

/-- The top-digit scan of `m0c_ge_dsm` over the positions below `k`: one more than the highest
position with a nonzero digit of `s` or `h`, or `0` when there is none. The loop then runs
`dsmRun sd hd A (dsmTop sd hd 256) 0`. -/
def dsmTop (sd hd : Nat → Int) : Nat → Nat
  | 0 => 0
  | k + 1 => if hd k = 0 ∧ sd k = 0 then dsmTop sd hd k else k + 1

theorem dsmTop_spec (sd hd : Nat → Int) (k : Nat) :
    dsmTop sd hd k ≤ k ∧ ∀ i, dsmTop sd hd k ≤ i → i < k → sd i = 0 ∧ hd i = 0 := by
  induction k with
  | zero => exact ⟨Nat.le_refl _, fun i _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    unfold dsmTop
    split
    · rename_i h
      refine ⟨by omega, fun i h1 h2 => ?_⟩
      by_cases hi : i = k
      · subst hi; exact ⟨h.2, h.1⟩
      · exact ih.2 i h1 (by omega)
    · exact ⟨Nat.le_refl _, fun i h1 h2 => absurd h2 (by omega)⟩

/-- The double-scalar loop over windowed NAF digits of widths `ws`, `wh` from the top-digit scan
is `[s]B − [h]A`. -/
theorem dsmRun_wnaf_w (A : EdPt) {ws wh s h : Nat} (hws : 2 ≤ ws) (hwh : 2 ≤ wh)
    (hs : s < 2 ^ 255) (hh : h < 2 ^ 255) :
    dsmRun (wnaf ws s) (wnaf wh h) A (dsmTop (wnaf ws s) (wnaf wh h) 256) 0 =
      (s : Int) • Bpt - (h : Int) • A :=
  dsm_eq A (dsmTop_spec _ _ 256).1 (dsmTop_spec _ _ 256).2 (wnafDigits_wnaf hws hs).2
    (wnafDigits_wnaf hwh hh).2

theorem L_lt : Spec.Ed25519.L < 2 ^ 255 := by unfold Spec.Ed25519.L; omega

/-- `m0c_ge_dsm` as `m0c_ed25519_verify` calls it: width 5 for `s` (odd multiples of `B`),
width 3 for `h` (odd multiples of `−A`), `s, h < L`: `[s]B − [h]A`. -/
theorem dsmRun_wnaf (A : EdPt) {s h : Nat} (hs : s < Spec.Ed25519.L) (hh : h < Spec.Ed25519.L) :
    dsmRun (wnaf 5 s) (wnaf 3 h) A (dsmTop (wnaf 5 s) (wnaf 3 h) 256) 0 =
      (s : Int) • Bpt - (h : Int) • A :=
  dsmRun_wnaf_w A (by decide) (by decide) (Nat.lt_trans hs L_lt) (Nat.lt_trans hh L_lt)

end M0Crypto.Release.Ed25519ScalarMul
