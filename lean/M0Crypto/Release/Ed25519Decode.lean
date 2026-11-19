import M0Crypto.Release.Ed25519Bridge

/-!
Decoding (`m0c_ge_decompress`) against RFC 8032 section 5.1.3 (`Spec.Ed25519.decodePoint`).

`decodeCode y sign` is the routine's computation over `F_p`, in the generator's order: `y` is the
encoded integer without bit 255 and `sign` is bit 255. It rejects `y ≥ p`; forms
`u = y² − 1`, `v = y² d + 1` and the candidate `x = (v³ v³ v u)^((p − 5)/8) v³ u`; keeps `x` when
`v x² = u`, takes `x · sqrt(−1)` when `v x² = −u`, rejects otherwise (`root`); rejects `x = 0`
with the sign bit set, and negates `x` when its parity differs from the sign (`finish`).

* `decodePoint_eq`: the specification's decoding, mapped into `F_p`, is `decodeCode`.
* `decodeCode_eq_some_iff`: `decodeCode` returns `(x, y, 1, x y)` exactly when `(x, y)` is on
  the curve and `x mod 2` is the sign. So it rejects exactly when no point of the curve has
  that `y` and that sign (`decodeCode_eq_none_iff`); in particular it rejects when no point has
  that `y`.
* `root_of_square`: the `(p − 5)/8` power gives a root of `v x² = ± u` whenever `u / v` is a
  square, which is why the two checks of `root` find every point.
-/

namespace M0Crypto.Release.Ed25519Decode

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519Edwards (Point OnCurve)
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519PrimeCert (p)

/-- Step 3 of section 5.1.3: `x` is the candidate root and `vxx = v x²`. -/
def root (x vxx u : Fp) : Option Fp :=
  if vxx = u then some x else if vxx = 0 - u then some (x * sqrtM1) else none

/-- Step 4: reject `x = 0` with the sign bit set; negate `x` when its parity is not the sign. -/
def finish (x Y : Fp) (sign : Nat) : Option (Ext Fp) :=
  if x = 0 ∧ sign ≠ 0 then none else
    let x := if x.val % 2 = sign then x else 0 - x
    some ⟨x, Y, 1, x * Y⟩

/-- `m0c_ge_decompress` over `F_p`: `y` is the integer without bit 255, `sign` is bit 255. -/
def decodeCode (y sign : Nat) : Option (Ext Fp) :=
  if p ≤ y then none else
    let Y := toF y
    let yy := Y * Y
    let u := yy - 1
    let v := yy * d + 1
    let v3 := v * v * v
    let t := (v3 * v3 * v * u) ^ ((p - 5) / 8)
    let x := t * v3 * u
    (root x (x * x * v) u).bind fun x => finish x Y sign

/-- The routine's test `y + 19 ≥ 2^255` for `y ≥ p`, on a 255-bit `y`. -/
theorem ge_p_iff {y : Nat} (hy : y < 2 ^ 255) : p ≤ y ↔ 2 ^ 255 ≤ y + 19 := by
  unfold p; omega

/-! ## Equality with the specification -/

theorem val_toF_of_lt {a : Nat} (h : a < p) : (toF a).val = a := by
  rw [val_toF, Nat.mod_eq_of_lt h]

/-- A reduced value equals `a % p` exactly when the field elements agree. -/
theorem mod_eq_iff {a b : Nat} (hb : b < p) : a % p = b ↔ toF a = toF b := by
  rw [toF_eq_iff]; show a % p = b ↔ a % p = b % p; rw [Nat.mod_eq_of_lt hb]

theorem fsub_lt (a b : Nat) : Spec.Ed25519.fsub a b < p := Nat.mod_lt _ (by decide)

theorem toF_sub_left {a : Nat} (h : a ≤ p) : toF (p - a) = 0 - toF a := by
  apply Fp.ext
  rw [Fp.val_sub, val_toF, val_toF, Fp.val_zero, Nat.add_zero]
  rcases Nat.eq_or_lt_of_le h with e | h'
  · subst e; simp
  · rw [Nat.mod_eq_of_lt h']

theorem ofSpec_ofXY (a y : Nat) :
    ofSpec (Spec.Ed25519.Point.ofXY a y) = ⟨toF a, toF y, 1, toF a * toF y⟩ := by
  simp only [ofSpec, Spec.Ed25519.Point.ofXY, toF_mod, toF_mul, toF_one]

/-- Step 4 of the specification, mapped into `F_p`, is `finish`. -/
theorem finish_eq {xs y sg : Nat} (hx : xs < p) (hsg : sg < 2) :
    (if xs = 0 ∧ sg = 1 then none
      else if sg ≠ xs % 2 then some (Spec.Ed25519.Point.ofXY (p - xs) y)
      else some (Spec.Ed25519.Point.ofXY xs y)).map ofSpec = finish (toF xs) (toF y) sg := by
  have hv := val_toF_of_lt hx
  have h0 : toF xs = 0 ↔ xs = 0 := by
    constructor
    · intro e; rw [← hv, e]; rfl
    · intro e; subst e; rfl
  unfold finish
  by_cases hz : xs = 0 ∧ sg = 1
  · have hz' : toF xs = 0 ∧ sg ≠ 0 := ⟨h0.2 hz.1, by omega⟩
    rw [ite_eq_left hz, ite_eq_left hz']; rfl
  · have hz' : ¬(toF xs = 0 ∧ sg ≠ 0) := fun h => hz ⟨h0.1 h.1, by omega⟩
    rw [ite_eq_right hz, ite_eq_right hz', hv]
    by_cases hs : sg = xs % 2
    · have h1 : ¬(sg ≠ xs % 2) := fun h => h hs
      have h2 : xs % 2 = sg := hs.symm
      rw [ite_eq_right h1, ite_eq_left h2, Option.map_some, ofSpec_ofXY]
    · have h2 : ¬(xs % 2 = sg) := fun h => hs h.symm
      rw [ite_eq_left hs, ite_eq_right h2, Option.map_some, ofSpec_ofXY,
        toF_sub_left (Nat.le_of_lt hx)]

/-- The decoding of the specification, mapped into `F_p`, is the routine's. -/
theorem decodePoint_eq (s : List Spec.Ed25519.Byte) :
    (Spec.Ed25519.decodePoint s).map ofSpec =
      decodeCode (Spec.Ed25519.decodeInt s % 2 ^ 255) (Spec.Ed25519.decodeInt s / 2 ^ 255 % 2) := by
  unfold Spec.Ed25519.decodePoint decodeCode
  simp only []
  generalize Spec.Ed25519.decodeInt s = n
  have hsg : n / 2 ^ 255 % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize n / 2 ^ 255 % 2 = sg at hsg ⊢
  generalize n % 2 ^ 255 = y
  by_cases hy : p ≤ y
  · have hy' : y ≥ Spec.Ed25519.p := hy
    rw [ite_eq_left hy', ite_eq_left hy]; rfl
  have hy' : ¬(y ≥ Spec.Ed25519.p) := hy
  rw [ite_eq_right hy', ite_eq_right hy]
  -- The specification's values and their images in `F_p`.
  generalize hU : Spec.Ed25519.fsub (y ^ 2) 1 = U
  generalize hV : (Spec.Ed25519.d * y ^ 2 + 1) % Spec.Ed25519.p = V
  have fU : toF U = toF y * toF y - 1 := by
    rw [← hU, toF_fsub, toF_pow, toF_one, Semiring.pow_two]
  have fV : toF V = toF y * toF y * d + 1 := by
    rw [← hV, toF_mod, toF_add, toF_mul, toF_pow, toF_one, toF_d, Semiring.pow_two]; grind
  have hUlt : U < p := hU ▸ fsub_lt _ _
  generalize hX : U * V ^ 3 * Spec.Ed25519.powp (U * V ^ 7) ((Spec.Ed25519.p - 5) / 8)
    % Spec.Ed25519.p = X
  have hXlt : X < p := hX ▸ Nat.mod_lt _ (by decide)
  generalize toF y * toF y * d + 1 = v at fV
  generalize toF y * toF y - 1 = u at fU
  have fX : toF X = (v * v * v * (v * v * v) * v * u) ^ ((p - 5) / 8) * (v * v * v) * u := by
    rw [← hX, toF_mod, toF_mul, toF_mul, toF_powp, toF_mul, toF_pow, toF_pow, fU, fV]
    have e : u * v ^ 7 = v * v * v * (v * v * v) * v * u := by grind
    rw [e, p_eq]; grind
  generalize (v * v * v * (v * v * v) * v * u) ^ ((p - 5) / 8) * (v * v * v) * u = x at fX
  have c1 : V * X ^ 2 % Spec.Ed25519.p = U ↔ x * x * v = u := by
    rw [p_eq, mod_eq_iff hUlt, toF_mul, toF_pow, fX, fV, fU]
    constructor <;> intro e <;> grind
  have c2 : V * X ^ 2 % Spec.Ed25519.p = Spec.Ed25519.fsub 0 U ↔ x * x * v = 0 - u := by
    rw [p_eq, mod_eq_iff (fsub_lt _ _), toF_mul, toF_pow, fX, fV, toF_fsub, toF_zero, fU]
    constructor <;> intro e <;> grind
  have hX2lt : X * Spec.Ed25519.powp 2 ((Spec.Ed25519.p - 1) / 4) % Spec.Ed25519.p < p :=
    Nat.mod_lt _ (by decide)
  have fX2 : toF (X * Spec.Ed25519.powp 2 ((Spec.Ed25519.p - 1) / 4) % Spec.Ed25519.p)
      = x * sqrtM1 := by
    rw [toF_mod, toF_mul, toF_powp, fX, toF_two]; rfl
  unfold root
  by_cases h1 : x * x * v = u
  · rw [ite_eq_left (c1.2 h1), ite_eq_left h1, Option.bind_some, ← fX]
    exact finish_eq hXlt hsg
  · rw [ite_eq_right (fun h => h1 (c1.1 h)), ite_eq_right h1]
    by_cases h2 : x * x * v = 0 - u
    · rw [ite_eq_left (c2.2 h2), ite_eq_left h2, Option.bind_some, ← fX2]
      exact finish_eq hX2lt hsg
    · rw [ite_eq_right (fun h => h2 (c2.1 h)), ite_eq_right h2]; rfl

/-! ## Mathematics of the square root -/

/-- `w² = 1` gives `w = ±1`. -/
theorem sq_eq_one {w : Fp} (h : w * w = 1) : w = 1 ∨ w = -1 := by
  have e : (w - 1) * (w + 1) = 0 := by grind
  rcases Field.of_mul_eq_zero e with e | e
  · left; grind
  · right; grind

theorem v_ne_zero (Y : Fp) : Y * Y * d + 1 ≠ 0 := by
  intro h
  have hY : Y ≠ 0 := by intro e; rw [e] at h; grind
  apply d_nonsq (sqrtM1 / Y)
  have := sqrtM1_sq
  grind

/-- `(x, y)` is on the curve exactly when `v x² = u`. -/
theorem onCurve_iff (X Y : Fp) :
    OnEd25519 ⟨X, Y⟩ ↔ X * X * (Y * Y * d + 1) = Y * Y - 1 := by
  show (-1) * X ^ 2 + Y ^ 2 = 1 + d * X ^ 2 * Y ^ 2 ↔ _
  constructor <;> intro h <;> grind

/-- The candidate of step 2 squares to `± u / v` when some `X` has `v X² = u`. -/
theorem root_of_square {u v X x : Fp} (hv : v ≠ 0) (hX : X * X * v = u)
    (hx : x = (v * v * v * (v * v * v) * v * u) ^ ((p - 5) / 8) * (v * v * v) * u) :
    x * x * v = u ∨ x * x * v = 0 - u := by
  by_cases hu : u = 0
  · left
    rw [hx, hu]; grind
  have hX0 : X ≠ 0 := by intro e; apply hu; rw [← hX, e]; grind
  -- `u v^7 = W²` with `W = X v⁴`, and `v x² = u (u v^7)^((p − 1)/4) = u W^((p − 1)/2)`.
  generalize ht : (v * v * v * (v * v * v) * v * u) ^ ((p - 5) / 8) = t at hx
  have hz : v * v * v * (v * v * v) * v * u = (X * (v * v * v * v)) ^ 2 := by
    rw [← hX]; grind
  have hW : X * (v * v * v * v) ≠ 0 :=
    Ed25519Edwards.mul_ne_zero hX0
      (Ed25519Edwards.mul_ne_zero (Ed25519Edwards.mul_ne_zero (Ed25519Edwards.mul_ne_zero hv hv) hv) hv)
  generalize X * (v * v * v * v) = W at hz hW
  have hxx : x * x * v = u * (t * t * W ^ 2) := by
    rw [← hz, hx]; grind
  have htt : t * t * W ^ 2 = W ^ ((p - 1) / 2) := by
    rw [← ht, hz, ← pow_mul, ← Semiring.pow_add, ← Semiring.pow_add]
    congr 1
  have hw : W ^ ((p - 1) / 2) * W ^ ((p - 1) / 2) = 1 := by
    rw [← Semiring.pow_add, show (p - 1) / 2 + (p - 1) / 2 = p - 1 by decide]
    exact pow_p_sub_one hW
  rw [hxx, htt]
  rcases sq_eq_one hw with e | e
  · left; rw [e]; grind
  · right; rw [e]; grind

theorem neg_val_mod_two {x : Fp} (hx : x ≠ 0) : (0 - x).val % 2 ≠ x.val % 2 := by
  rw [Fp.val_sub, Fp.val_zero, Nat.add_zero]
  have hl := x.val_lt
  have h0 : x.val ≠ 0 := fun e => hx (Fp.ext (by rw [e]; rfl))
  rw [Nat.mod_eq_of_lt (show p - x.val < p by omega)]
  have hp : p % 2 = 1 := by decide
  omega

/-- What `finish` returns: the root with the sign's parity, when it exists. -/
theorem finish_eq_some_iff {x Y : Fp} {sign : Nat} (hs : sign < 2) {E : Ext Fp} :
    finish x Y sign = some E ↔
      ∃ X : Fp, (X = x ∨ X = 0 - x) ∧ X.val % 2 = sign ∧ E = ⟨X, Y, 1, X * Y⟩ := by
  unfold finish
  by_cases hz : x = 0 ∧ sign ≠ 0
  · rw [ite_eq_left hz]
    simp only [reduceCtorEq, false_iff, _root_.not_exists, _root_.not_and]
    intro X hX hXs
    have : X = 0 := by rcases hX with e | e <;> rw [e, hz.1] <;> grind
    rw [this, Fp.val_zero] at hXs; have := hz.2; omega
  · rw [ite_eq_right hz]
    simp only [Option.some.injEq]
    by_cases hp : x.val % 2 = sign
    · rw [ite_eq_left hp]
      constructor
      · intro e; exact ⟨x, Or.inl rfl, hp, e.symm⟩
      · rintro ⟨X, hX | hX, hXs, rfl⟩
        · rw [hX]
        · subst hX
          by_cases hx0 : x = 0
          · rw [hx0]; congr 1 <;> grind
          · exact absurd (hXs.trans hp.symm) (neg_val_mod_two hx0)
    · rw [ite_eq_right hp]
      have hx0 : x ≠ 0 := by
        intro e; apply hz; refine ⟨e, ?_⟩; intro hs0; apply hp; rw [e, hs0]; rfl
      have hn : (0 - x).val % 2 = sign := by
        have := neg_val_mod_two hx0; omega
      constructor
      · intro e; exact ⟨0 - x, Or.inr rfl, hn, e.symm⟩
      · rintro ⟨X, hX | hX, hXs, rfl⟩
        · exact absurd (hX ▸ hXs) hp
        · rw [hX]

/-- Two roots of `v X² = u`, `v ≠ 0`, agree up to sign. -/
theorem sq_eq_sq {X x v : Fp} (hv : v ≠ 0) (h : X * X * v = x * x * v) : X = x ∨ X = 0 - x := by
  have e : (X - x) * (X + x) = 0 := by
    have : (X * X - x * x) * v = 0 := by grind
    rcases Field.of_mul_eq_zero this with e | e
    · grind
    · exact absurd e hv
  rcases Field.of_mul_eq_zero e with e | e
  · left; grind
  · right; grind

/-- `decodeCode` returns `(x, y, 1, x y)` exactly when `(x, y)` is a point of the curve whose
`x mod 2` is the sign bit. -/
theorem decodeCode_eq_some_iff {y sign : Nat} (hy : y < p) (hs : sign < 2) {E : Ext Fp} :
    decodeCode y sign = some E ↔
      ∃ X : Fp, OnEd25519 ⟨X, toF y⟩ ∧ X.val % 2 = sign ∧ E = ⟨X, toF y, 1, X * toF y⟩ := by
  unfold decodeCode
  rw [ite_eq_right (Nat.not_le.2 hy)]
  simp only []
  generalize toF y = Y
  have hv := v_ne_zero Y
  simp only [onCurve_iff]
  generalize Y * Y * d + 1 = v at hv ⊢
  generalize Y * Y - 1 = u
  have hrs := fun X hX => @root_of_square u v X _ hv hX rfl
  generalize (v * v * v * (v * v * v) * v * u) ^ ((p - 5) / 8) * (v * v * v) * u = x at hrs
  unfold root
  -- The root that `root` keeps satisfies `v r² = u`.
  have hsq : x * sqrtM1 * (x * sqrtM1) * v = x * x * v * (sqrtM1 * sqrtM1) := by grind
  rw [sqrtM1_sq] at hsq
  by_cases h1 : x * x * v = u
  · rw [ite_eq_left h1, Option.bind_some, finish_eq_some_iff hs]
    constructor
    · rintro ⟨X, hX, hXs, rfl⟩
      refine ⟨X, ?_, hXs, rfl⟩
      rcases hX with rfl | rfl
      · exact h1
      · rw [← h1]; grind
    · rintro ⟨X, hX, hXs, rfl⟩
      exact ⟨X, sq_eq_sq hv (hX.trans h1.symm), hXs, rfl⟩
  · rw [ite_eq_right h1]
    by_cases h2 : x * x * v = 0 - u
    · rw [ite_eq_left h2, Option.bind_some, finish_eq_some_iff hs]
      have hr : x * sqrtM1 * (x * sqrtM1) * v = u := by rw [hsq, h2]; grind
      constructor
      · rintro ⟨X, hX, hXs, rfl⟩
        refine ⟨X, ?_, hXs, rfl⟩
        rcases hX with rfl | rfl
        · exact hr
        · rw [← hr]; grind
      · rintro ⟨X, hX, hXs, rfl⟩
        exact ⟨X, sq_eq_sq hv (hX.trans hr.symm), hXs, rfl⟩
    · rw [ite_eq_right h2, Option.bind_none]
      simp only [reduceCtorEq, false_iff, _root_.not_exists, _root_.not_and]
      intro X hX
      rcases hrs X hX with e | e
      · exact absurd e h1
      · exact absurd e h2

/-- `decodeCode` rejects a `y < p` exactly when no point of the curve has that `y` and an `x`
whose parity is the sign bit. -/
theorem decodeCode_eq_none_iff {y sign : Nat} (hy : y < p) (hs : sign < 2) :
    decodeCode y sign = none ↔ ¬∃ X : Fp, OnEd25519 ⟨X, toF y⟩ ∧ X.val % 2 = sign := by
  constructor
  · rintro hn ⟨X, hX, hXs⟩
    have := (decodeCode_eq_some_iff hy hs).2 ⟨X, hX, hXs, rfl⟩
    rw [hn] at this; exact absurd this (by simp)
  · intro hne
    cases e : decodeCode y sign with
    | none => rfl
    | some E =>
      obtain ⟨X, hX, hXs, -⟩ := (decodeCode_eq_some_iff hy hs).1 e
      exact absurd ⟨X, hX, hXs⟩ hne

/-- A rejection of `y < p` with the sign bit clear means no point of the curve has that `y`. -/
theorem no_point_of_reject {y : Nat} (hy : y < p) (h : decodeCode y 0 = none) :
    ∀ X : Fp, ¬OnEd25519 ⟨X, toF y⟩ := by
  intro X hX
  have hne := (decodeCode_eq_none_iff hy (by decide)).1 h
  by_cases h0 : X.val % 2 = 0
  · exact hne ⟨X, hX, h0⟩
  · have hX0 : X ≠ 0 := by intro e; apply h0; rw [e]; rfl
    apply hne ⟨0 - X, ?_, by have := neg_val_mod_two hX0; omega⟩
    rw [onCurve_iff] at hX ⊢; rw [← hX]; grind

/-- A successful decoding represents its point. -/
theorem rep_of_decode {y sign : Nat} (hy : y < p) (hs : sign < 2) {E : Ext Fp}
    (h : decodeCode y sign = some E) :
    ∃ A : EdPt, Rep E A ∧ A.pt = ⟨E.X, E.Y⟩ ∧ E.Z = 1 := by
  obtain ⟨X, hX, -, rfl⟩ := (decodeCode_eq_some_iff hy hs).1 h
  exact ⟨⟨_, hX⟩, rep_ofPoint ⟨_, hX⟩, rfl, rfl⟩

end M0Crypto.Release.Ed25519Decode
