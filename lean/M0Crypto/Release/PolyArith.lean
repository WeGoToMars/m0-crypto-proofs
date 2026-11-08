import M0Crypto.Spec.AEAD

/-!
Arithmetic core of `m0c_poly1305_blocks`, over `Nat`, independent of the machine model.

One block of the code, in radix 2^32 with a 5-limb accumulator `h` (top limb small),
clamped `r = r0 + 2^32 r1 + 2^64 r2 + 2^96 r3` and `s_j = r_j + r_j / 4`:

* `h + m + pad 2^128` (exact: the top limb stays small);
* column sums `d0..d3` built by 64-bit additions (each MAC is exact mod 2^64; the
  bounds below show no sum reaches 2^64), carried from one column to the next;
* `g = hi(d3) + h4 r0`, then `g = 4 (g / 4) + g % 4` is folded as
  `2^130 (g / 4) = 5 (g / 4) mod p`.

`block_arith` states, with every intermediate value exactly as the code computes it
(each `% 2^32` / `% 2^64` is a register width), that the result is congruent to
`(h + m + pad 2^128) r` modulo `p = 2^130 - 5` and has top limb at most 4.
The multiplication identity is proved by `grind`'s commutative-ring normaliser.
-/

namespace M0Crypto.Release.PolyArith

open M0Crypto.Spec.AEAD (p)

/-- Value of five 32-bit limbs. -/
def val5 (h0 h1 h2 h3 h4 : Nat) : Nat := h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4

/-- Value of four 32-bit limbs. -/
def val4 (a0 a1 a2 a3 : Nat) : Nat := a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3

theorem p_eq : p = 2 ^ 130 - 5 := rfl

/-- Product in limbs with `r_j = 4 q_j` (j ≥ 1): the wrapped columns are multiples of
`2^130 = p + 5`. -/
theorem mul_fold (h0 h1 h2 h3 h4 r0 q1 q2 q3 : Nat) :
    val5 h0 h1 h2 h3 h4 * val4 r0 (4 * q1) (4 * q2) (4 * q3) +
      5 * (h1 * q3 + h2 * q2 + h3 * q1 + (h2 * q3 + h3 * q2 + h4 * q1) * 2 ^ 32 +
        (h3 * q3 + h4 * q2) * 2 ^ 64 + h4 * q3 * 2 ^ 96) =
    (h0 * r0 + h1 * (5 * q3) + h2 * (5 * q2) + h3 * (5 * q1)) +
      2 ^ 32 * (h0 * (4 * q1) + h1 * r0 + h2 * (5 * q3) + h3 * (5 * q2) + h4 * (5 * q1)) +
      2 ^ 64 * (h0 * (4 * q2) + h1 * (4 * q1) + h2 * r0 + h3 * (5 * q3) + h4 * (5 * q2)) +
      2 ^ 96 * (h0 * (4 * q3) + h1 * (4 * q2) + h2 * (4 * q1) + h3 * r0 + h4 * (5 * q3)) +
      2 ^ 128 * (h4 * r0) +
      2 ^ 130 * (h1 * q3 + h2 * q2 + h3 * q1 + (h2 * q3 + h3 * q2 + h4 * q1) * 2 ^ 32 +
        (h3 * q3 + h4 * q2) * 2 ^ 64 + h4 * q3 * 2 ^ 96) := by
  simp only [val5, val4]
  grind

theorem mul_le {a b A B : Nat} (ha : a ≤ A) (hb : b ≤ B) : a * b ≤ A * B := Nat.mul_le_mul ha hb

/-- The linear part of one block: column sums are exact, the carry chain and the fold
of `g` give `HR = o + p (K + g / 4)`. All products are atoms here. -/
theorem carry_fold (P00 P10 P20 P30 P40 P01 P02 P03 P11 P12 P21 S13 S22 S31 S23 S32 S33 S41 S42 S43
    e0 e1 e2 e3 g c o K HR : Nat)
    (b00 : P00 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1)) (b10 : P10 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1))
    (b20 : P20 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1)) (b30 : P30 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1))
    (b40 : P40 ≤ 6 * (2 ^ 28 - 1))
    (b01 : P01 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1)) (b02 : P02 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1))
    (b03 : P03 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1)) (b11 : P11 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1))
    (b12 : P12 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1)) (b21 : P21 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1))
    (c13 : S13 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26)) (c22 : S22 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26))
    (c31 : S31 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26)) (c23 : S23 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26))
    (c32 : S32 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26)) (c33 : S33 ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26))
    (c41 : S41 ≤ 6 * (5 * 2 ^ 26)) (c42 : S42 ≤ 6 * (5 * 2 ^ 26)) (c43 : S43 ≤ 6 * (5 * 2 ^ 26))
    (he0 : e0 = ((((0 + P00) % 2 ^ 64 + S13) % 2 ^ 64 + S22) % 2 ^ 64 + S31) % 2 ^ 64)
    (he1 : e1 = (((((e0 / 2 ^ 32 + P01) % 2 ^ 64 + P10) % 2 ^ 64 + S23) % 2 ^ 64 + S32)
      % 2 ^ 64 + S41 % 2 ^ 32) % 2 ^ 64)
    (he2 : e2 = (((((e1 / 2 ^ 32 + P02) % 2 ^ 64 + P11) % 2 ^ 64 + P20) % 2 ^ 64 + S33)
      % 2 ^ 64 + S42 % 2 ^ 32) % 2 ^ 64)
    (he3 : e3 = (((((e2 / 2 ^ 32 + P03) % 2 ^ 64 + P12) % 2 ^ 64 + P21) % 2 ^ 64 + P30)
      % 2 ^ 64 + S43 % 2 ^ 32) % 2 ^ 64)
    (hg : g = (e3 / 2 ^ 32 + P40 % 2 ^ 32) % 2 ^ 32)
    (hc : c = (g / 4 + (g - g % 4)) % 2 ^ 32)
    (ho : o = (e0 % 2 ^ 32 + 2 ^ 32 * (e1 % 2 ^ 32) + 2 ^ 64 * (e2 % 2 ^ 32) + 2 ^ 96 * (e3 % 2 ^ 32)
      + 2 ^ 128 * (g % 4) + c) % 2 ^ 160)
    (hid : HR + 5 * K = (P00 + S13 + S22 + S31) + 2 ^ 32 * (P01 + P10 + S23 + S32 + S41) +
      2 ^ 64 * (P02 + P11 + P20 + S33 + S42) + 2 ^ 96 * (P03 + P12 + P21 + P30 + S43) +
      2 ^ 128 * P40 + 2 ^ 130 * K) :
    HR = o + p * (K + g / 4) ∧ o < 5 * 2 ^ 128 := by
  have x0 : e0 = P00 + S13 + S22 + S31 := by clear hid ho hc hg he1 he2 he3; omega
  have x1 : e1 = e0 / 2 ^ 32 + P01 + P10 + S23 + S32 + S41 := by
    clear hid ho hc hg he0 he2 he3; subst x0; omega
  have x2 : e2 = e1 / 2 ^ 32 + P02 + P11 + P20 + S33 + S42 := by
    clear hid ho hc hg he0 he1 he3; subst x1 x0; omega
  have x3 : e3 = e2 / 2 ^ 32 + P03 + P12 + P21 + P30 + S43 := by
    clear hid ho hc hg he0 he1 he2; subst x2 x1 x0; omega
  have xg : g = e3 / 2 ^ 32 + P40 := by
    clear hid ho hc he0 he1 he2 he3; subst x3 x2 x1 x0; omega
  have xc : c = 5 * (g / 4) := by
    clear hid ho he0 he1 he2 he3 hg; subst xg x3 x2 x1 x0; omega
  have xo : o = e0 % 2 ^ 32 + 2 ^ 32 * (e1 % 2 ^ 32) + 2 ^ 64 * (e2 % 2 ^ 32) + 2 ^ 96 * (e3 % 2 ^ 32)
      + 2 ^ 128 * (g % 4) + c := by
    clear hid he0 he1 he2 he3 hg hc; subst xc xg x3 x2 x1 x0; omega
  clear he0 he1 he2 he3 hg hc ho
  rw [p_eq]
  omega

/-- **One block.** Hypotheses name every value the code computes, at register width:
`H` the accumulator after adding the message, `e0..e3` the four column sums,
`g` the new top limb before folding, `c` the fold term `5 (g / 4)`, `o` the result. -/
theorem block_arith (h0 h1 h2 h3 h4 m0 m1 m2 m3 pad r0 r1 r2 r3 s1 s2 s3 : Nat)
    (H0 H1 H2 H3 H4 e0 e1 e2 e3 g c o : Nat)
    (hh : h0 < 2 ^ 32 ∧ h1 < 2 ^ 32 ∧ h2 < 2 ^ 32 ∧ h3 < 2 ^ 32 ∧ h4 ≤ 4)
    (hm : m0 < 2 ^ 32 ∧ m1 < 2 ^ 32 ∧ m2 < 2 ^ 32 ∧ m3 < 2 ^ 32) (hpad : pad ≤ 1)
    (hr : r0 < 2 ^ 28 ∧ r1 < 2 ^ 28 ∧ r2 < 2 ^ 28 ∧ r3 < 2 ^ 28)
    (hr4 : r1 % 4 = 0 ∧ r2 % 4 = 0 ∧ r3 % 4 = 0)
    (hs : s1 = r1 + r1 / 4 ∧ s2 = r2 + r2 / 4 ∧ s3 = r3 + r3 / 4)
    (hH : H0 < 2 ^ 32 ∧ H1 < 2 ^ 32 ∧ H2 < 2 ^ 32 ∧ H3 < 2 ^ 32 ∧ H4 < 2 ^ 32)
    (hadd : val5 H0 H1 H2 H3 H4 = (val5 h0 h1 h2 h3 h4 + val4 m0 m1 m2 m3 + 2 ^ 128 * pad) % 2 ^ 160)
    (he0 : e0 = ((((0 + H0 * r0) % 2 ^ 64 + H1 * s3) % 2 ^ 64 + H2 * s2) % 2 ^ 64 + H3 * s1) % 2 ^ 64)
    (he1 : e1 = (((((e0 / 2 ^ 32 + H0 * r1) % 2 ^ 64 + H1 * r0) % 2 ^ 64 + H2 * s3) % 2 ^ 64 + H3 * s2)
      % 2 ^ 64 + H4 * s1 % 2 ^ 32) % 2 ^ 64)
    (he2 : e2 = (((((e1 / 2 ^ 32 + H0 * r2) % 2 ^ 64 + H1 * r1) % 2 ^ 64 + H2 * r0) % 2 ^ 64 + H3 * s3)
      % 2 ^ 64 + H4 * s2 % 2 ^ 32) % 2 ^ 64)
    (he3 : e3 = (((((e2 / 2 ^ 32 + H0 * r3) % 2 ^ 64 + H1 * r2) % 2 ^ 64 + H2 * r1) % 2 ^ 64 + H3 * r0)
      % 2 ^ 64 + H4 * s3 % 2 ^ 32) % 2 ^ 64)
    (hg : g = (e3 / 2 ^ 32 + H4 * r0 % 2 ^ 32) % 2 ^ 32)
    (hc : c = (g / 4 + (g - g % 4)) % 2 ^ 32)
    (ho : o = (val4 (e0 % 2 ^ 32) (e1 % 2 ^ 32) (e2 % 2 ^ 32) (e3 % 2 ^ 32) + 2 ^ 128 * (g % 4) + c)
      % 2 ^ 160) :
    o % p = ((val5 h0 h1 h2 h3 h4 + val4 m0 m1 m2 m3 + 2 ^ 128 * pad) * val4 r0 r1 r2 r3) % p ∧
      o < 5 * 2 ^ 128 := by
  obtain ⟨hh0, hh1, hh2, hh3, hh4⟩ := hh
  obtain ⟨hm0, hm1, hm2, hm3⟩ := hm
  obtain ⟨hr0, hr1, hr2, hr3⟩ := hr
  obtain ⟨hH0, hH1, hH2, hH3, hH4⟩ := hH
  obtain ⟨q1, rfl⟩ : ∃ q, r1 = 4 * q := ⟨r1 / 4, by omega⟩
  obtain ⟨q2, rfl⟩ : ∃ q, r2 = 4 * q := ⟨r2 / 4, by omega⟩
  obtain ⟨q3, rfl⟩ : ∃ q, r3 = 4 * q := ⟨r3 / 4, by omega⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have e1' : s1 = 5 * q1 := by omega
  have e2' : s2 = 5 * q2 := by omega
  have e3' : s3 = 5 * q3 := by omega
  subst e1' e2' e3'
  -- the accumulator after the message: exact, top limb at most 6
  have hval : val5 H0 H1 H2 H3 H4 = val5 h0 h1 h2 h3 h4 + val4 m0 m1 m2 m3 + 2 ^ 128 * pad := by
    simp only [val5, val4] at hadd ⊢; omega
  have hH4' : H4 ≤ 6 := by simp only [val5, val4] at hval; omega
  -- product bounds
  have bR : ∀ x, x < 2 ^ 32 → ∀ y, y < 2 ^ 28 → x * y ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1) :=
    fun x hx y hy => mul_le (by omega) (by omega)
  have bS : ∀ x, x < 2 ^ 32 → ∀ q, 4 * q < 2 ^ 28 → x * (5 * q) ≤ (2 ^ 32 - 1) * (5 * 2 ^ 26) :=
    fun x hx q hq => mul_le (by omega) (by omega)
  have bS4 : ∀ q, 4 * q < 2 ^ 28 → H4 * (5 * q) ≤ 6 * (5 * 2 ^ 26) := fun q hq => mul_le hH4' (by omega)
  have bR4 : H4 * r0 ≤ 6 * (2 ^ 28 - 1) := mul_le hH4' (by omega)
  have b00 := bR H0 hH0 r0 hr0; have b10 := bR H1 hH1 r0 hr0
  have b20 := bR H2 hH2 r0 hr0; have b30 := bR H3 hH3 r0 hr0
  have b01 := bR H0 hH0 _ hr1; have b02 := bR H0 hH0 _ hr2; have b03 := bR H0 hH0 _ hr3
  have b11 := bR H1 hH1 _ hr1; have b12 := bR H1 hH1 _ hr2; have b21 := bR H2 hH2 _ hr1
  have c13 := bS H1 hH1 q3 hr3; have c22 := bS H2 hH2 q2 hr2; have c31 := bS H3 hH3 q1 hr1
  have c23 := bS H2 hH2 q3 hr3; have c32 := bS H3 hH3 q2 hr2; have c33 := bS H3 hH3 q3 hr3
  have c41 := bS4 q1 hr1; have c42 := bS4 q2 hr2; have c43 := bS4 q3 hr3
  -- the reduction identity, instantiated
  have hid := mul_fold H0 H1 H2 H3 H4 r0 q1 q2 q3
  rw [hval] at hid
  -- name every product; from here on everything is linear
  generalize H0 * r0 = P00 at *; generalize H1 * r0 = P10 at *; generalize H2 * r0 = P20 at *
  generalize H3 * r0 = P30 at *; generalize H4 * r0 = P40 at *
  generalize H0 * (4 * q1) = P01 at *; generalize H0 * (4 * q2) = P02 at *
  generalize H0 * (4 * q3) = P03 at *; generalize H1 * (4 * q1) = P11 at *
  generalize H1 * (4 * q2) = P12 at *; generalize H2 * (4 * q1) = P21 at *
  generalize H1 * (5 * q3) = S13 at *; generalize H2 * (5 * q2) = S22 at *
  generalize H3 * (5 * q1) = S31 at *; generalize H2 * (5 * q3) = S23 at *
  generalize H3 * (5 * q2) = S32 at *; generalize H3 * (5 * q3) = S33 at *
  generalize H4 * (5 * q1) = S41 at *; generalize H4 * (5 * q2) = S42 at *
  generalize H4 * (5 * q3) = S43 at *
  generalize (H1 * q3 + H2 * q2 + H3 * q1 + (H2 * q3 + H3 * q2 + H4 * q1) * 2 ^ 32 +
    (H3 * q3 + H4 * q2) * 2 ^ 64 + H4 * q3 * 2 ^ 96) = K at hid
  generalize (val5 h0 h1 h2 h3 h4 + val4 m0 m1 m2 m3 + 2 ^ 128 * pad) * val4 r0 (4 * q1) (4 * q2) (4 * q3) = HR at *
  obtain ⟨key, hlt⟩ := carry_fold P00 P10 P20 P30 P40 P01 P02 P03 P11 P12 P21 S13 S22 S31 S23 S32 S33
    S41 S42 S43 e0 e1 e2 e3 g c o K HR b00 b10 b20 b30 bR4 b01 b02 b03 b11 b12 b21 c13 c22 c31 c23 c32
    c33 c41 c42 c43 he0 he1 he2 he3 hg hc (by simp only [val4] at ho; exact ho) hid
  exact ⟨by rw [key, Nat.add_mul_mod_self_left], hlt⟩

end M0Crypto.Release.PolyArith
