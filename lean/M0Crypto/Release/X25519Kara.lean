/-!
Subtractive Karatsuba with explicit sign.

The field routines compute every product of two `2k`-bit numbers from three `k`-bit products:
`a * b = lo + W * mid + W^2 * hi` with `W = 2^k`, `lo = a0 * b0`, `hi = a1 * b1`, and the
middle term `mid = a0 * b1 + a1 * b0` obtained from `lo + hi` and `|u0 - u1| * |v0 - v1|`,
added or subtracted according to the two borrow bits. The same three lemmas serve the 64-,
128- and 256-bit levels (macros `mul64`, `mul128` / `combine128`, `fe_mul` /
`combine_reduce`), and the squaring variants (`sqr64`, `sqr128`, `fe_sqr`), where both
differences are the same and the product is always subtracted:

* `absdiff`: subtract with borrow `b`, complement by the mask, subtract the mask: `|x - y|`.
* `cross`: the middle term from `lo + hi` and the product of the two absolute differences.
* `negacc`: adding the complement of `m`, one carry in and `z`, modulo `W`, is `z - m`.
* `kara_split`: `a * b = lo + W * mid + W^2 * hi`.
* `chain3`, `mul64_tail_nat`: the three-word accumulation that ends macro `mul64`.

All arguments are `Nat` (word values); `W` is any modulus, in practice `2^32`, `2^64` and so
on. No machine term appears here.
-/

namespace M0Crypto.Release.X25519Kara

/-- `d = x - y mod W` with borrow `b` (`subs`/`sbcs`), `e` the complement of `d` when
`b = 1` (`eors` with the mask), `r = e - mask mod W` (`subs`/`sbcs` of the mask, borrow
`b'`): `r = |x - y|`, signed by `b`. -/
theorem absdiff (W x y d b e r b' : Nat) (hy : y < W) (hd : d < W) (hr : r < W)
    (hb : b ≤ 1) (hb' : b' ≤ 1)
    (hsub : d + y = x + W * b)
    (he : e = if b = 1 then W - 1 - d else d)
    (hfix : r + b * (W - 1) = e + W * b') :
    (x : Int) - y = if b = 1 then -(r : Int) else r := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb' with rfl | rfl <;>
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hsub hfix <;>
  simp at he <;> subst he <;> simp <;> omega

/-- The middle term. `x = |u0 - u1|` with sign bit `bu`, `y = |v0 - v1|` with sign bit `bv`.
`u0 * v0 + u1 * v1` and `u0 * v1 + u1 * v0` differ by `x * y`, on the side given by the
signs. -/
theorem cross (u0 u1 v0 v1 x y bu bv : Nat)
    (hx : (u0 : Int) - u1 = if bu = 1 then -(x : Int) else x)
    (hy : (v0 : Int) - v1 = if bv = 1 then -(y : Int) else y)
    (hbu : bu ≤ 1) (hbv : bv ≤ 1) :
    u0 * v0 + u1 * v1 + (if bu = bv then 0 else x * y) =
      u0 * v1 + u1 * v0 + (if bu = bv then x * y else 0) := by
  have key : ((u0 : Int) - u1) * ((v0 : Int) - v1) =
      (u0 * v0 + u1 * v1 : Int) - (u0 * v1 + u1 * v0 : Int) := by grind
  apply Int.ofNat_inj.mp
  push_cast
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbu with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbv with rfl | rfl <;>
  simp only [Nat.zero_ne_one, Nat.one_ne_zero, ↓reduceIte, Int.natCast_zero, Int.natCast_mul]
    at hx hy ⊢ <;>
  rw [hx, hy] at key <;> grind

/-- The squaring case of `cross`: one difference, always subtracted. -/
theorem cross_sq (u0 u1 x b : Nat) (hx : (u0 : Int) - u1 = if b = 1 then -(x : Int) else x)
    (hb : b ≤ 1) :
    u0 * u0 + u1 * u1 = u0 * u1 + u1 * u0 + x * x := by
  have h := cross u0 u1 u0 u1 x x b b hx hx hb hb
  simpa using h

/-- Two's complement accumulation modulo `W`: `r` is the sum of the complement of `m`
(`W - 1 - m`) when `neg`, the carry in `1` when `neg`, and `z`. If `t` is `z - m` (when
`neg`) or `z + m`, and below `W`, then `r = t`. -/
theorem negacc (W m z t r c : Nat) (neg : Bool) (hm : m < W) (hr : r < W) (ht : t < W)
    (hsum : r + W * c = (if neg then W - 1 - m else m) + (if neg then 1 else 0) + z)
    (hval : if neg then t + m = z else t = z + m) : r = t := by
  have hW : 0 < W := by omega
  have hr' : r = (r + W * c) % W := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsum hval
    rw [hr', hsum, Nat.add_comm m z, ← hval, Nat.mod_eq_of_lt ht]
  · simp only [↓reduceIte] at hsum hval
    have : W - 1 - m + 1 + z = t + W * 1 := by omega
    rw [hr', hsum, this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-- The product from the three parts. -/
theorem kara_split (W a0 a1 b0 b1 : Nat) :
    (a0 + W * a1) * (b0 + W * b1) = a0 * b0 + W * (a0 * b1 + a1 * b0) + W * W * (a1 * b1) := by
  grind

/-- Three-word addition with carry in, from its three carry equations. -/
theorem w3_lt {a b c : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) :
    a + 2 ^ 32 * b + 2 ^ 64 * c < 2 ^ 96 := by omega

theorem chain3 (x0 x1 x2 y0 y1 y2 cin r0 r1 r2 c0 c1 c2 : Nat)
    (e0 : r0 + 2 ^ 32 * c0 = x0 + y0 + cin) (e1 : r1 + 2 ^ 32 * c1 = x1 + y1 + c0)
    (e2 : r2 + 2 ^ 32 * c2 = x2 + y2 + c1) :
    r0 + 2 ^ 32 * r1 + 2 ^ 64 * r2 + 2 ^ 96 * c2 =
      (x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2) + (y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2) + cin := by
  omega

/-- The tail of macro `mul64`: the conditionally complemented middle product, `L` and `H`
accumulated over three words, then added at word 1. The result is the 128-bit product. -/
theorem mul64_tail_nat (A0 A1 B0 B1 L0 L1 H0 H1 p0 p1 : Nat) (neg : Bool)
    (t1a k1 t2a k2 t3a k3 t1b j1 t2b j2 t3b j3 f1 g1 f2 g2 f3 g3 : Nat)
    (hA0 : A0 < 2 ^ 32) (hA1 : A1 < 2 ^ 32) (hB0 : B0 < 2 ^ 32) (hB1 : B1 < 2 ^ 32)
    (hL : L0 + 2 ^ 32 * L1 = A0 * B0) (hH : H0 + 2 ^ 32 * H1 = A1 * B1)
    (hp0 : p0 < 2 ^ 32) (hp1 : p1 < 2 ^ 32)
    (hmid : if neg then A0 * B1 + A1 * B0 + (p0 + 2 ^ 32 * p1) = A0 * B0 + A1 * B1
      else A0 * B1 + A1 * B0 = A0 * B0 + A1 * B1 + (p0 + 2 ^ 32 * p1))
    (e1 : t1a + 2 ^ 32 * k1 = (if neg then 2 ^ 32 - 1 - p0 else p0) + L0 + (if neg then 1 else 0))
    (e2 : t2a + 2 ^ 32 * k2 = (if neg then 2 ^ 32 - 1 - p1 else p1) + L1 + k1)
    (e3 : t3a + 2 ^ 32 * k3 = (if neg then 2 ^ 32 - 1 else 0) + 0 + k2)
    (e4 : t1b + 2 ^ 32 * j1 = t1a + H0 + 0)
    (e5 : t2b + 2 ^ 32 * j2 = t2a + H1 + j1)
    (e6 : t3b + 2 ^ 32 * j3 = t3a + 0 + j2)
    (e7 : f1 + 2 ^ 32 * g1 = L1 + t1b + 0)
    (e8 : f2 + 2 ^ 32 * g2 = H0 + t2b + g1)
    (e9 : f3 + 2 ^ 32 * g3 = H1 + t3b + g2)
    (l4 : t1b < 2 ^ 32) (l5 : t2b < 2 ^ 32) (l6 : t3b < 2 ^ 32) (l7 : f1 < 2 ^ 32)
    (l8 : f2 < 2 ^ 32) (l9 : f3 < 2 ^ 32) (hL0 : L0 < 2 ^ 32) :
    L0 + 2 ^ 32 * f1 + 2 ^ 64 * f2 + 2 ^ 96 * f3 = (A0 + 2 ^ 32 * A1) * (B0 + 2 ^ 32 * B1) := by
  have ca := chain3 _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3
  have cb := chain3 _ _ _ _ _ _ _ _ _ _ _ _ _ e4 e5 e6
  have cc := chain3 _ _ _ _ _ _ _ _ _ _ _ _ _ e7 e8 e9
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9
  have hk := kara_split (2 ^ 32) A0 A1 B0 B1
  have hprod : (A0 + 2 ^ 32 * A1) * (B0 + 2 ^ 32 * B1) < 2 ^ 128 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show A0 + 2 ^ 32 * A1 < 2 ^ 64 by omega)
      (show B0 + 2 ^ 32 * B1 < 2 ^ 64 by omega)
    simpa using this
  have hm1 : A0 * B1 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hm2 : A1 * B0 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [hk]; rw [hk] at hprod
  have hTl := w3_lt l4 l5 l6
  have hP : p0 + 2 ^ 32 * p1 < 2 ^ 64 := by omega
  obtain ⟨T, hT⟩ : ∃ T, t1b + 2 ^ 32 * t2b + 2 ^ 64 * t3b = T := ⟨_, rfl⟩
  rw [hT] at cb hTl
  have hQ : (2 ^ 32 - 1 - p0) + 2 ^ 32 * (2 ^ 32 - 1 - p1) + 2 ^ 64 * (2 ^ 32 - 1) =
      2 ^ 96 - 1 - (p0 + 2 ^ 32 * p1) := by omega
  have hQ' : p0 + 2 ^ 32 * p1 + 2 ^ 64 * 0 = p0 + 2 ^ 32 * p1 := by omega
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmid ca
  · rw [hQ'] at ca
    generalize A0 * B0 = L at *
    generalize A1 * B1 = H at *
    generalize A0 * B1 = X at *
    generalize A1 * B0 = Y at *
    generalize p0 + 2 ^ 32 * p1 = P at *
    omega
  · rw [hQ] at ca
    generalize A0 * B0 = L at *
    generalize A1 * B1 = H at *
    generalize A0 * B1 = X at *
    generalize A1 * B0 = Y at *
    generalize p0 + 2 ^ 32 * p1 = P at *
    omega

end M0Crypto.Release.X25519Kara
