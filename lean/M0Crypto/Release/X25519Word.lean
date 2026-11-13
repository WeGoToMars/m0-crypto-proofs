import M0Crypto.Armv6M.State

/-!
Word-level identities of the X25519 field routines.

Each lemma takes as hypotheses the equations a machine proof gets from one macro: the 16-bit
halves, the 16x16 products, and one equation per `adds`/`adcs` (result plus `2^32` times the
carry out equals the sum, `X25519Carry.adc_nat`). The conclusion is the value the macro
computes. Names follow the generator (`bench/x25519/gen_x25519.py`):

* `mul32_nat`: macro `mul32`, `rl:rh = rl * rb` from four 16x16 products.
* `sqr32_nat`: macro `sqr32`, `rl:rh = rl^2` from three products, the middle one doubled by a
  shift of 17.
* `mulcWord_nat`: one `word` of `m0c_fe_mulc_add`, `121666 * a + b + k` with
  `121666 = 2 * 60833`.
* `select_word`: one word of `select_words`, `a ^ ((b ^ a) & m)` for a mask `m` of 0 or all
  ones.
-/

namespace M0Crypto.Release.X25519Word

theorem mul16_lt {x y : Nat} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) : x * y < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

theorem mul32_lt {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : x * y < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

/-- The four partial products of a 32x32 product from 16-bit halves. -/
theorem halves_mul (aL aH bL bH : Nat) :
    (aL + 2 ^ 16 * aH) * (bL + 2 ^ 16 * bH) =
      aL * bL + 2 ^ 16 * (bH * aL) + 2 ^ 16 * (aH * bL) + 2 ^ 32 * (aH * bH) := by
  grind

/-- Macro `mul32`. `s1, h1` after the first `adds`/`adcs` pair, `s2, h2` after the second;
`c*` are the carries. The product is `s2 + 2^32 * h2`. -/
theorem mul32_nat (aL aH bL bH s1 c1 h1 d1 s2 c2 h2 d2 : Nat)
    (haL : aL < 2 ^ 16) (haH : aH < 2 ^ 16) (hbL : bL < 2 ^ 16) (hbH : bH < 2 ^ 16)
    (hs1 : s1 + 2 ^ 32 * c1 = aL * bL + bH * aL % 2 ^ 16 * 2 ^ 16)
    (hh1 : h1 + 2 ^ 32 * d1 = aH * bH + bH * aL / 2 ^ 16 + c1)
    (hs2 : s2 + 2 ^ 32 * c2 = s1 + aH * bL % 2 ^ 16 * 2 ^ 16)
    (hh2 : h2 + 2 ^ 32 * d2 = h1 + aH * bL / 2 ^ 16 + c2)
    (hs1l : s1 < 2 ^ 32) (hh1l : h1 < 2 ^ 32) (hs2l : s2 < 2 ^ 32) (hh2l : h2 < 2 ^ 32) :
    s2 + 2 ^ 32 * h2 = (aL + 2 ^ 16 * aH) * (bL + 2 ^ 16 * bH) := by
  have hp : (aL + 2 ^ 16 * aH) * (bL + 2 ^ 16 * bH) < 2 ^ 64 := mul32_lt (by omega) (by omega)
  rw [halves_mul] at hp ⊢
  have := mul16_lt haL hbL; have := mul16_lt hbH haL
  have := mul16_lt haH hbL; have := mul16_lt haH hbH
  generalize aL * bL = Z at *
  generalize bH * aL = X at *
  generalize aH * bL = Y at *
  generalize aH * bH = W at *
  omega

/-- Macro `sqr32`. The middle product `aH * aL` is added twice by shifting it left by 17. -/
theorem sqr32_nat (aL aH s c h d : Nat) (haL : aL < 2 ^ 16) (haH : aH < 2 ^ 16)
    (hs : s + 2 ^ 32 * c = aL * aL + aH * aL % 2 ^ 15 * 2 ^ 17)
    (hh : h + 2 ^ 32 * d = aH * aH + aH * aL / 2 ^ 15 + c)
    (hsl : s < 2 ^ 32) (hhl : h < 2 ^ 32) :
    s + 2 ^ 32 * h = (aL + 2 ^ 16 * aH) * (aL + 2 ^ 16 * aH) := by
  have hp : (aL + 2 ^ 16 * aH) * (aL + 2 ^ 16 * aH) < 2 ^ 64 := mul32_lt (by omega) (by omega)
  have e : (aL + 2 ^ 16 * aH) * (aL + 2 ^ 16 * aH) =
      aL * aL + 2 ^ 17 * (aH * aL) + 2 ^ 32 * (aH * aH) := by grind
  rw [e] at hp ⊢
  have := mul16_lt haL haL; have := mul16_lt haH haL; have := mul16_lt haH haH
  generalize aL * aL = Z at *
  generalize aH * aL = X at *
  generalize aH * aH = W at *
  omega

/-- One `word` of `m0c_fe_mulc_add`: `t = aL * 60833`, `x = aH * 60833`, then `t + t`,
`+ (x << 17)`, `+ b` and `+ k`, with the high word collecting `x >> 15` and the carries.
The result `lo + 2^32 * hi` is `121666 * a + b + k`. Without `k`, take `k = 0`. -/
theorem mulcWord_nat (aL aH b k t1 c1 h1 d1 t2 c2 h2 d2 t3 c3 h3 d3 t4 c4 h4 d4 : Nat)
    (haL : aL < 2 ^ 16) (haH : aH < 2 ^ 16) (hb : b < 2 ^ 32) (hk : k < 2 ^ 32)
    (e1 : t1 + 2 ^ 32 * c1 = aL * 60833 + aL * 60833)
    (f1 : h1 + 2 ^ 32 * d1 = aH * 60833 / 2 ^ 15 + c1)
    (e2 : t2 + 2 ^ 32 * c2 = t1 + aH * 60833 % 2 ^ 15 * 2 ^ 17)
    (f2 : h2 + 2 ^ 32 * d2 = h1 + c2)
    (e3 : t3 + 2 ^ 32 * c3 = t2 + b)
    (f3 : h3 + 2 ^ 32 * d3 = h2 + c3)
    (e4 : t4 + 2 ^ 32 * c4 = t3 + k)
    (f4 : h4 + 2 ^ 32 * d4 = h3 + c4)
    (ht3 : t3 < 2 ^ 32) (hh3 : h3 < 2 ^ 32) (ht4 : t4 < 2 ^ 32) (hh4 : h4 < 2 ^ 32) :
    t4 + 2 ^ 32 * h4 = 121666 * (aL + 2 ^ 16 * aH) + b + k := by
  have hX := mul16_lt haL (show 60833 < 2 ^ 16 by omega)
  have hY := mul16_lt haH (show 60833 < 2 ^ 16 by omega)
  have e : 121666 * (aL + 2 ^ 16 * aH) = 2 * (aL * 60833) + 2 ^ 17 * (aH * 60833) := by grind
  rw [e]
  obtain ⟨X, eX⟩ : ∃ X, aL * 60833 = X := ⟨_, rfl⟩
  obtain ⟨Y, eY⟩ : ∃ Y, aH * 60833 = Y := ⟨_, rfl⟩
  rw [eX] at e1 hX ⊢
  rw [eY] at f1 e2 hY ⊢
  omega

/-- One word of `select_words`: `a ^ ((b ^ a) & m)` is `a` for `m = 0` and `b` for
`m = -1`. -/
theorem select_word (a b m : BitVec 32) (hm : m = 0 ∨ m = BitVec.allOnes 32) :
    a ^^^ ((b ^^^ a) &&& m) = if m = 0 then a else b := by
  rcases hm with h | h
  · subst h; simp
  · have hne : m ≠ 0 := by
      rw [h]; intro h0
      have := congrArg BitVec.toNat h0
      simp at this
    simp only [hne, ↓reduceIte]
    rw [h, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm a b,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end M0Crypto.Release.X25519Word
