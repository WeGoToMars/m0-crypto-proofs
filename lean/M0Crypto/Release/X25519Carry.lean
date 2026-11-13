import M0Crypto.Armv6M.Step

/-!
Carry and borrow facts for the X25519 field routines, over `Nat`.

`adc_nat` is the statement of `Poly1305Mac.awc_nat`, restated here so that the X25519
arithmetic does not import the Poly1305 machine proofs. `sbc_nat` is its twin for
`subs`/`sbcs`, which add `NOT y` with carry in `c`: the carry out is NOT borrow, so the
borrow out is `1 - C`. `sbc_pair` is the 64-bit `subs lo, x; sbcs hi, y`.

Machine proofs turn each carry chain into these equations once, and the rest of the
argument is linear arithmetic over `Nat` (`omega`).
-/

namespace M0Crypto.Release.X25519Carry

open M0Crypto.Armv6M (Word addWithCarry)

/-- `addWithCarry`: 32-bit result plus 2^32 times the carry out is the exact sum. -/
theorem adc_nat (x y : Word) (c : Bool) :
    (addWithCarry x y c).1.toNat + 2 ^ 32 * (addWithCarry x y c).2.1.toNat =
      x.toNat + y.toNat + c.toNat := by
  simp only [addWithCarry, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  by_cases h : (x.toNat + y.toNat + c.toNat) % 2 ^ 32 = x.toNat + y.toNat + c.toNat
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.toNat_false]; omega
  · simp only [h, ne_eq, not_false_eq_true, decide_true, Bool.toNat_true]; omega

theorem carry_le (x y : Word) (c : Bool) : (addWithCarry x y c).2.1.toNat ≤ 1 := by
  cases (addWithCarry x y c).2.1 <;> decide

/-- `sbcs` (and `subs` with `c = true`): `x - y - (1 - c)`, with borrow out `1 - C`.
The result plus `y` plus the borrow in equals `x` plus 2^32 times the borrow out. -/
theorem sbc_nat (x y : Word) (c : Bool) :
    (addWithCarry x (~~~y) c).1.toNat + y.toNat + (1 - c.toNat) =
      x.toNat + 2 ^ 32 * (1 - (addWithCarry x (~~~y) c).2.1.toNat) := by
  have e := adc_nat x (~~~y) c
  have hl := carry_le x (~~~y) c
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  have hy := y.isLt
  rw [BitVec.toNat_not] at e
  omega

/-- One `subs lo, x; sbcs hi, y` pair: 64-bit subtraction of `y:x` with its borrow out. -/
theorem sbc_pair (lo hi x y : Word) :
    (addWithCarry hi (~~~y) (addWithCarry lo (~~~x) true).2.1).1.toNat * 2 ^ 32 +
        (addWithCarry lo (~~~x) true).1.toNat + (y.toNat * 2 ^ 32 + x.toNat) =
      hi.toNat * 2 ^ 32 + lo.toNat +
        2 ^ 64 * (1 - (addWithCarry hi (~~~y) (addWithCarry lo (~~~x) true).2.1).2.1.toNat) := by
  have e1 := sbc_nat lo x true
  have e2 := sbc_nat hi y (addWithCarry lo (~~~x) true).2.1
  have := carry_le lo (~~~x) true
  have := carry_le hi (~~~y) (addWithCarry lo (~~~x) true).2.1
  simp only [Bool.toNat_true] at e1
  omega

end M0Crypto.Release.X25519Carry
