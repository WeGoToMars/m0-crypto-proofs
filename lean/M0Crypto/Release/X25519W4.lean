import M0Crypto.Release.X25519Carry

/-!
Four-word carry chains: the value equations of
`adds/adcs` and `subs/sbcs` chains over four words, and of a word-wise xor with a mask of
zeros or ones, stated on the exact terms the machine semantics produces. A macro proof
instantiates these on its symbolic state instead of summing per-word equations itself.
-/

namespace M0Crypto.Release.X25519W4
open M0Crypto.Armv6M (Word addWithCarry)
open M0Crypto.Release.X25519Carry (adc_nat sbc_nat carry_le)

/-- Four words as a number, least significant first. -/
def w4 (a b c d : Word) : Nat := a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat + 2 ^ 96 * d.toNat

theorem w4_lt (a b c d : Word) : w4 a b c d < 2 ^ 128 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [w4]; omega

/-- A four-word `adcs` chain with carry in `c`. The steps are given as equations, as
`generalize` leaves them in a macro proof. -/
theorem add4 {x0 x1 x2 x3 y0 y1 y2 y3 : Word} {c : Bool} {A0 A1 A2 A3 : Word × Bool × Bool}
    (h0 : addWithCarry x0 y0 c = A0) (h1 : addWithCarry x1 y1 A0.2.1 = A1)
    (h2 : addWithCarry x2 y2 A1.2.1 = A2) (h3 : addWithCarry x3 y3 A2.2.1 = A3) :
    w4 A0.1 A1.1 A2.1 A3.1 + 2 ^ 128 * A3.2.1.toNat = w4 x0 x1 x2 x3 + w4 y0 y1 y2 y3 + c.toNat := by
  have e0 := adc_nat x0 y0 c; have e1 := adc_nat x1 y1 A0.2.1
  have e2 := adc_nat x2 y2 A1.2.1; have e3 := adc_nat x3 y3 A2.2.1
  rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
  simp only [w4]; omega

/-- A four-word `sbcs` chain with carry in `c` (borrow in `1 - c`). -/
theorem sub4 {x0 x1 x2 x3 y0 y1 y2 y3 : Word} {c : Bool} {A0 A1 A2 A3 : Word × Bool × Bool}
    (h0 : addWithCarry x0 (~~~y0) c = A0) (h1 : addWithCarry x1 (~~~y1) A0.2.1 = A1)
    (h2 : addWithCarry x2 (~~~y2) A1.2.1 = A2) (h3 : addWithCarry x3 (~~~y3) A2.2.1 = A3) :
    w4 A0.1 A1.1 A2.1 A3.1 + w4 y0 y1 y2 y3 + (1 - c.toNat) =
      w4 x0 x1 x2 x3 + 2 ^ 128 * (1 - A3.2.1.toNat) := by
  have e0 := sbc_nat x0 y0 c; have e1 := sbc_nat x1 y1 A0.2.1
  have e2 := sbc_nat x2 y2 A1.2.1; have e3 := sbc_nat x3 y3 A2.2.1
  have l0 := carry_le x0 (~~~y0) c; have l1 := carry_le x1 (~~~y1) A0.2.1
  have l2 := carry_le x2 (~~~y2) A1.2.1; have l3 := carry_le x3 (~~~y3) A2.2.1
  rw [h0] at e0 l0; rw [h1] at e1 l1; rw [h2] at e2 l2; rw [h3] at e3 l3
  have : c.toNat ≤ 1 := Bool.toNat_le c
  simp only [w4]; omega

/-- The mask of a Boolean: all ones or zero. -/
def mask (neg : Bool) : Word := if neg then BitVec.allOnes 32 else 0#32

theorem mask_toNat (neg : Bool) : (mask neg).toNat = if neg then 2 ^ 32 - 1 else 0 := by
  cases neg <;> rfl

theorem xor_mask (w : Word) (neg : Bool) :
    (w ^^^ mask neg).toNat = if neg then 2 ^ 32 - 1 - w.toNat else w.toNat := by
  cases neg
  · simp [mask]
  · simp only [mask, ite_true]; rw [BitVec.xor_allOnes, BitVec.toNat_not]

/-- Word-wise xor with a mask: the four-word complement or the value itself. -/
theorem xor4 (a b c d : Word) (neg : Bool) :
    w4 (a ^^^ mask neg) (b ^^^ mask neg) (c ^^^ mask neg) (d ^^^ mask neg) =
      if neg then 2 ^ 128 - 1 - w4 a b c d else w4 a b c d := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [w4, xor_mask]; cases neg <;> simp <;> omega

theorem w4_mask (neg : Bool) :
    w4 (mask neg) (mask neg) (mask neg) (mask neg) = if neg then 2 ^ 128 - 1 else 0 := by
  cases neg <;> rfl

/-- `sbcs m, m` after a borrow-out `c`: the mask of `!c`. -/
theorem sbcs_self (M : Word) (c : Bool) : (addWithCarry M (~~~M) c).1 = mask (!c) := by
  apply BitVec.eq_of_toNat_eq
  have e := adc_nat M (~~~M) c
  have hn : (~~~M).toNat = 2 ^ 32 - 1 - M.toNat := by simp [BitVec.toNat_not]
  have := M.isLt; have := (addWithCarry M (~~~M) c).1.isLt
  have := carry_le M (~~~M) c
  cases c <;> simp [mask] at e ⊢ <;> omega

end M0Crypto.Release.X25519W4
