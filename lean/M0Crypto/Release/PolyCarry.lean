import M0Crypto.Release.PolyMac
set_option linter.unusedSimpArgs false
namespace M0Crypto.Release.PolyCarry
open M0Crypto.Armv6M (Word addWithCarry)
open PolyArith (val4 val5)

/-- Exact five-word ADC chain, including the carry past bit 159. -/
theorem adc5 (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Word) :
    let a0 := addWithCarry x0 y0 false
    let a1 := addWithCarry x1 y1 a0.2.1
    let a2 := addWithCarry x2 y2 a1.2.1
    let a3 := addWithCarry x3 y3 a2.2.1
    let a4 := addWithCarry x4 y4 a3.2.1
    val5 a0.1.toNat a1.1.toNat a2.1.toNat a3.1.toNat a4.1.toNat + 2^160 * a4.2.1.toNat =
      val5 x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat +
      val5 y0.toNat y1.toNat y2.toNat y3.toNat y4.toNat := by
  dsimp only
  have e0 := PolyMac.awc_nat x0 y0 false
  have e1 := PolyMac.awc_nat x1 y1 (addWithCarry x0 y0 false).2.1
  have e2 := PolyMac.awc_nat x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1
  have e3 := PolyMac.awc_nat x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1
  have e4 := PolyMac.awc_nat x4 y4 (addWithCarry x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1).2.1
  simp only [val5, Bool.toNat_false] at *
  omega

/-- Low five words of an ADC chain. -/
theorem adc5_mod (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : Word) :
    let a0 := addWithCarry x0 y0 false
    let a1 := addWithCarry x1 y1 a0.2.1
    let a2 := addWithCarry x2 y2 a1.2.1
    let a3 := addWithCarry x3 y3 a2.2.1
    let a4 := addWithCarry x4 y4 a3.2.1
    val5 a0.1.toNat a1.1.toNat a2.1.toNat a3.1.toNat a4.1.toNat =
      (val5 x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat +
       val5 y0.toNat y1.toNat y2.toNat y3.toNat y4.toNat) % 2^160 := by
  have h := adc5 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4
  dsimp only at h ⊢
  have := (addWithCarry x0 y0 false).1.isLt
  have := (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).1.isLt
  have := (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).1.isLt
  have := (addWithCarry x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1).1.isLt
  have := (addWithCarry x4 y4 (addWithCarry x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1).2.1).1.isLt
  simp only [val5] at *
  omega

/-- Exact four-word ADC chain, including the carry past bit 127. -/
theorem adc4 (x0 x1 x2 x3 y0 y1 y2 y3 : Word) :
    let a0 := addWithCarry x0 y0 false
    let a1 := addWithCarry x1 y1 a0.2.1
    let a2 := addWithCarry x2 y2 a1.2.1
    let a3 := addWithCarry x3 y3 a2.2.1
    val4 a0.1.toNat a1.1.toNat a2.1.toNat a3.1.toNat + 2^128 * a3.2.1.toNat =
      val4 x0.toNat x1.toNat x2.toNat x3.toNat + val4 y0.toNat y1.toNat y2.toNat y3.toNat := by
  dsimp only
  have e0 := PolyMac.awc_nat x0 y0 false
  have e1 := PolyMac.awc_nat x1 y1 (addWithCarry x0 y0 false).2.1
  have e2 := PolyMac.awc_nat x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1
  have e3 := PolyMac.awc_nat x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1
  simp only [val4, Bool.toNat_false] at *
  omega

/-- The low four words represent their sum modulo 2^128. -/
theorem adc4_mod (x0 x1 x2 x3 y0 y1 y2 y3 : Word) :
    let a0 := addWithCarry x0 y0 false
    let a1 := addWithCarry x1 y1 a0.2.1
    let a2 := addWithCarry x2 y2 a1.2.1
    let a3 := addWithCarry x3 y3 a2.2.1
    val4 a0.1.toNat a1.1.toNat a2.1.toNat a3.1.toNat =
      (val4 x0.toNat x1.toNat x2.toNat x3.toNat + val4 y0.toNat y1.toNat y2.toNat y3.toNat) % 2^128 := by
  have h := adc4 x0 x1 x2 x3 y0 y1 y2 y3
  dsimp only at h ⊢
  have := (addWithCarry x0 y0 false).1.isLt
  have := (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).1.isLt
  have := (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).1.isLt
  have := (addWithCarry x3 y3 (addWithCarry x2 y2 (addWithCarry x1 y1 (addWithCarry x0 y0 false).2.1).2.1).2.1).1.isLt
  simp only [val4] at *
  omega
end M0Crypto.Release.PolyCarry
