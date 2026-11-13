import M0Crypto.Release.X25519Reduce

/-!
Value-level steps of the `combineReduce` composition.

`y_value`: phases A and B compute the 9-word middle term modulo `2^288` (the chains add
`P' = P xor mask`, the mask word on top and the carry-in `neg`). With the Karatsuba relation
(`Y = L + H - P` for `neg`, else `Y = L + H + P`) and `Y < 2^257`, the 9 words are `Y` exactly
and the top word `Y8` is at most 1.
-/

namespace M0Crypto.Release.X25519CR

theorem y_value (neg : Bool) (Ylo cA P03 L03 H03 Ymid Y8 P47 L47 H47 Y : Nat)
    (hP03 : P03 < 2 ^ 128) (hP47 : P47 < 2 ^ 128) (hYlo : Ylo < 2 ^ 128)
    (hYmid : Ymid < 2 ^ 128) (hY8 : Y8 < 2 ^ 32)
    (hA : Ylo + 2 ^ 128 * cA =
      (if neg then 2 ^ 128 - 1 - P03 else P03) + L03 + H03 + neg.toNat)
    (hB : Ymid + 2 ^ 128 * Y8 =
      ((if neg then 2 ^ 128 - 1 - P47 else P47) + 2 ^ 128 * (if neg then 2 ^ 32 - 1 else 0) + cA +
        L47 + H47) % 2 ^ 160)
    (hY : if neg then Y + (P03 + 2 ^ 128 * P47) = (L03 + 2 ^ 128 * L47) + (H03 + 2 ^ 128 * H47)
      else Y = (L03 + 2 ^ 128 * L47) + (H03 + 2 ^ 128 * H47) + (P03 + 2 ^ 128 * P47))
    (hYlt : Y < 2 ^ 257) :
    Ylo + 2 ^ 128 * Ymid + 2 ^ 256 * Y8 = Y ∧ Y8 ≤ 1 := by
  cases neg <;> simp only [Bool.toNat_false, Bool.toNat_true, ite_true, ite_false,
    Bool.false_eq_true] at hA hB hY <;> omega

end M0Crypto.Release.X25519CR
