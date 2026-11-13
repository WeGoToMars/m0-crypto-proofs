import M0Crypto.Release.X25519Congr

/-!
Reduction modulo `p = 2^255 - 19` as the field routines perform it (plan phase 6, items 4
and 5).

Every lemma is stated over `Nat` values of multi-word quantities: a machine proof sums the
carry equations of one routine into the value-level hypotheses below (linear arithmetic),
and these lemmas give the congruence and the bound that makes the last carry vanish. The
names follow the generator (`bench/x25519/gen_x25519.py`):

* `combine_reduce_nat`: the fused 256-bit Karatsuba combine and reduction of `m0c_fe_mul` and
  `m0c_fe_sqr` (`combine_reduce`).
* `fe_add_nat`, `fe_sub_nat`: `fe_add_body`, `fe_sub_body`.
* `mulc_add_nat`: `m0c_fe_mulc_add`.
* `canon_nat`: `canon_body`, the only step whose result is the exact residue.

`congr_of_eq` turns an exact equation `a = b + p * m` into `a ≡p b`.
-/

namespace M0Crypto.Release.X25519Reduce

open M0Crypto.Release.X25519Congr

/-- `p` as a natural number. -/
def pN : Nat := 2 ^ 255 - 19

theorem p_eq : p = (pN : Int) := by unfold p pN; omega

theorem congr_of_eq {a b m : Nat} (h : a = b + pN * m) : (a : Int) ≡p b := by
  unfold ModP
  rw [h, p_eq]; push_cast
  rw [Int.add_mul_emod_self_left]

theorem two255 : (2 : Int) ^ 255 ≡p 19 := by
  have h := congr_of_eq (a := 2 ^ 255) (b := 19) (m := 1) (by unfold pN; omega)
  simpa using h

theorem two256 : (2 : Int) ^ 256 ≡p 38 := by
  have h := congr_of_eq (a := 2 ^ 256) (b := 38) (m := 2) (by unfold pN; omega)
  simpa using h

/-- `combine_reduce`. `L`, `H`: the low and high 256-bit products; `Y`: the middle term,
below `2^257`, given by its pieces: `L = Llo + 2^224 * L7`, `H = H128 + 2^128 * Hm +
2^224 * H7`, `Y = Y96 + 2^96 * Y3 + 2^128 * Y47 + 2^256 * Y8` (word ranges 0-6, 7; 0-3,
4-6, 7; 0-2, 3, 4-7, 8). Phase C stores `F38lo = H128 + Y47` with carry `cC`, and
`s = Y8 + cC`. The top word is computed first, `v = L7 + Y3 + 38 * H7`, and split as
`base7 + 2^31 * q`; `19 * q` enters the chain at word 0. The seven low words `lo7` and their
carry `k7` come from one chain; the last word is `base7 + k7`. The result is congruent to
`L + 2^128 * Y + 2^256 * H`, and the last word does not overflow. -/
theorem combine_reduce_nat (L H Y Llo L7 H128 Hm H7 Y96 Y3 Y47 Y8 F38lo cC s v q base7 lo7 k7 : Nat)
    (hLd : L = Llo + 2 ^ 224 * L7) (hHd : H = H128 + 2 ^ 128 * Hm + 2 ^ 224 * H7)
    (hYd : Y = Y96 + 2 ^ 96 * Y3 + 2 ^ 128 * Y47 + 2 ^ 256 * Y8)
    (hLlo : Llo < 2 ^ 224) (hL7 : L7 < 2 ^ 32) (hH128 : H128 < 2 ^ 128) (hHm : Hm < 2 ^ 96)
    (hH7 : H7 < 2 ^ 32) (hY96 : Y96 < 2 ^ 96) (hY3 : Y3 < 2 ^ 32) (hY47 : Y47 < 2 ^ 128)
    (hY8 : Y8 ≤ 1)
    (hC : F38lo + 2 ^ 128 * cC = H128 + Y47) (hF : F38lo < 2 ^ 128)
    (hs : s = Y8 + cC)
    (hv : v = L7 + Y3 + 38 * H7)
    (hq : base7 + 2 ^ 31 * q = v) (hb : base7 < 2 ^ 31)
    (hlow : lo7 + 2 ^ 224 * k7 = Llo + 2 ^ 128 * Y96 + 38 * F38lo + 2 ^ 128 * (38 * Hm) +
      2 ^ 128 * (38 * s) + 19 * q)
    (hlo : lo7 < 2 ^ 224) :
    base7 + k7 < 2 ^ 32 ∧
      ((lo7 + 2 ^ 224 * (base7 + k7) : Nat) : Int) ≡p ((L + 2 ^ 128 * Y + 2 ^ 256 * H : Nat) : Int) := by
  have hcC : cC ≤ 1 := by omega
  have hq' : q ≤ 80 := by omega
  have hk : k7 ≤ 42 := by omega
  refine ⟨by omega, ModP.symm (congr_of_eq (m := 2 * (H + Y47 + 2 ^ 128 * Y8) + q) ?_)⟩
  subst hLd hHd hYd hs hv
  unfold pN
  omega

/-- `fe_add_body`: `s + 2^256 * c = a + b`; `q = 2 * c + bit 255 of s`; the chain adds
`19 * q` to `s` with bit 255 cleared. No carry leaves the chain. -/
theorem fe_add_nat (a b s c r c' : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hs : s + 2 ^ 256 * c = a + b) (hsl : s < 2 ^ 256)
    (hr : r + 2 ^ 256 * c' = s % 2 ^ 255 + 19 * (2 * c + s / 2 ^ 255)) (hrl : r < 2 ^ 256) :
    c' = 0 ∧ (r : Int) ≡p ((a + b : Nat) : Int) := by
  have hc : c ≤ 1 := by omega
  refine ⟨by omega, ModP.symm (congr_of_eq (m := 2 * c + s / 2 ^ 255) ?_)⟩
  unfold pN
  omega

/-- `fe_sub_body`: `d + b = a + 2^256 * br`; `k = (1 - bit 255 of d) + 2 * br`; the chain
subtracts `19 * k` from `d` with bit 255 set. No borrow leaves the chain. -/
theorem fe_sub_nat (a b d br r br' : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hd : d + b = a + 2 ^ 256 * br) (hdl : d < 2 ^ 256)
    (hr : r + 19 * ((1 - d / 2 ^ 255) + 2 * br) = d % 2 ^ 255 + 2 ^ 255 + 2 ^ 256 * br')
    (hrl : r < 2 ^ 256) :
    br' = 0 ∧ (r : Int) ≡p (a : Int) - b := by
  have hbr' : br' = 0 := by omega
  refine ⟨hbr', ?_⟩
  have hbit : d / 2 ^ 255 ≤ 1 := by omega
  have h : (r : Int) = (a : Int) - b + p * ((1 - d / 2 ^ 255 + 2 * br : Nat) : Int) := by
    rw [p_eq]; unfold pN; omega
  unfold ModP
  rw [h, Int.add_mul_emod_self_left]

/-- `m0c_fe_mulc_add`. Word 7 first: `lo7 + 2^32 * hi7 = 121666 * a7 + b7`, `q = 2 * hi7 +
bit 31 of lo7`, `base7 = lo7 mod 2^31`. The chain over words 0 to 6 starts with carry
`19 * q` and ends with carry `k7`; the last word is `base7 + k7`. -/
theorem mulc_add_nat (a b lo7 hi7 lo k7 : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h7 : lo7 + 2 ^ 32 * hi7 = 121666 * (a / 2 ^ 224) + b / 2 ^ 224)
    (hlow : lo + 2 ^ 224 * k7 = 121666 * (a % 2 ^ 224) + b % 2 ^ 224 +
      19 * (2 * hi7 + lo7 / 2 ^ 31))
    (hlo : lo < 2 ^ 224) :
    lo7 % 2 ^ 31 + k7 < 2 ^ 32 ∧
      ((lo + 2 ^ 224 * (lo7 % 2 ^ 31 + k7) : Nat) : Int) ≡p ((121666 * a + b : Nat) : Int) := by
  refine ⟨by omega, ModP.symm (congr_of_eq (m := 2 * hi7 + lo7 / 2 ^ 31) ?_)⟩
  unfold pN
  omega

/-- `canon_body`: fold bit 255 (`a1 = a mod 2^255 + 19 * bit`), test `a1 + 19` at bit 255,
add `19` times that bit and clear bit 255. The result is `a mod p`. -/
theorem canon_nat (a a1 q2 a2 r : Nat) (ha : a < 2 ^ 256)
    (h1 : a1 = a % 2 ^ 255 + 19 * (a / 2 ^ 255))
    (h2 : q2 = (a1 + 19) / 2 ^ 255)
    (h3 : a2 = a1 + 19 * q2)
    (h4 : r = a2 % 2 ^ 255) :
    r = a % pN ∧ r < pN := by
  have hb : a / 2 ^ 255 ≤ 1 := by omega
  have hdec : a = a1 + pN * (a / 2 ^ 255) := by unfold pN; omega
  have hp : 0 < pN := by unfold pN; omega
  by_cases hc : pN ≤ a1
  · have hq : q2 = 1 := by unfold pN at hc; omega
    have hr : r = a1 - pN := by unfold pN at hc ⊢; omega
    have ha' : a = (a1 - pN) + pN * (a / 2 ^ 255 + 1) := by unfold pN at hc hdec ⊢; omega
    have hlt : a1 - pN < pN := by unfold pN at hc ⊢; omega
    refine ⟨?_, by omega⟩
    rw [hr, ha', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · have hq : q2 = 0 := by unfold pN at hc; omega
    have hr : r = a1 := by unfold pN at hc; omega
    refine ⟨?_, by omega⟩
    rw [hr, hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

end M0Crypto.Release.X25519Reduce
