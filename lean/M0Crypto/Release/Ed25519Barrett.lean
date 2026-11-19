import M0Crypto.Release.Ed25519Words
import M0Crypto.Spec.Ed25519

/-!
Barrett reduction modulo `L` as `m0c_sc_reduce` performs it, and `m0c_sc_muladd`.

`m0c_sc_reduce` (`emit_sc_reduce` in `bench/ed25519/gen_ed25519.py`) is HAC algorithm 14.42
with `b = 2^32`, `k = 8` on a 512-bit input `x` (16 words):

1. `Q2 = q1 * mu` with `q1 = x / 2^224` (words 7 to 15 of the input) and `mu = 2^512 / L`
   (`m0c_ed_mu`, 9 words), by `m0c_mp_mul` with `n = 9`.
2. `Q4 = q3 * L` with `q3 = Q2 / 2^288` (words 9 to 17 of `Q2`), by `m0c_mp_mul` with `n = 9`.
3. `R = x - Q4` over 9 words (`sub_words`), which is `x - q3 L` exactly (`barrett`).
4. Twice: `T = R - L` over 9 words, and `R = T` when that subtraction does not borrow, by
   `m0c_cmov` on 8 words. Word 8 of `R` is zero because `R < 3 L < 2^254`, and word 8 of `T`
   is zero whenever `T` is selected (it can be nonzero otherwise: `x = 0` gives
   `T = 2^288 - L`), so selecting 8 words loses nothing.
5. The 8 low words of `R` are `x mod L`.

`sc_reduce_nat` states the whole routine with the machine facts as hypotheses: the two
products, the three subtraction chains (through `Ed25519Words.sub_chain`) and the selects.
`sc_muladd_nat` states the product and addition of `m0c_sc_muladd`.
-/

namespace M0Crypto.Release.Ed25519Barrett

open M0Crypto.Release.Ed25519Words
open M0Crypto.Spec.Ed25519 (L)

/-- `mu = floor(2^512 / L)`, the constant `m0c_ed_mu`. -/
def mu : Nat := 2 ^ 512 / L

theorem L_pos : 0 < L := by decide

theorem two224_lt_L : 2 ^ 224 < L := by decide

theorem three_L_lt : 3 * L < 2 ^ 254 := by decide

theorem L_lt : L < 2 ^ 253 := by decide

/-- HAC 14.42, fact 14.43, for `x / B1 < B2` and `mu = B1 B2 / L`: the quotient estimate
`q3 = (x / B1) mu / B2` is at most the true quotient and at least the true quotient minus 2,
so `0 ≤ x - q3 L < 3 L`. -/
theorem barrett_gen (x L B1 B2 : Nat) (hL : 0 < L) (hB1p : 0 < B1) (hB1 : B1 ≤ L) (hx : x / B1 < B2) :
    x / B1 * (B1 * B2 / L) / B2 * L ≤ x ∧
      x < x / B1 * (B1 * B2 / L) / B2 * L + 3 * L := by
  have hB2 : 0 < B2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
  generalize hq1 : x / B1 = q1 at hx
  generalize hmu : B1 * B2 / L = μ
  generalize hq3 : q1 * μ / B2 = q3
  have f1 : B1 * q1 ≤ x := hq1 ▸ Nat.mul_div_le x B1
  have f1' : x < B1 * q1 + B1 := by
    have := Nat.div_add_mod x B1; have := Nat.mod_lt x hB1p; rw [hq1] at *; omega
  have f2 : L * μ ≤ B1 * B2 := hmu ▸ Nat.mul_div_le _ L
  have f2' : B1 * B2 < L * μ + L := by
    have := Nat.div_add_mod (B1 * B2) L; have := Nat.mod_lt (B1 * B2) hL; rw [hmu] at *; omega
  have f3 : B2 * q3 ≤ q1 * μ := hq3 ▸ Nat.mul_div_le _ B2
  have f3' : q1 * μ < B2 * q3 + B2 := by
    have := Nat.div_add_mod (q1 * μ) B2; have := Nat.mod_lt (q1 * μ) hB2; rw [hq3] at *; omega
  constructor
  · refine Nat.le_of_mul_le_mul_left (c := B2) ?_ hB2
    have g1 := Nat.mul_le_mul_right L f3
    have g2 := Nat.mul_le_mul_left q1 f2
    have g3 := Nat.mul_le_mul_left B2 f1
    calc B2 * (q3 * L) = B2 * q3 * L := by ac_rfl
      _ ≤ q1 * μ * L := g1
      _ = q1 * (L * μ) := by ac_rfl
      _ ≤ q1 * (B1 * B2) := g2
      _ = B2 * (B1 * q1) := by ac_rfl
      _ ≤ B2 * x := g3
  · apply Nat.lt_of_mul_lt_mul_left (a := B2)
    have g1 := Nat.mul_lt_mul_of_pos_left f1' hB2
    have g2 := Nat.mul_le_mul_left q1 (Nat.le_of_lt f2')
    have g3 := Nat.mul_lt_mul_of_pos_right f3' hL
    have g4 := Nat.mul_le_mul_right L (Nat.le_of_lt hx)
    have g5 := Nat.mul_le_mul_left B2 hB1
    grind

/-- `barrett_gen` for `m0c_sc_reduce`: `B1 = 2^224`, `B2 = 2^288`, `mu = 2^512 / L`. -/
theorem barrett (x : Nat) (hx : x < 2 ^ 512) :
    x / 2 ^ 224 * mu / 2 ^ 288 * L ≤ x ∧ x < x / 2 ^ 224 * mu / 2 ^ 288 * L + 3 * L := by
  have e : 2 ^ 224 * 2 ^ 288 = 2 ^ 512 := by decide +kernel
  have hmu : 2 ^ 224 * 2 ^ 288 / L = mu := by unfold mu; rw [e]
  have h := barrett_gen x L (2 ^ 224) (2 ^ 288) L_pos (Nat.two_pow_pos _)
    (Nat.le_of_lt two224_lt_L)
    (Nat.div_lt_of_lt_mul (by rw [e]; exact hx))
  rw [hmu] at h
  exact h

/-- Two conditional subtractions reduce a value below `3 m`. -/
theorem two_sub_mod (m D : Nat) (hD : D < 3 * m) :
    (if m ≤ (if m ≤ D then D - m else D) then (if m ≤ D then D - m else D) - m
      else (if m ≤ D then D - m else D)) = D % m := by
  by_cases h1 : m ≤ D
  · rw [ite_eq_left h1, Nat.mod_eq_sub_mod h1]
    by_cases h2 : m ≤ D - m
    · rw [ite_eq_left h2, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right h2, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1, Nat.mod_eq_of_lt (by omega)]

theorem wsum_nine (f : Nat → Nat) : wsum f 9 = wsum f 8 + 2 ^ 256 * f 8 := rfl

/-- One conditional subtraction of `m0c_sc_reduce`: `T = R - L` over 9 words with borrow `b`,
then words 0 to 7 of `R` replaced by those of `T` when `b = 0`; word 8 is kept. For
`R < 2^256` the result is `R - L` when `L ≤ R`, else `R`, and its word 8 is zero. -/
theorem select_step {R T R' : Nat → Nat} {b : Nat}
    (hTw : ∀ j, j < 9 → T j < 2 ^ 32)
    (hR : wsum R 9 < 2 ^ 256)
    (hT : wsum T 9 + L = wsum R 9 + 2 ^ 288 * b)
    (hb : b ≤ 1)
    (hsel : ∀ j, j < 8 → R' j = if b = 0 then T j else R j) (h8 : R' 8 = R 8) :
    wsum R' 9 = (if L ≤ wsum R 9 then wsum R 9 - L else wsum R 9) ∧ R' 8 = 0 := by
  have hT9 := wsum_lt hTw
  have hR8 : R 8 = 0 := wsum_top_zero (n := 8) (show wsum R 9 < 2 ^ (32 * 8) by omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · have hge : L ≤ wsum R 9 := by omega
    have hT8 : T 8 = 0 := wsum_top_zero (n := 8) (show wsum T 9 < 2 ^ (32 * 8) by omega)
    have : wsum R' 9 = wsum T 9 := by
      rw [wsum_nine R', wsum_nine T, h8, hR8, hT8,
        wsum_congr (g := T) (fun j hj => by rw [hsel j hj]; rfl)]
    rw [ite_eq_left hge, this, h8, hR8]
    omega
  · have hlt : ¬ L ≤ wsum R 9 := by omega
    have : wsum R' 9 = wsum R 9 := by
      rw [wsum_nine R', wsum_nine R, h8,
        wsum_congr (g := R) (fun j hj => by rw [hsel j hj]; rfl)]
    rw [ite_eq_right hlt, this, h8, hR8]
    exact ⟨rfl, rfl⟩

/-- `m0c_sc_reduce`. `IN`: the 16 input words. `MU`, `LW`: the 9 words of `m0c_ed_mu` and
`m0c_ed_l9`. `Q2`, `Q4`: the 18-word products. `R0`: the first subtraction (borrow `b0`).
`T1`, `R1` and `T2`, `R2`: the two conditional subtractions. The 8 words of `R2` hold
`x mod L`. -/
theorem sc_reduce_nat {IN MU LW Q2 Q4 R0 T1 R1 T2 R2 : Nat → Nat} {b0 b1 b2 : Nat}
    (hIN : ∀ j, j < 16 → IN j < 2 ^ 32) (hQ2w : ∀ j, j < 18 → Q2 j < 2 ^ 32)
    (hQ4w : ∀ j, j < 18 → Q4 j < 2 ^ 32) (hR0w : ∀ j, j < 9 → R0 j < 2 ^ 32)
    (hT1w : ∀ j, j < 9 → T1 j < 2 ^ 32) (hT2w : ∀ j, j < 9 → T2 j < 2 ^ 32)
    (hMU : ∀ j, j < 9 → MU j = mu / 2 ^ (32 * j) % 2 ^ 32)
    (hLW : ∀ j, j < 9 → LW j = L / 2 ^ (32 * j) % 2 ^ 32)
    (hQ2 : wsum Q2 18 = wsum (fun j => IN (7 + j)) 9 * wsum MU 9)
    (hQ4 : wsum Q4 18 = wsum (fun j => Q2 (9 + j)) 9 * wsum LW 9)
    (hR0 : wsum R0 9 + wsum Q4 9 = wsum IN 9 + 2 ^ 288 * b0)
    (hT1 : wsum T1 9 + wsum LW 9 = wsum R0 9 + 2 ^ 288 * b1) (hb1 : b1 ≤ 1)
    (hR1 : ∀ j, j < 8 → R1 j = if b1 = 0 then T1 j else R0 j) (hR18 : R1 8 = R0 8)
    (hT2 : wsum T2 9 + wsum LW 9 = wsum R1 9 + 2 ^ 288 * b2) (hb2 : b2 ≤ 1)
    (hR2 : ∀ j, j < 8 → R2 j = if b2 = 0 then T2 j else R1 j) (hR28 : R2 8 = R1 8) :
    wsum R2 8 = wsum IN 16 % L := by
  have hmu : wsum MU 9 = mu := by
    rw [wsum_congr hMU]; decide +kernel
  have hLv : wsum LW 9 = L := by
    rw [wsum_congr hLW]; decide +kernel
  rw [hLv] at hT1 hT2
  generalize hx : wsum IN 16 = x
  have hx512 : x < 2 ^ 512 := by
    have h := wsum_lt hIN
    rw [hx, show 32 * 16 = 512 from rfl] at h
    exact h
  -- q1, q3 and the low words of the products
  have hq1 : wsum (fun j => IN (7 + j)) 9 = x / 2 ^ 224 := by
    rw [← hx, ← show 32 * 7 = 224 from rfl]; exact (wsum_div (m := 7) (k := 9) hIN).symm
  have hq3 : wsum (fun j => Q2 (9 + j)) 9 = x / 2 ^ 224 * mu / 2 ^ 288 := by
    rw [← hq1, ← hmu, ← hQ2, ← show 32 * 9 = 288 from rfl]
    exact (wsum_div (m := 9) (k := 9) hQ2w).symm
  have hlo4 : wsum Q4 9 = x / 2 ^ 224 * mu / 2 ^ 288 * L % 2 ^ 288 := by
    rw [← hq3, ← hLv, ← hQ4, ← show 32 * 9 = 288 from rfl]
    exact (wsum_mod (m := 9) (k := 9) hQ4w).symm
  have hlo : wsum IN 9 = x % 2 ^ 288 := by
    rw [← hx, ← show 32 * 9 = 288 from rfl]; exact (wsum_mod (m := 9) (k := 7) hIN).symm
  obtain ⟨hb, ht⟩ := barrett x hx512
  generalize x / 2 ^ 224 * mu / 2 ^ 288 = q3 at hb ht hlo4
  -- R0 = x - q3 L
  have hR0v : wsum R0 9 = x - q3 * L := by
    have := wsum_lt hR0w
    have := Nat.div_add_mod x (2 ^ 288)
    have := Nat.div_add_mod (q3 * L) (2 ^ 288)
    have := Nat.mod_lt x (Nat.two_pow_pos 288)
    have := Nat.mod_lt (q3 * L) (Nat.two_pow_pos 288)
    have := three_L_lt
    omega
  have h3 := three_L_lt
  have hR0b : wsum R0 9 < 2 ^ 256 := by omega
  obtain ⟨hv1, h18⟩ := select_step (R := R0) (T := T1) (b := b1) hT1w hR0b hT1 hb1 hR1 hR18
  obtain ⟨hv2, h28⟩ := select_step (R := R1) (T := T2) (b := b2) hT2w (by split at hv1 <;> omega) hT2 hb2 hR2 hR28
  have h98 : wsum R2 9 = wsum R2 8 := by rw [wsum_succ, h28]; simp
  have hxD : x = (x - q3 * L) + q3 * L := by omega
  rw [← h98, hv2, hv1, hR0v]
  conv => rhs; rw [hxD, Nat.add_mul_mod_self_right]
  exact two_sub_mod L (x - q3 * L) (by omega)

/-- `m0c_sc_muladd` before its call to `m0c_sc_reduce`: `P = K * A` (16 words, by
`m0c_mp_mul` with `n = 8`), then `adds`/`adcs` of the 8 words of `Rr` into words 0 to 7 and of
zero into words 8 to 15. The dropped final carry is zero. -/
theorem sc_muladd_nat {K A Rr P S c : Nat → Nat}
    (hK : ∀ j, j < 8 → K j < 2 ^ 32) (hA : ∀ j, j < 8 → A j < 2 ^ 32)
    (hR : ∀ j, j < 8 → Rr j < 2 ^ 32) (hS : ∀ j, j < 16 → S j < 2 ^ 32)
    (hP : wsum P 16 = wsum K 8 * wsum A 8)
    (hadd : ∀ j, j < 16 → S j + 2 ^ 32 * c (j + 1) = P j + (if j < 8 then Rr j else 0) + c j)
    (hc0 : c 0 = 0) :
    wsum S 16 = wsum K 8 * wsum A 8 + wsum Rr 8 := by
  have hch := add_chain P (fun j => if j < 8 then Rr j else 0) S c 16 hadd
  have hext : wsum (fun j => if j < 8 then Rr j else 0) 16 = wsum Rr 8 := by
    have h1 : wsum (fun j => if j < 8 then Rr j else 0) 8 = wsum Rr 8 :=
      wsum_congr (fun j hj => ite_eq_left hj)
    have h2 : wsum (fun j => if 8 + j < 8 then Rr (8 + j) else 0) 8 = 0 := by
      rw [wsum_congr (g := fun _ => 0) (fun j _ => ite_eq_right (by omega))]
      exact wsum_const_zero 8
    rw [show 16 = 8 + 8 from rfl, wsum_add, h1, h2, Nat.mul_zero, Nat.add_zero]
  rw [hext, hc0, Nat.add_zero, hP] at hch
  have hKv := wsum_lt hK
  have hAv := wsum_lt hA
  have hRv := wsum_lt hR
  have hSv := wsum_lt hS
  have hm : wsum K 8 * wsum A 8 ≤ (2 ^ (32 * 8) - 1) * (2 ^ (32 * 8) - 1) :=
    Nat.mul_le_mul (Nat.le_sub_one_of_lt hKv) (Nat.le_sub_one_of_lt hAv)
  have key : (2 ^ (32 * 8) - 1) * (2 ^ (32 * 8) - 1) + 2 ^ (32 * 8) ≤ 2 ^ (32 * 16) := by
    decide +kernel
  generalize wsum K 8 * wsum A 8 = KA at hm hch ⊢
  generalize (2 ^ (32 * 8) - 1) * (2 ^ (32 * 8) - 1) = Q at hm key
  generalize 2 ^ (32 * 8) = P at *
  generalize 2 ^ (32 * 16) = W at *
  have hc : c 16 = 0 := by
    rcases Nat.eq_zero_or_pos (c 16) with h0 | h0
    · exact h0
    · have := Nat.mul_le_mul_left W (Nat.succ_le_of_lt h0)
      omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at hch
  exact hch

/-- The specification's `S = (r + k s) mod L` from `r mod L` and `k mod L`, the values that
`m0c_ed25519_sign` passes to `m0c_sc_muladd`. -/
theorem muladd_mod (r k s : Nat) : (k % L * s + r % L) % L = (r + k * s) % L := by
  rw [Nat.add_comm r, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod]

/-- `m0c_cmov` on one word: `d ^ ((s ^ d) & m)` with the mask `m` all ones or zero. -/
theorem cmov_word (d s : BitVec 32) (sel : Bool) :
    d ^^^ ((s ^^^ d) &&& (if sel then BitVec.allOnes 32 else 0#32)) = if sel then s else d := by
  cases sel
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm s d, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `sbcs r3, r3; mvns r3, r3` with carry `C` in (no borrow): all ones when `C`, else zero. -/
theorem borrow_mask (x : BitVec 32) (c : Bool) :
    ~~~(BitVec.ofNat 32 (x.toNat + (~~~x).toNat + c.toNat)) =
      if c then BitVec.allOnes 32 else 0#32 := by
  have h : x.toNat + (~~~x).toNat = 2 ^ 32 - 1 := by
    rw [BitVec.toNat_not]; have := x.isLt; omega
  rw [h]
  cases c <;> decide

end M0Crypto.Release.Ed25519Barrett
