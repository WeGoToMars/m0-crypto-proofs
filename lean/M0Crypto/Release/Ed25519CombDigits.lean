import M0Crypto.Release.Ed25519Bytes

/-!
The signed comb recoding of `m0c_sc_recode_comb` (Hamburg 2012), for `n` combs of four teeth.

The code (`emit_recode_comb` in `bench/ed25519/gen_ed25519.py`) takes a scalar `e < 2^255`,
forms `u = (e >> 1) | 2^255` (`recode_u`), so that `2 (e / 2) + 1 = sum_{j<256} (2 u_j - 1) 2^j`
(`signed_bits`). For each digit index `q < 64` it reads the four teeth of `u` at
`combPos n q k = q / n + (n - 1 - q mod n) (256 / n) + k (64 / n)`, `k < 4` (the masked byte and
bit indices are exact because `combPos n q k < 256`), packs them as `v < 16`, and stores the
byte `combDigit v + 8`. `combDigit v` is `+(v mod 8 + 1)` when the top tooth is 1, else
`-(7 - v mod 8 + 1)`: nonzero with `|d| ≤ 8` (`combDigit_bound`). `sign_byte` is the
register-level sign trick of the code, checked on all 16 values.

`toothVal dd c d` is the multiple of `B` that the comb table row `c` holds for the digit `d`:
`combEntry dd c j = 2^(dd (4c+3)) + sum_{k<3} (2 j_k - 1) 2^(dd (4c+k))` is entry `j` of row
`c` (`table_comb` in `edref.py`), negated for a negative digit. With `dd = 64 / n`, the
digit at `q = i n + (n - 1 - c)` belongs to round `i` and comb `c`, and

`comb_identity`: `2 (e / 2) + 1 = sum_{i < dd} 2^i sum_{c < n} toothVal dd c (digit (i n + n - 1 - c))`.

`comb_even` adds the final correction of `m0c_ge_mul_base`: `e = (2 (e / 2) + 1) - (1 - e mod 2)`.
-/

namespace M0Crypto.Release.Ed25519CombDigits

open M0Crypto.Release.Ed25519Bytes
open M0Crypto.Spec.Ed25519 (decodeInt)

/-- `sum_{j < N} f j` over `Int`. -/
def ssum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | N + 1 => ssum f N + f N

theorem ssum_succ (f : Nat → Int) (N : Nat) : ssum f (N + 1) = ssum f N + f N := rfl

theorem ssum_congr {f g : Nat → Int} {N : Nat} (h : ∀ j, j < N → f j = g j) :
    ssum f N = ssum g N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [ssum_succ, ssum_succ, ih (fun j hj => h j (by omega)), h N (by omega)]

theorem ssum_add (f : Nat → Int) (a b : Nat) :
    ssum f (a + b) = ssum f a + ssum (fun j => f (a + j)) b := by
  induction b with
  | zero => simp [ssum]
  | succ b ih => rw [← Nat.add_assoc, ssum_succ, ih, ssum_succ]; omega

theorem ssum_plus (f g : Nat → Int) (N : Nat) :
    ssum (fun j => f j + g j) N = ssum f N + ssum g N := by
  induction N with
  | zero => simp [ssum]
  | succ N ih => rw [ssum_succ, ih, ssum_succ, ssum_succ]; omega

theorem ssum_mul (a : Int) (f : Nat → Int) (N : Nat) :
    ssum (fun j => a * f j) N = a * ssum f N := by
  induction N with
  | zero => simp [ssum]
  | succ N ih => rw [ssum_succ, ih, ssum_succ, Int.mul_add]

theorem ssum_comm (f : Nat → Nat → Int) (A B : Nat) :
    ssum (fun a => ssum (fun b => f a b) B) A = ssum (fun b => ssum (fun a => f a b) A) B := by
  induction A with
  | zero =>
    simp only [ssum]
    induction B with
    | zero => rfl
    | succ B ih => rw [ssum_succ, ← ih]; rfl
  | succ A ih => rw [ssum_succ, ih, ← ssum_plus]; rfl

/-- `j = i + d m` with `i < d`, `m < M`. -/
theorem ssum_split (f : Nat → Int) (d M : Nat) :
    ssum f (d * M) = ssum (fun m => ssum (fun i => f (i + d * m)) d) M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Nat.mul_succ, ssum_add, ih, ssum_succ]
    congr 1
    exact ssum_congr (fun i _ => by rw [Nat.add_comm])

/-! ## Signed bits -/

/-- Bit `j` of `u`. -/
def ubit (u j : Nat) : Nat := u / 2 ^ j % 2

/-- The signed-bit sum of the low `N` bits: `sum_{j<N} (2 u_j - 1) 2^j = 2 (u mod 2^N) - (2^N - 1)`. -/
theorem signed_bits_mod (u N : Nat) :
    ssum (fun j => (2 * (ubit u j : Int) - 1) * 2 ^ j) N = 2 * ((u % 2 ^ N : Nat) : Int) - (2 ^ N - 1) := by
  induction N with
  | zero => simp [ssum]
  | succ N ih =>
    rw [ssum_succ, ih, Nat.mod_pow_succ, ← ubit, Int.pow_succ]
    push_cast
    generalize (2 : Int) ^ N = P
    grind

/-- `u = e / 2 + 2^255`, the bytes `U` of the code. -/
def recode_u (e : Nat) : Nat := e / 2 + 2 ^ 255

/-- `e | 1 = sum_{j<256} (2 u_j - 1) 2^j` for `e < 2^255`. -/
theorem signed_bits (e : Nat) (he : e < 2 ^ 255) :
    ssum (fun j => (2 * (ubit (recode_u e) j : Int) - 1) * 2 ^ j) 256 = 2 * ((e / 2 : Nat) : Int) + 1 := by
  have hu : recode_u e < 2 ^ 256 := by unfold recode_u; omega
  rw [signed_bits_mod, Nat.mod_eq_of_lt hu]
  unfold recode_u
  rw [Int.natCast_add, Int.natCast_pow]
  have : (2 : Int) ^ 256 = 2 * 2 ^ 255 := by rw [Int.pow_succ, Int.mul_comm]
  rw [this]
  generalize (2 : Int) ^ 255 = P
  omega

/-! ## Digits -/

/-- The digit of the packed teeth `v < 16` (bit `k` of `v` is tooth `k`). -/
def combDigit (v : Nat) : Int :=
  if v / 8 % 2 = 1 then ((v % 8 + 1 : Nat) : Int) else -((7 - v % 8 + 1 : Nat) : Int)

/-- Entry `j < 8` of comb row `c`, as a multiple of `B` (`table_comb` in `edref.py`). -/
def combEntry (dd c j : Nat) : Int :=
  2 ^ (dd * (4 * c + 3)) +
    ((2 * ((j % 2 : Nat) : Int) - 1) * 2 ^ (dd * (4 * c)) +
      (2 * ((j / 2 % 2 : Nat) : Int) - 1) * 2 ^ (dd * (4 * c + 1)) +
      (2 * ((j / 4 % 2 : Nat) : Int) - 1) * 2 ^ (dd * (4 * c + 2)))

/-- The multiple of `B` that `m0c_ge_lookup` returns for row `c` and digit `d ≠ 0`: entry
`|d| - 1`, negated when `d < 0`. -/
def toothVal (dd c : Nat) (d : Int) : Int :=
  if d < 0 then -combEntry dd c (d.natAbs - 1) else combEntry dd c (d.natAbs - 1)

theorem combDigit_bound (v : Nat) :
    combDigit v ≠ 0 ∧ -8 ≤ combDigit v ∧ combDigit v ≤ 8 := by
  unfold combDigit; split <;> omega

/-- One digit: the four signed teeth at `dd (4c + k)` are the table value of the digit. -/
theorem tooth_digit (dd c t0 t1 t2 t3 : Nat) (h0 : t0 ≤ 1) (h1 : t1 ≤ 1) (h2 : t2 ≤ 1)
    (h3 : t3 ≤ 1) :
    toothVal dd c (combDigit (t0 + 2 * t1 + 4 * t2 + 8 * t3)) =
      (2 * (t0 : Int) - 1) * 2 ^ (dd * (4 * c)) + (2 * (t1 : Int) - 1) * 2 ^ (dd * (4 * c + 1)) +
      (2 * (t2 : Int) - 1) * 2 ^ (dd * (4 * c + 2)) + (2 * (t3 : Int) - 1) * 2 ^ (dd * (4 * c + 3)) := by
  unfold toothVal combEntry
  generalize (2 : Int) ^ (dd * (4 * c)) = P0
  generalize (2 : Int) ^ (dd * (4 * c + 1)) = P1
  generalize (2 : Int) ^ (dd * (4 * c + 2)) = P2
  generalize (2 : Int) ^ (dd * (4 * c + 3)) = P3
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h3 with rfl | rfl <;>
  simp [combDigit] <;> grind

/-! ## The code's indices -/

/-- Bit position of tooth `k` of digit `q` (`r3 = q >> lg + ((n - 1 - (q & (n - 1))) << ...)`,
plus `k d`). -/
def combPos (n q k : Nat) : Nat := q / n + (n - 1 - q % n) * (256 / n) + k * (64 / n)

/-- The packed teeth of digit `q` (register `r6` before the sign step). -/
def combTeeth (n u q : Nat) : Nat :=
  ubit u (combPos n q 0) + 2 * ubit u (combPos n q 1) + 4 * ubit u (combPos n q 2) +
    8 * ubit u (combPos n q 3)

/-- The digit stored (minus 8) at index `q` for the scalar `e`. -/
def digitAt (n e q : Nat) : Int := combDigit (combTeeth n (recode_u e) q)

theorem combTeeth_lt (n u q : Nat) : combTeeth n u q < 16 := by
  unfold combTeeth ubit; omega

/-- Every digit is nonzero with `|d| ≤ 8`, and the stored byte `d + 8` is at most 16. -/
theorem digitAt_bound (n e q : Nat) :
    digitAt n e q ≠ 0 ∧ -8 ≤ digitAt n e q ∧ digitAt n e q ≤ 8 :=
  combDigit_bound _

theorem combPos_eq {n : Nat} (hn : 0 < n) (hd : n ∣ 64) {i c : Nat} (hc : c < n) (k : Nat) :
    combPos n (i * n + (n - 1 - c)) k = i + 64 / n * (4 * c + k) := by
  unfold combPos
  have h1 : (i * n + (n - 1 - c)) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (by omega)]; omega
  have h2 : (i * n + (n - 1 - c)) % n = n - 1 - c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have h3 : 256 / n = 4 * (64 / n) := by
    rw [show 256 = 4 * 64 from rfl, Nat.mul_div_assoc _ hd]
  rw [h1, h2, h3, show n - 1 - (n - 1 - c) = c by omega]
  grind

/-- The masked indices are exact: every tooth position of a digit `q < 64` is below 256. -/
theorem combPos_lt {n : Nat} (hn : 0 < n) (hd : n ∣ 64) {q k : Nat} (hq : q < 64) (hk : k < 4) :
    combPos n q k < 256 := by
  have hq' : q = q / n * n + (n - 1 - (n - 1 - q % n)) := by
    have := Nat.div_add_mod q n; have := Nat.mod_lt q hn
    rw [Nat.mul_comm]; omega
  rw [hq', combPos_eq hn hd (by omega)]
  obtain ⟨m, hm⟩ := hd
  have hmn : 64 / n = m := by rw [hm, Nat.mul_div_cancel_left _ hn]
  have hqn : q / n < m := by rw [Nat.div_lt_iff_lt_mul hn, Nat.mul_comm, ← hm]; exact hq
  have hc : n - 1 - q % n < n := by omega
  rw [hmn]
  have := Nat.mul_le_mul_left m (show 4 * (n - 1 - q % n) + k + 1 ≤ 4 * n by omega)
  have e : m * (4 * n) = 256 := by grind
  grind

/-! ## The identity -/

/-- The signed comb identity: the digits of `m0c_sc_recode_comb`, at `q = i n + (n - 1 - c)`
for round `i < 64 / n` and comb `c < n`, sum to `e | 1`. -/
theorem comb_identity {n : Nat} (hn : 0 < n) (hd : n ∣ 64) (e : Nat) (he : e < 2 ^ 255) :
    2 * ((e / 2 : Nat) : Int) + 1 =
      ssum (fun i => 2 ^ i * ssum (fun c => toothVal (64 / n) c (digitAt n e (i * n + (n - 1 - c)))) n)
        (64 / n) := by
  obtain ⟨m, hm⟩ := hd
  have hmn : 64 / n = m := by rw [hm, Nat.mul_div_cancel_left _ hn]
  rw [← signed_bits e he, hmn]
  have h256 : 256 = m * (4 * n) := by grind
  rw [h256, ssum_split, ssum_comm]
  apply ssum_congr
  intro i hi
  rw [ssum_split (d := 4), ← ssum_mul]
  apply ssum_congr
  intro c hc
  unfold digitAt combTeeth
  rw [combPos_eq hn ⟨m, hm⟩ hc, combPos_eq hn ⟨m, hm⟩ hc, combPos_eq hn ⟨m, hm⟩ hc,
    combPos_eq hn ⟨m, hm⟩ hc, hmn]
  rw [tooth_digit _ _ _ _ _ _ (by unfold ubit; omega) (by unfold ubit; omega)
    (by unfold ubit; omega) (by unfold ubit; omega)]
  simp only [ssum, Int.pow_add]
  grind

/-- The even-scalar correction of `m0c_ge_mul_base`: `[e]B = [e | 1]B - [1 - e mod 2]B`. -/
theorem comb_even (e : Nat) :
    (e : Int) = (2 * ((e / 2 : Nat) : Int) + 1) - ((1 - e % 2 : Nat) : Int) := by
  omega

/-! ## Register and byte level -/

/-- The sign step of the code on the packed teeth `x = v < 16`: `r4 = (x >> 3) - 1`,
`r6 = ((((x ^ r4) & 7) + 1) ^ r4) - r4 + 8` is the stored byte `combDigit v + 8`. -/
theorem sign_byte (v : Nat) (hv : v < 16) :
    (((((BitVec.ofNat 32 v ^^^ ((BitVec.ofNat 32 v >>> 3) - 1#32)) &&& 7#32) + 1#32) ^^^
        ((BitVec.ofNat 32 v >>> 3) - 1#32)) - ((BitVec.ofNat 32 v >>> 3) - 1#32) + 8#32).toNat =
      (combDigit v + 8).toNat := by
  have h : ∀ x : Fin 16,
      (((((BitVec.ofNat 32 x ^^^ ((BitVec.ofNat 32 x >>> 3) - 1#32)) &&& 7#32) + 1#32) ^^^
        ((BitVec.ofNat 32 x >>> 3) - 1#32)) - ((BitVec.ofNat 32 x >>> 3) - 1#32) + 8#32).toNat =
      (combDigit x + 8).toNat := by
    decide +kernel
  exact h ⟨v, hv⟩

/-- The packing loop: `movs r6, #0`, then for tooth `k` the bit `t_k` (`ands r5, #1`) shifted by
`k` and `orrs` into `r6`, is `combTeeth`'s sum `t0 + 2 t1 + 4 t2 + 8 t3`. -/
theorem teeth_or (t0 t1 t2 t3 : Nat) (h0 : t0 < 2) (h1 : t1 < 2) (h2 : t2 < 2) (h3 : t3 < 2) :
    ((((0#32 ||| BitVec.ofNat 32 t0) ||| (BitVec.ofNat 32 t1 <<< 1)) |||
        (BitVec.ofNat 32 t2 <<< 2)) ||| (BitVec.ofNat 32 t3 <<< 3)).toNat =
      t0 + 2 * t1 + 4 * t2 + 8 * t3 := by
  have h : ∀ a b c d : Fin 2,
      ((((0#32 ||| BitVec.ofNat 32 a) ||| (BitVec.ofNat 32 b <<< 1)) |||
        (BitVec.ofNat 32 c <<< 2)) ||| (BitVec.ofNat 32 d <<< 3)).toNat =
      (a : Nat) + 2 * b + 4 * c + 8 * d := by decide +kernel
  exact h ⟨t0, h0⟩ ⟨t1, h1⟩ ⟨t2, h2⟩ ⟨t3, h3⟩

/-- Bit `j` of `recode_u e`: bit `j + 1` of `e` below 255, and 1 at 255. -/
theorem recode_u_bit (e j : Nat) (he : e < 2 ^ 255) (hj : j < 256) :
    recode_u e / 2 ^ j % 2 = if j = 255 then 1 else e / 2 ^ (j + 1) % 2 := by
  rw [← Nat.toNat_testBit]
  have hb : (recode_u e).testBit j = if j < 255 then (e / 2).testBit j else (1 : Nat).testBit (j - 255) := by
    unfold recode_u
    rw [show e / 2 + 2 ^ 255 = 2 ^ 255 * 1 + e / 2 by omega,
      Nat.testBit_two_pow_mul_add _ (by omega)]
  rw [hb]
  split
  · rw [ite_eq_right (by omega), ← Nat.toNat_testBit, show e / 2 = e / 2 ^ 1 from rfl,
      Nat.testBit_div_two_pow]
  · rw [ite_eq_left (by omega), show j - 255 = 0 by omega]; rfl

/-- The bytes `U` that the first loop of `m0c_sc_recode_comb` stores (`(e_i >> 1) | (e_{i+1} << 7)`,
then `(e_31 >> 1) | 128`) hold `recode_u e`. -/
theorem recode_u_bytes {E U : List Byte} (hU : U.length = 32) (he : decodeInt E < 2 ^ 255)
    (hlo : ∀ i, i < 31 →
      (U.getD i 0).toNat = (E.getD i 0).toNat / 2 + 128 * ((E.getD (i + 1) 0).toNat % 2))
    (hhi : (U.getD 31 0).toNat = (E.getD 31 0).toNat / 2 + 128) :
    decodeInt U = recode_u (decodeInt E) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  apply congrArg (· = 1)
  by_cases hj : 256 ≤ j
  · have h1 := decodeInt_lt U
    rw [hU] at h1
    have h2 : recode_u (decodeInt E) < 2 ^ 256 := by unfold recode_u; omega
    have hp : 2 ^ 256 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  rw [decodeInt_bit, recode_u_bit _ _ he (by omega)]
  have hx := fun i => (E.getD i 0).isLt
  have hr : j % 8 < 8 := Nat.mod_lt _ (by omega)
  by_cases h255 : j = 255
  · subst h255
    simp only [ite_true, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow]
    rw [hhi]; have := hx 31; omega
  rw [ite_eq_right h255, decodeInt_bit]
  by_cases h7 : j % 8 = 7
  · have ha : (j + 1) / 8 = j / 8 + 1 := by omega
    rw [ha, show (j + 1) % 8 = 0 by omega, hlo (j / 8) (by omega), h7]
    have := hx (j / 8); simp only [Nat.pow_zero, Nat.div_one]; omega
  · rw [show (j + 1) / 8 = j / 8 by omega, show (j + 1) % 8 = j % 8 + 1 by omega]
    have hU' : (U.getD (j / 8) 0).toNat = (E.getD (j / 8) 0).toNat / 2 +
        128 * (if j / 8 < 31 then (E.getD (j / 8 + 1) 0).toNat % 2 else 1) := by
      split
      · exact hlo _ (by assumption)
      · rw [show j / 8 = 31 by omega, hhi]
    rw [hU']
    generalize (E.getD (j / 8) 0).toNat = x at *
    generalize (if j / 8 < 31 then (E.getD (j / 8 + 1) 0).toNat % 2 else 1) = t
    generalize j % 8 = r at *
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceAdd] <;> omega

end M0Crypto.Release.Ed25519CombDigits
