import SafegcdRow.Columns

namespace SafegcdRow

set_option maxHeartbeats 900000

/-- Little-endian radix expansion. n counts the words included in the value. -/
def weighted (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => weighted f n + radix^n * f n

theorem weighted_congr (n : Nat) {f g : Nat → Int} (h : ∀ i < n, f i = g i) :
    weighted f n = weighted g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [weighted, weighted, h n (by omega), ih (fun i hi => h i (by omega))]

private theorem weighted_add (f g : Nat → Int) (n : Nat) :
    weighted (fun i => f i + g i) n = weighted f n + weighted g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [weighted, ih]; grind

private theorem weighted_mul (a : Int) (f : Nat → Int) (n : Nat) :
    weighted (fun i => a * f i) n = a * weighted f n := by
  induction n with
  | zero => simp [weighted]
  | succ n ih => simp only [weighted, ih]; grind

def limb (f : Nat → Word) (i : Nat) : Int :=
  if i < 16 then f i |>.toNat else f i |>.toInt

def VecWellFormed (f : Nat → Word) : Prop :=
  (∀ i < 16, (f i).toNat < 65536) ∧ -65535 ≤ (f 16).toInt ∧ (f 16).toInt ≤ 65535

def numerator (s : Input) : Int :=
  s.pins.a.toInt * weighted (limb s.x) 17 + s.pins.b.toInt * weighted (limb s.y) 17

structure Args (s : Input) : Prop where
  x : VecWellFormed s.x
  y : VecWellFormed s.y
  norm : rowNorm s.pins.a.toInt s.pins.b.toInt
  t : (s.pins.t.toNat : Int) = numerator s * 2587 % divisor

def columnZ (s : Input) (i : Nat) : Int :=
  s.pins.a.toInt * limb s.x i + s.pins.b.toInt * limb s.y i + sparse s.pins.t.toNat i

def exactCarry (s : Input) : Nat → Int
  | 0 => 0
  | i+1 => (columnZ s i + exactCarry s i) / radix

def rawDigit (s : Input) (i : Nat) : Int :=
  (columnZ s i + exactCarry s i) % radix

private theorem limb_bound {f : Nat → Word} (h : VecWellFormed f) (i : Nat) (hi : i < 17) :
    -65535 ≤ limb f i ∧ limb f i ≤ 65535 := by
  unfold limb
  split
  · have := h.1 i (by assumption)
    omega
  · have e : i = 16 := by omega
    subst i
    exact h.2

private theorem limb_word (f : Nat → Word) (i : Nat) :
    BitVec.ofInt 32 (limb f i) = f i := by
  unfold limb
  split
  · simp
  · exact BitVec.ofInt_toInt

private theorem corr_word (t : Word) (i : Nat) :
    correctionWord t i = BitVec.ofInt 32 (sparse t.toNat i) := by
  have h : BitVec.ofInt 32 (t.toNat : Int) = t := by simp
  by_cases h0 : i = 0
  · simp only [correctionWord, h0, ↓reduceIte, sparse, Int.neg_mul, BitVec.ofInt_neg, BitVec.ofInt_mul, h]
    rw [BitVec.mul_comm]
    rfl
  · by_cases h15 : i = 15
    · simp only [correctionWord, h15, ↓reduceIte, sparse]
      change t <<< 15 = 32768#32 * t
      rw [BitVec.mul_comm]
      exact BitVec.shiftLeft_eq_mul_twoPow t 15
    · simp [correctionWord, sparse, h0, h15]

private theorem accumulator (s : Input) (i : Nat)
    (h : carryIn s i = BitVec.ofInt 32 (exactCarry s i)) :
    accumulateWord s i (carryIn s i) =
      BitVec.ofInt 32 (columnZ s i + exactCarry s i) := by
  simp only [accumulateWord, columnZ, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    limb_word, ← corr_word, h]
  ac_rfl

private theorem bounded_column (s : Input) (h : Args s) (i : Nat) (hi : i < 17)
    (hc : carryBound (exactCarry s i)) :
    signed32 (columnZ s i + exactCarry s i) ∧ carryBound (exactCarry s (i+1)) := by
  have ht : 0 ≤ (s.pins.t.toNat : Int) ∧ s.pins.t.toNat < divisor := by
    rw [h.t]
    have hd : 0 < divisor := by decide
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hd⟩
  have hv := column_bound h.norm (limb_bound h.x i hi) (limb_bound h.y i hi) hc
    (sparse_bound s.pins.t.toNat ht i)
  rw [show s.pins.a.toInt * limb s.x i + s.pins.b.toInt * limb s.y i + exactCarry s i +
      sparse s.pins.t.toNat i = columnZ s i + exactCarry s i by unfold columnZ; ac_rfl] at hv
  exact hv

theorem carry_certificate (s : Input) (h : Args s) (i : Nat) (hi : i ≤ 17) :
    carryIn s i = BitVec.ofInt 32 (exactCarry s i) ∧ carryBound (exactCarry s i) := by
  induction i with
  | zero => exact ⟨rfl, by change carryBound 0; unfold carryBound; decide⟩
  | succ i ih =>
    have ⟨hce, hcb⟩ := ih (by omega)
    have hv := bounded_column s h i (by omega) hcb
    refine ⟨?_, hv.2⟩
    rw [carryIn, accumulator s i hce, carry_int _ hv.1, exactCarry]

theorem signed_accumulator (s : Input) (h : Args s) (i : Nat) (hi : i < 17) :
    signed32 (columnZ s i + exactCarry s i) ∧
      (accumulateWord s i (carryIn s i)).toInt = columnZ s i + exactCarry s i := by
  obtain ⟨he, hc⟩ := carry_certificate s h i (by omega)
  have hs := (bounded_column s h i hi hc).1
  exact ⟨hs, by rw [accumulator s i he]; exact int_of_word _ hs⟩

theorem digit_certificate (s : Input) (h : Args s) (i : Nat) (hi : i < 17) :
    ((digit s i).toNat : Int) = rawDigit s i := by
  rw [digit, accumulator s i (carry_certificate s h i (by omega)).1, low_int, rawDigit]
  have hr : 0 < radix := by decide
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

private theorem raw_range (s : Input) (i : Nat) : 0 ≤ rawDigit s i ∧ rawDigit s i < radix :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

private theorem rem_value (s : Input) (h : Args s) (i : Nat) (hi : i < 17) :
    ((remainder (digit s i)).toNat : Int) = rawDigit s i / divisor := by
  rw [rem_word, BitVec.toNat_ofNat]
  have hd := low_bound (accumulateWord s i (carryIn s i))
  change (digit s i).toNat < 65536 at hd
  rw [Nat.mod_eq_of_lt (by omega : (digit s i).toNat / 16384 < 2^32)]
  have hv := digit_certificate s h i hi
  simp only [divisor]
  omega

private theorem rem_bound (s : Input) (i : Nat) : (remainder (digit s i)).toNat < 4 := by
  rw [rem_word, BitVec.toNat_ofNat]
  have hd := low_bound (accumulateWord s i (carryIn s i))
  change (digit s i).toNat < 65536 at hd
  omega

def qDigit (s : Input) (i : Nat) : Int :=
  4 * (rawDigit s (i+1) % divisor) + rawDigit s i / divisor

private theorem outLow (s : Input) (h : Args s) (i : Nat) (hi : i < 16) :
    limb (outWord s) i = qDigit s i := by
  simp only [limb, hi, outWord, show i ≠ 16 by omega, ↓reduceIte, qDigit]
  rw [emit_int _ _ (rem_bound s i)]
  have hn := digit_certificate s h (i+1) (by omega)
  have hr := rem_value s h i (by omega)
  simp only [divisor] at *
  omega

private theorem outHigh (s : Input) (h : Args s) :
    limb (outWord s) 16 = 4 * exactCarry s 17 + rawDigit s 16 / divisor := by
  have hc := carry_certificate s h 17 (by decide)
  have hC : (carryIn s 17).toInt = exactCarry s 17 := by
    rw [hc.1]
    exact int_of_word _ (by have := hc.2; simp only [carryBound, signed32] at *; omega)
  simp only [limb, Nat.lt_irrefl, ↓reduceIte, outWord]
  rw [top_int _ _ (rem_bound s 16) (by rw [hC]; have := hc.2; simp [carryBound] at this; omega),
    hC, rem_value s h 16 (by decide)]

private theorem integer_carry (s : Input) (i : Nat) :
    rawDigit s i + radix * exactCarry s (i+1) = columnZ s i + exactCarry s i := by
  simp only [rawDigit, exactCarry]
  exact Int.emod_add_mul_ediv _ _

private theorem carry_value (s : Input) (n : Nat) :
    weighted (rawDigit s) n + radix^n * exactCarry s n = weighted (columnZ s) n := by
  induction n with
  | zero => simp [weighted, exactCarry]
  | succ n ih =>
    simp only [weighted, Int.pow_succ]
    have hn := integer_carry s n
    grind

private theorem shift_value (s : Input) (n : Nat) :
    weighted (rawDigit s) (n+1) = rawDigit s 0 % divisor +
    divisor * (weighted (qDigit s) n + radix^n * (rawDigit s n / divisor)) := by
  induction n with
  | zero =>
    simp only [weighted, Int.pow_zero, Int.one_mul, Int.zero_add]
    exact (Int.emod_add_mul_ediv _ _).symm
  | succ n ih =>
    have e : divisor * 4 = radix := by decide
    have h := Int.emod_add_mul_ediv (rawDigit s (n+1)) divisor
    rw [weighted, ih]
    simp only [weighted, Int.pow_succ, qDigit]
    grind

private theorem correction_value (t : Int) :
    weighted (sparse t) 17 = t * prime := by
  simp only [weighted, sparse, ↓reduceIte, Nat.reduceEqDiff,
    Int.add_zero, Int.mul_zero, Int.pow_zero, Int.one_mul, Int.zero_add, radix, prime]
  grind

theorem exact_value (s : Input) (h : Args s) :
    divisor * weighted (limb (outWord s)) 17 = numerator s + (s.pins.t.toNat : Int) * prime := by
  have hz : weighted (columnZ s) 17 = numerator s + (s.pins.t.toNat : Int) * prime := by
    unfold columnZ numerator
    rw [weighted_add, weighted_add, weighted_mul, weighted_mul, correction_value]
  have hc := carry_value s 17
  have hs := shift_value s 16
  have e : weighted (limb (outWord s)) 16 = weighted (qDigit s) 16 :=
    weighted_congr 16 (outLow s h)
  have hdiv : rawDigit s 0 % divisor = 0 := by
    have hd := exact_correction (numerator s) s.pins.t.toNat h.t
    rw [← hz, ← hc, hs] at hd
    have hm : radix^17 % divisor = 0 := by decide +kernel
    have hcarry : (radix^17 * exactCarry s 17) % divisor = 0 := by
      rw [Int.mul_emod, hm, Int.zero_mul]
      rfl
    rw [Int.add_emod, hcarry, Int.add_zero, Int.emod_emod, Int.add_emod,
      Int.mul_emod, Int.emod_self, Int.zero_mul] at hd
    simpa only [Int.zero_emod, Int.add_zero, Int.emod_emod] using hd

  rw [weighted, outHigh s h, e]
  rw [hdiv, Int.zero_add] at hs
  rw [hs, hz] at hc
  have eq : divisor * 4 = radix := by decide
  have pw : radix^17 = radix^16 * radix := by rw [show 17 = 16+1 by decide, Int.pow_succ]
  grind

end SafegcdRow
