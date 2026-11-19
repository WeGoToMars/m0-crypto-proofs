import Std

namespace SafegcdRow

abbrev Word := BitVec 32

def radix : Int := 65536
def divisor : Int := 16384
def prime : Int := 2 ^ 255 - 19

def low (w : Word) : Word := (w.setWidth 16).setWidth 32
def carry (w : Word) : Word := w.sshiftRight 16
def remainder (w : Word) : Word := w >>> 14

def emit (w prev : Word) : Word := low ((w <<< 2) ||| prev)
def emitTop (c prev : Word) : Word := (c <<< 2) ||| prev

def signed32 (z : Int) : Prop := -2147483648 ≤ z ∧ z < 2147483648

theorem int_of_word (z : Int) (h : signed32 z) : (BitVec.ofInt 32 z).toInt = z :=
  BitVec.toInt_ofInt_eq_self (by decide) h.1 h.2

theorem low_int (z : Int) : (low (BitVec.ofInt 32 z)).toNat = (z % radix).toNat := by
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_ofInt, radix]
  omega

theorem carry_int (z : Int) (h : signed32 z) :
    carry (BitVec.ofInt 32 z) = BitVec.ofInt 32 (z / radix) := by
  rw [← BitVec.ofInt_toInt (x := carry (BitVec.ofInt 32 z))]
  rw [carry, BitVec.toInt_sshiftRight, int_of_word z h]
  simp [Int.shiftRight_eq_div_pow, radix]

theorem rem_word (w : Word) : remainder w = BitVec.ofNat 32 (w.toNat / 16384) := by
  apply BitVec.eq_of_toNat_eq
  simp only [remainder, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have := w.isLt
  omega

theorem low_bound (w : Word) : (low w).toNat < 65536 := by
  simp [low]
  omega

private theorem shift_or (x y : Word) (h : y.toNat < 4) :
    (x <<< 2) ||| y = (x <<< 2) + y := by
  symm
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases hlt : i < 2
  · simp [hlt]
  · have hy : y.toNat < 2^i := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 2 ≤ i))
    have hb : y.getLsbD i = false := Nat.testBit_lt_two_pow hy
    simp [hb]

theorem emit_top_bits (c prev : Word) (hp : prev.toNat < 4) :
    emitTop c prev = (c <<< 2) + prev :=
  shift_or c prev hp

theorem emit_int (w prev : Word) (hp : prev.toNat < 4) :
    (emit w prev).toNat = w.toNat % 16384 * 4 + prev.toNat := by
  rw [emit, shift_or w prev hp]
  simp only [BitVec.toNat_add, low, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem top_int (c prev : Word) (hp : prev.toNat < 4)
    (hc : -32768 ≤ c.toInt ∧ c.toInt ≤ 32767) :
    (emitTop c prev).toInt = 4 * c.toInt + prev.toNat := by
  have ec : c <<< 2 = BitVec.ofInt 32 (c.toInt * 4) := by
    rw [BitVec.ofInt_mul, BitVec.ofInt_toInt]
    exact BitVec.shiftLeft_eq_mul_twoPow c 2
  have ep : prev = BitVec.ofInt 32 prev.toNat := by
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [emit_top_bits c prev hp, ec]
  conv => lhs; rw [ep]
  rw [← BitVec.ofInt_add, int_of_word]
  · omega
  · constructor <;> omega

/-- Matrix row norm. Limb products and corrections use signed word arithmetic. -/
def rowNorm (a b : Int) : Prop := (a.natAbs : Int) + b.natAbs ≤ divisor

def carryBound (c : Int) : Prop := -24576 ≤ c ∧ c ≤ 24576

private theorem abs_mul_bound (a x : Int) (hx : -65535 ≤ x ∧ x ≤ 65535) :
    -65535 * (a.natAbs : Int) ≤ a * x ∧ a * x ≤ 65535 * (a.natAbs : Int) := by
  by_cases ha : 0 ≤ a
  · rw [Int.natAbs_of_nonneg ha]
    constructor
    · rw [Int.mul_comm (-65535)]
      exact Int.mul_le_mul_of_nonneg_left hx.1 ha
    · rw [Int.mul_comm 65535]
      exact Int.mul_le_mul_of_nonneg_left hx.2 ha
  · have an : (a.natAbs : Int) = -a := by omega
    rw [an]
    constructor
    · rw [Int.mul_neg, ← Int.neg_mul, show -(-65535 : Int) = 65535 by decide,
        Int.mul_comm 65535]
      exact Int.mul_le_mul_of_nonpos_left (by omega) hx.2
    · rw [Int.mul_neg, ← Int.neg_mul, Int.mul_comm (-65535)]
      exact Int.mul_le_mul_of_nonpos_left (by omega) hx.1

/-- Uniform invariant for all columns, including sparse corrections at 0 and 15. -/
theorem column_bound {a b x y c k : Int} (hn : rowNorm a b)
    (hx : -65535 ≤ x ∧ x ≤ 65535) (hy : -65535 ≤ y ∧ y ≤ 65535) (hc : carryBound c)
    (hk : -311277 ≤ k ∧ k ≤ 536838144) :
    signed32 (a * x + b * y + c + k) ∧ carryBound ((a * x + b * y + c + k) / radix) := by
  have hx' := abs_mul_bound a x hx
  have hy' := abs_mul_bound b y hy
  simp only [rowNorm, divisor] at hn
  simp only [signed32, carryBound, radix] at hc ⊢
  omega

def sparse (t : Int) (i : Nat) : Int :=
  if i = 0 then -19 * t else if i = 15 then 32768 * t else 0

theorem sparse_bound (t : Int) (ht : 0 ≤ t ∧ t < divisor) (i : Nat) :
    -311277 ≤ sparse t i ∧ sparse t i ≤ 536838144 := by
  simp only [divisor] at ht
  unfold sparse
  split
  · omega
  · split <;> omega

theorem exact_correction (n t : Int) (ht : t = n * 2587 % divisor) :
    (n + t * prime) % divisor = 0 := by
  subst t
  simp only [prime, divisor]
  have p : (2 ^ 255 - 19 : Int) % 16384 = 16365 := by decide +kernel
  rw [Int.add_emod, Int.mul_emod, p]
  simp only [Int.emod_emod]
  omega

end SafegcdRow
