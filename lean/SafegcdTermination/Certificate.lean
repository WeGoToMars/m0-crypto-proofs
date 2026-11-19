module

public import Lean

@[expose] public section

/-!
The absolute support of 16 integer directions bounds the divstep state
at every visit to counter 1. Between visits the two extreme return maps
suffice. All short return maps are checked with integer arithmetic.
-/

namespace SafegcdTermination

def p : Int := 2 ^ 255 - 19

def magnitude (x : Int) : Int := x.natAbs

theorem magnitude_nonneg (x : Int) : 0 ≤ magnitude x := by
  unfold magnitude
  omega

theorem magnitude_of_nonneg {x : Int} (h : 0 ≤ x) : magnitude x = x :=
  Int.natAbs_of_nonneg h

@[simp] theorem magnitude_neg (x : Int) : magnitude (-x) = magnitude x := by
  simp [magnitude]

theorem magnitude_mul (x y : Int) : magnitude (x * y) = magnitude x * magnitude y := by
  simp [magnitude, Int.natAbs_mul]

theorem magnitude_add_le (x y : Int) : magnitude (x + y) ≤ magnitude x + magnitude y := by
  have := Int.natAbs_add_le x y
  unfold magnitude
  omega

theorem magnitude_le_iff {x b : Int} : magnitude x ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  unfold magnitude
  omega

theorem magnitude_nonzero {x : Int} (h : x ≠ 0) : 1 ≤ magnitude x := by
  unfold magnitude
  omega

def w (i : Fin 16) : Int :=
  (#[1055,4000,3000,5000,2008,5302,3294,4701,1420,4112,2760,4267,1524,3461,2018,2767])[i.val]!

def a (i : Fin 16) : Int := (#[1,3,2,3,1,2,1,1,0,-1,-1,-2,-1,-3,-2,-3])[i.val]!
def b (i : Fin 16) : Int := (#[0,1,1,2,1,3,2,3,1,3,2,3,1,2,1,1])[i.val]!

def boundNumerator (n : Nat) : Int := p * 93 ^ n

def boundDenominator (n : Nat) : Int := 1000 * 125 ^ n

def Bounded (n : Nat) (f g : Int) : Prop :=
  ∀ i : Fin 16, magnitude (a i * g + b i * f) * boundDenominator n ≤ w i * boundNumerator n

def shortLimit : Nat := 12

theorem p_pos : 0 < p := by decide +kernel

theorem boundNumerator_nonneg (n : Nat) : 0 ≤ boundNumerator n :=
  Int.mul_nonneg (Int.le_of_lt p_pos) (Int.pow_nonneg (by decide))

theorem boundDenominator_pos (n : Nat) : 0 < boundDenominator n :=
  Int.mul_pos (by decide) (Int.pow_pos (by decide))

theorem boundNumerator_add (n t : Nat) : boundNumerator (n + t) = boundNumerator n * 93 ^ t := by
  simp only [boundNumerator, Int.pow_add, Int.mul_assoc]

theorem boundDenominator_add (n t : Nat) : boundDenominator (n + t) = boundDenominator n * 125 ^ t := by
  simp only [boundDenominator, Int.pow_add, Int.mul_assoc]

theorem decay (k : Nat) : (125 : Int) ^ (2*k) ≤ 2^k * 93^(2*k) := by
  rw [Int.pow_mul (a := 125), Int.pow_mul (a := 93), ← Int.mul_pow]
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ, Int.pow_succ]
    exact Int.mul_le_mul ih (show (125 : Int)^2 ≤ 2 * 93^2 by decide)
      (by decide) (Int.pow_nonneg (by decide))

/-- Pull a direction back through the extreme return map with parameter
0 or 2^j-1, clearing the denominator 2^(2j+1). -/
def endpoint (j : Nat) (upper : Bool) (i : Fin 16) : Int × Int :=
  let m : Int := 2 ^ j
  let c := if upper then 2 * m - 1 else 1
  (c * a i + 2 * m * b i, -m * a i)

/-- Two neighboring signed normals. Absolute bounds make their negatives
available as well. The final interval ends at (-1,0). -/
def neighbor (i : Fin 16) : Fin 16 := i + 1
def signNext (i : Fin 16) : Int := if i.val = 15 then -1 else 1

def bracket (v : Int × Int) (i : Fin 16) : Int × Int × Int :=
  let r := neighbor i
  let sg := signNext i
  let u := a i
  let z := b i
  let x := sg * a r
  let y := sg * b r
  (v.1 * y - v.2 * x, u * v.2 - z * v.1, u * y - z * x)

def upperHalf (v : Int × Int) : Int × Int :=
  if v.2 < 0 || (v.2 == 0 && v.1 < 0) then (-v.1, -v.2) else v

def checkLine (j : Nat) (upper : Bool) (i k : Fin 16) : Bool :=
  let (l,r,d) := bracket (upperHalf (endpoint j upper i)) k
  let t := 2*j+1
  decide (0 ≤ l ∧ 0 ≤ r ∧ 0 < d ∧
    (l * w k + r * w (neighbor k)) * 125 ^ t ≤ d * 2 ^ t * w i * 93 ^ t)

def shortAt (j : Nat) (i : Fin 16) : Bool :=
  (List.finRange 16).any (checkLine j false i) &&
    (List.finRange 16).any (checkLine j true i)

def shortFailure : Option (Nat × Fin 16) :=
  (List.range shortLimit).findSome? fun j =>
    ((List.finRange 16).find? fun i => !shortAt j i).map (j, ·)

theorem shortFailure_eq_none :
    shortFailure = none ↔
      (List.range shortLimit).all (fun j => (List.finRange 16).all (shortAt j)) = true := by
  simp [shortFailure]

theorem checkShort :
    (List.range shortLimit).all (fun j => (List.finRange 16).all (shortAt j)) = true :=
  shortFailure_eq_none.mp (by decide +kernel)

def seedAt (i : Fin 16) : Bool :=
  decide (1000 * magnitude (b i) ≤ w i ∧ 1000 * magnitude (a i + b i) ≤ w i)

def seedFailure : Option (Fin 16) := (List.finRange 16).find? (fun i => !seedAt i)

theorem seedFailure_eq_none :
    seedFailure = none ↔ (List.finRange 16).all seedAt = true := by
  simp [seedFailure]

theorem initialWeights : (List.finRange 16).all seedAt = true :=
  seedFailure_eq_none.mp (by decide +kernel)

def longCost (i : Fin 16) : Int := 2 * (magnitude (a i) + magnitude (b i)) * w 0 + magnitude (a i) * w 8

def longAt (i : Fin 16) : Bool :=
  decide (longCost i * 125 ^ (2 * shortLimit + 1) ≤
    w i * 2 ^ (shortLimit + 1) * 93 ^ (2 * shortLimit + 1))

def longFailure : Option (Fin 16) := (List.finRange 16).find? (fun i => !longAt i)

theorem longFailure_eq_none :
    longFailure = none ↔ (List.finRange 16).all longAt = true := by
  simp [longFailure]

theorem checkLong : (List.finRange 16).all longAt = true :=
  longFailure_eq_none.mp (by decide +kernel)

theorem terminal602 : (1055 : Int) * p * 93 ^ 602 < 1000 * 125 ^ 602 := by decide +kernel
theorem terminal601 : (1055 : Int) * p * 93 ^ 601 < 1000 * 125 ^ 601 := by decide +kernel

end SafegcdTermination
