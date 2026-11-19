import SafegcdTermination.Vectors
import M0Crypto.Release.Field25519Facts

namespace SafegcdTermination.Packing

open SafegcdRow
open SafegcdTermination.FoldRefine (value vec)
open M0Crypto.Armv6M (Mem)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (psum feVal_psum)

set_option linter.unusedSimpArgs false

def halfPair (lo hi : Word) : Word := lo ||| (hi <<< 16)

theorem halfPair_value (lo hi : Word) (hl : lo.toNat < 65536) (hh : hi.toNat < 65536) :
    (halfPair lo hi).toNat = lo.toNat + 65536 * hi.toNat := by
  have hd : lo &&& (hi <<< 16) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    by_cases ht : i < 16
    · simp [ht]
    · have h := Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 16 ≤ i))
      simp [show lo.getLsbD i = false from Nat.testBit_lt_two_pow h]
  rw [halfPair, ← BitVec.add_eq_or_of_and_eq_zero _ _ hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem halves_value (w : Word) :
    (low w).toNat + 65536 * (w >>> 16).toNat = w.toNat := by
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have h := w.isLt
  omega

theorem split_high (w : Word) : (w >>> 16).toNat < 65536 := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have h := w.isLt
  omega

theorem word_pairs (v w : Nat → Word) (n : Nat)
    (h : ∀ i < n, (w i).toNat = (v (2*i)).toNat + 65536 * (v (2*i+1)).toNat) :
    weighted (fun i => ((v i).toNat : Int)) (2*n) = psum (fun i => (w i).toNat) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have hW := congrArg (fun n : Nat => (n : Int)) (h n (by omega))
    have hQ : radix^(2*n) = ((2 : Int) ^ (32*n)) := by
      rw [show radix = (2 : Int)^16 by decide, ← Int.pow_mul]
      congr 1
      omega
    rw [show 2*(n+1) = (2*n+1)+1 by omega, weighted, weighted, ih', psum]
    change ((w n).toNat : Int) = (((v (2*n)).toNat + 65536 * (v (2*n+1)).toNat : Nat) : Int) at hW
    simp only [Int.natCast_add, Int.natCast_mul, show ((65536 : Nat) : Int) = 65536 from rfl] at hW
    rw [Int.pow_succ, hQ]
    have hR : radix = 65536 := rfl
    rw [hR]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rw [hW]
    grind only

theorem value_without_top (m : Mem) (a : Word) (hTop : vec m a 16 = 0#32) :
    value m a = weighted (fun i => ((vec m a i).toNat : Int)) 16 := by
  change weighted (limb (vec m a)) 16 + radix^16 * (vec m a 16).toInt = _
  rw [hTop, show (0#32).toInt = 0 from rfl, Int.mul_zero, Int.add_zero]
  exact weighted_congr 16 (fun i hi => by simp only [limb, hi, ite_true])

theorem vector_packed (m m' : Mem) (a a' : Word)
    (ht : vec m a 16 = 0#32)
    (h : ∀ i < 8, (vec m' a' i).toNat = (vec m a (2*i)).toNat + 65536 * (vec m a (2*i+1)).toNat) :
    value m a = feVal m' a' := by
  rw [value_without_top m a ht, feVal_psum]
  exact word_pairs _ _ 8 h

end SafegcdTermination.Packing
