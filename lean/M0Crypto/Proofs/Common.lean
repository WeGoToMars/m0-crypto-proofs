import M0Crypto.Spec.ChaCha20
import M0Crypto.Armv6M.StraightLine

/-! Lemmas shared by the ChaCha20 kernel proofs. -/

namespace M0Crypto.Proofs

open M0Crypto.Armv6M
open M0Crypto.Spec.ChaCha20 (rotl)

/-- A nonzero register rotation by `m < 32` is the RFC left rotation by `32 - m`. -/
theorem rorC_eq_rotl (x : Armv6M.Word) (m : Nat) (c : Bool) (h0 : m ≠ 0) (h32 : m < 32) :
    (rorC x m c).1 = rotl x (32 - m) := by
  simp only [rorC, h0, ite_false, Nat.mod_eq_of_lt h32, rotl]
  rw [show 32 - (32 - m) = m by omega, BitVec.or_comm]

/-- Flag-free part of `AddWithCarry(x, y, '0')` is 32-bit wrapping addition. -/
theorem addWithCarry_fst (x y : Armv6M.Word) : (addWithCarry x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [addWithCarry, BitVec.toNat_add]

/-! Literal forms of `LowReg.toReg`, so register hypotheses rewrite syntactically. -/
theorem toReg_0 : LowReg.toReg 0 = 0 := rfl
theorem toReg_1 : LowReg.toReg 1 = 1 := rfl
theorem toReg_2 : LowReg.toReg 2 = 2 := rfl
theorem toReg_3 : LowReg.toReg 3 = 3 := rfl
theorem toReg_4 : LowReg.toReg 4 = 4 := rfl
theorem toReg_5 : LowReg.toReg 5 = 5 := rfl
theorem toReg_6 : LowReg.toReg 6 = 6 := rfl
theorem toReg_7 : LowReg.toReg 7 = 7 := rfl

end M0Crypto.Proofs
