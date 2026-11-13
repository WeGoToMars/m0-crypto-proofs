import M0Crypto.Spec.ChaCha20
import M0Crypto.Proofs.Common

/-! Lemmas shared by the ChaCha20 kernel proofs. -/

namespace M0Crypto.Proofs

open M0Crypto.Armv6M
open M0Crypto.Spec.ChaCha20 (rotl)

/-- A nonzero register rotation by `m < 32` is the RFC left rotation by `32 - m`. -/
theorem rorC_eq_rotl (x : Armv6M.Word) (m : Nat) (c : Bool) (h0 : m ≠ 0) (h32 : m < 32) :
    (rorC x m c).1 = rotl x (32 - m) := by
  simp only [rorC, h0, ite_false, Nat.mod_eq_of_lt h32, rotl]
  rw [show 32 - (32 - m) = m by omega, BitVec.or_comm]

end M0Crypto.Proofs
