import M0Crypto.Release.X25519OpRun

/-!
Branch targets of `m0c_x25519`'s loops at any offset (plan `x25519-proofs.md`, phase 11 E):
the forward `b<cond>` over one 2-byte instruction (`bcTo c q (q + 4)`) and the backward `b`
of up to 2044 bytes (`bTo (p + k) p`). With these the loop proofs never name a code offset.
-/

namespace M0Crypto.Release.X25519Branch

/-- Sign extension of every even backward `b` offset up to 2048 bytes. -/
theorem se_back11 : ∀ k : Nat, k < 2045 → k % 2 = 0 →
    ((BitVec.ofInt 11 (-((k : Int) + 4) / 2)) ++ 0#1).signExtend 32 = -(BitVec.ofNat 32 (k + 4)) := by
  decide +kernel

/-- Target of `bTo (p + k) p`. -/
theorem b_back (p k : Nat) (hk : k % 2 = 0) (hk2 : k < 2045) :
    BitVec.ofNat 32 (p + k) + 4#32 +
      ((BitVec.ofInt 11 (((p : Int) - ((p + k : Nat) + 4)) / 2)) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 p := by
  rw [show ((p : Int) - ((p + k : Nat) + 4)) = -((k : Int) + 4) by omega, se_back11 k hk2 hk]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

/-- Target of `bcTo cond q (q + 4)`. -/
theorem bc_fwd4 (q : Nat) :
    BitVec.ofNat 32 q + 4#32 +
      ((BitVec.ofInt 8 ((((q + 4 : Nat) : Int) - ((q : Nat) + 4)) / 2)) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 (q + 4) := by
  rw [show (((q + 4 : Nat) : Int) - ((q : Nat) + 4)) / 2 = 0 by omega,
    show ((BitVec.ofInt 8 0 ++ 0#1).signExtend 32 : BitVec 32) = 0#32 by decide, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end M0Crypto.Release.X25519Branch
