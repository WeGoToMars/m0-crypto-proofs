import M0Crypto.Release.ConstantTime.Transfer
import M0Crypto.Thumb.Program

/-! Agreement between abstract relative offsets and machine branch addresses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)

/-- An accepted relative target denotes the same address under 32-bit arithmetic. -/
theorem relTarget_address (base : Word) (off target : Nat) (disp : Int)
    (h : relTarget off disp = some target) :
    base + BitVec.ofNat 32 target =
      base + BitVec.ofNat 32 off + 4#32 + BitVec.ofInt 32 disp := by
  unfold relTarget at h
  dsimp only at h
  split at h
  · rename_i hn
    have ht : target = ((off : Int) + 4 + disp).toNat := by simpa using h.symm
    subst target
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hn, BitVec.ofInt_add,
      BitVec.ofInt_add, BitVec.ofInt_natCast]
    simp only [BitVec.ofInt_ofNat, BitVec.add_assoc]
  · contradiction

end M0Crypto.Release.ConstantTime
