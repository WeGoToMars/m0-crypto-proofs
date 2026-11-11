import M0Crypto.Release.Frame

/-! Saved-register layout and generic helpers used by return proofs.
Kept separate so Poly1305 does not wait for the ChaCha return proof. -/

namespace M0Crypto.Release.ChaChaRet
open M0Crypto.Armv6M (Word Reg slot)
open M0Crypto.Thumb

/-- Saved register words at slots 35..43: r8-r11, r4-r7, LR. -/
def saved (r : Reg → Word) (i : Nat) : Word :=
  match i with
  | 0 => r 8 | 1 => r 9 | 2 => r 10 | 3 => r 11
  | 4 => r 4 | 5 => r 5 | 6 => r 6 | 7 => r 7 | _ => r 14

theorem listRegs_f0 : listRegs 0xf0 = [4, 5, 6, 7] := by decide

theorem listRegs_240 : listRegs 240#8 = [4, 5, 6, 7] := by decide

theorem bitCount_f0 : bitCount 0xf0 = 4 := by decide

theorem four_eq : (4#32 : Word) = BitVec.ofNat 32 4 := rfl

theorem slot_eq (fp : Word) (i : Nat) : slot fp i = fp + BitVec.ofNat 32 (4 * i) := rfl

end M0Crypto.Release.ChaChaRet
