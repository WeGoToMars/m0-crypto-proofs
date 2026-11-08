import M0Crypto.Sym.Known
import M0Crypto.Release.ChaChaRoundDefs

/-!
# Approach C pilot: the ChaCha20 quarter-round core through the checker

`core_regs_sym` has exactly the statement of `Release.ChaChaRound.core_regs`. Its proof
does not step through the instructions: the kernel runs the symbolic executor and the
normaliser on `core` (with r4-r7 known), and checks syntactic equality with the RFC
quarter round written as syntax (`qrS`).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (quarterRound rotl)
open M0Crypto.Release

/-- RFC 8439 quarter round as syntax, in the machine's operand order. -/
def qrS (a b c d : SExpr) : SExpr × SExpr × SExpr × SExpr :=
  let a := SExpr.add a b
  let d := SExpr.rotl (.xor d a) 16
  let c := SExpr.add c d
  let b := SExpr.rotl (.xor b c) 12
  let a := SExpr.add a b
  let d := SExpr.rotl (.xor d a) 8
  let c := SExpr.add c d
  let b := SExpr.rotl (.xor b c) 7
  (a, b, c, d)

def rotK : List (Reg × Word) := [(4, 16#32), (5, 20#32), (6, 24#32), (7, 25#32)]

abbrev coreS : SState := symExec ChaChaRound.core (SState.initK rotK)
abbrev qr0 := qrS (.reg0 0) (.reg0 1) (.reg0 2) (.reg0 3)

theorem core_norm0 : norm (coreS.regs 0) = qr0.1 := by decide
theorem core_norm1 : norm (coreS.regs 1) = qr0.2.1 := by decide
theorem core_norm2 : norm (coreS.regs 2) = qr0.2.2.1 := by decide
theorem core_norm3 : norm (coreS.regs 3) = qr0.2.2.2 := by decide

theorem core_regs_sym (s : State) (h : ChaChaRound.RotRegs s) :
    let s' := execAll ChaChaRound.core s
    (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
      quarterRound (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) := by
  have hk : ∀ p ∈ rotK, s.regs p.1 = p.2 := by
    obtain ⟨h4, h5, h6, h7⟩ := h
    simp [rotK, h4, h5, h6, h7]
  have e := fun r => execAll_regs_normK ChaChaRound.core (by decide) rotK s hk r
  simp only [e]
  rw [show (symExec ChaChaRound.core (SState.initK rotK)) = coreS from rfl, core_norm0, core_norm1,
    core_norm2, core_norm3]
  rfl

end M0Crypto.Sym
