import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.InstructionCases
import M0Crypto.Release.ConstantTime.BufferSeparation
import M0Crypto.Release.RunStates

/-! Functional write guarantees for recorded executions. -/
set_option maxRecDepth 100000
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release

/-- Successful executions from the same state and stop PC have the same
result, regardless of their fuel allowances. -/
theorem runUntil_success_unique {stop : Word} {n m : Nat} {s t₁ t₂ : State}
    {tr₁ tr₂ : List Event} (h₁ : runUntil stop n s = .ok (t₁, tr₁))
    (h₂ : runUntil stop m s = .ok (t₂, tr₂)) : t₁ = t₂ ∧ tr₁ = tr₂ := by
  induction n generalizing m s t₁ t₂ tr₁ tr₂ with
  | zero =>
    by_cases hpc : s.pc = stop
    · cases m <;> simp [runUntil, hpc] at h₁ h₂ <;>
        exact ⟨h₁.1.symm.trans h₂.1, h₁.2.trans h₂.2.symm⟩
    · simp [runUntil, hpc] at h₁
  | succ n ih =>
    by_cases hpc : s.pc = stop
    · cases m <;> simp [runUntil, hpc] at h₁ h₂ <;>
        exact ⟨h₁.1.symm.trans h₂.1, h₁.2.trans h₂.2.symm⟩
    · cases m with
      | zero => simp [runUntil, hpc] at h₂
      | succ m =>
        simp only [runUntil, hpc, ↓reduceIte] at h₁ h₂
        cases hs : step s with
        | error err => simp [hs] at h₁
        | ok pair =>
          obtain ⟨next, event⟩ := pair
          simp only [hs] at h₁ h₂
          cases hr₁ : runUntil stop n next with
          | error err => simp [hr₁] at h₁
          | ok pair₁ =>
            obtain ⟨last₁, tail₁⟩ := pair₁
            simp only [hr₁, Except.ok.injEq, Prod.mk.injEq] at h₁
            cases hr₂ : runUntil stop m next with
            | error err => simp [hr₂] at h₂
            | ok pair₂ =>
              obtain ⟨last₂, tail₂⟩ := pair₂
              simp only [hr₂, Except.ok.injEq, Prod.mk.injEq] at h₂
              obtain ⟨hlast, htail⟩ := ih hr₁ hr₂
              constructor
              · exact h₁.1.symm.trans (hlast.trans h₂.1)
              · exact h₁.2.symm.trans (congrArg (List.cons event) htail |>.trans h₂.2)

/-- The single-register stores whose address is not represented as a stack
offset by the abstract state. -/
def untrackedStore (st : AbsState) : Instr → Bool
  | .memImm op _ n imm => !op.isLoad && !((st.get n.val).addK (imm.toNat * op.width)).isSp
  | .memReg op _ n m => !op.isLoad && !((st.get n.val).add (st.get m.val)).isSp
  | _ => false

end M0Crypto.Release.ConstantTime
