import M0Crypto.Release.ConstantTime.BranchSound

/-! Soundness of known conditional-branch decisions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb (condPassed)

private theorem knownB_value {a : AbsFlags} {x y : Bool} (h : AbsFlags.Sem a x y) :
    knownB a = none ∨ knownB a = some x ∧ x = y := by
  cases a <;> simp_all [knownB, AbsFlags.Sem]

/-- A known branch condition agrees with the decision in both executions. -/
theorem evalCond_sound (cond : BitVec 4) (f : AFl) (s₁ s₂ : State) (v : Bool)
    (hf : FlagSem f s₁ s₂) (he : evalCond cond.toNat f = some v) :
    condPassed cond s₁ = v ∧ condPassed cond s₂ = v := by
  have hn := knownB_value hf.1
  have hz := knownB_value hf.2.1
  have hc := knownB_value hf.2.2.1
  have hv := knownB_value hf.2.2.2
  have hh : cond.toNat = 0 ∨ cond.toNat = 1 ∨ cond.toNat = 2 ∨ cond.toNat = 3 ∨
      cond.toNat = 4 ∨ cond.toNat = 5 ∨ cond.toNat = 6 ∨ cond.toNat = 7 ∨
      cond.toNat = 8 ∨ cond.toNat = 9 ∨ cond.toNat = 10 ∨ cond.toNat = 11 ∨
      cond.toNat = 12 ∨ cond.toNat = 13 ∨ cond.toNat = 14 ∨ cond.toNat = 15 := by
    have hb := cond.isLt
    omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases hn with hn | ⟨hn, hne⟩ <;>
    rcases hz with hz | ⟨hz, hze⟩ <;>
    rcases hc with hc | ⟨hc, hce⟩ <;>
    rcases hv with hv | ⟨hv, hve⟩ <;>
    simp_all [evalCond, condPassed]

end M0Crypto.Release.ConstantTime
