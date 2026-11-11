import M0Crypto.Release.ConstantTime.Transfer
import M0Crypto.Release.ConstantTime.Sem
import M0Crypto.Thumb.Exec

/-! Public condition flags produce identical branch decisions. -/
namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State)
open M0Crypto.Thumb (condPassed)

theorem AbsFlags.sem_public {a : AbsFlags} {x y : Bool} (h : AbsFlags.Sem a x y)
    (hp : a.pub = true) : x = y := by
  cases a <;> simp_all [AbsFlags.Sem, AbsFlags.pub]

/-- A condition whose tested flags are public evaluates identically in both runs. -/
theorem condFlagsPub_sound (cond : BitVec 4) (f : AFl) (s₁ s₂ : State)
    (hf : FlagSem f s₁ s₂) (hp : condFlagsPub cond.toNat f = true) :
    condPassed cond s₁ = condPassed cond s₂ := by
  have hn : f.n.pub = true → s₁.n = s₂.n := AbsFlags.sem_public hf.1
  have hz : f.z.pub = true → s₁.z = s₂.z := AbsFlags.sem_public hf.2.1
  have hc : f.c.pub = true → s₁.c = s₂.c := AbsFlags.sem_public hf.2.2.1
  have hv : f.v.pub = true → s₁.v = s₂.v := AbsFlags.sem_public hf.2.2.2
  have hh : cond.toNat = 0 ∨ cond.toNat = 1 ∨ cond.toNat = 2 ∨ cond.toNat = 3 ∨
      cond.toNat = 4 ∨ cond.toNat = 5 ∨ cond.toNat = 6 ∨ cond.toNat = 7 ∨
      cond.toNat = 8 ∨ cond.toNat = 9 ∨ cond.toNat = 10 ∨ cond.toNat = 11 ∨
      cond.toNat = 12 ∨ cond.toNat = 13 ∨ cond.toNat = 14 ∨ cond.toNat = 15 := by
    have hb := cond.isLt
    omega
  rcases hh with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [condFlagsPub, condPassed, Bool.and_eq_true]

end M0Crypto.Release.ConstantTime
