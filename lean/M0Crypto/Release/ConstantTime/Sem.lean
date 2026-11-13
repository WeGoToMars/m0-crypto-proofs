import M0Crypto.Release.ConstantTime.Domain
import M0Crypto.Armv6M.Memory

/-! Concrete interpretation of the relational abstract values used by the analysis.
The certificate generator is untrusted; these definitions are for its soundness proof. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word)

structure Params where
  base : Word
  sp0 : Word
  lr0 : Word
  size : Nat

namespace AbsVal

def Sem (p : Params) : AbsVal → Word → Word → Prop
  | .hi, _, _ => True
  | .lo, x, y => x = y
  | .num a b, x, y => x = y ∧ a ≤ x.toNat ∧ x.toNat ≤ b
  | .sp a b, x, y => ∃ k : Int, a ≤ k ∧ k ≤ b ∧
      x = p.sp0 + BitVec.ofInt 32 k ∧ y = x
  | .ret rs, x, y => (∃ r ∈ rs, x = (p.base + BitVec.ofNat 32 r) ||| 1#32) ∧ y = x
  | .lr0, x, y => x = p.lr0 ∧ y = x

theorem sem_public {p : Params} {v : AbsVal} {x y : Word}
    (h : Sem p v x y) (hp : v.pub = true) : x = y := by
  cases v <;> simp_all [Sem, pub]
  case sp => obtain ⟨_, _, _, _, h⟩ := h; exact h.symm

end AbsVal

namespace AbsFlags

/-- Interpretation of a flag label for two executions. -/
def Sem : AbsFlags → Bool → Bool → Prop
  | .hi, _, _ => True
  | .lo, x, y => x = y
  | .known b, x, y => x = b ∧ y = b

theorem le_sem {a b : AbsFlags} {x y : Bool} (h : Sem a x y)
    (hle : a.le b = true) : Sem b x y := by
  cases a <;> cases b <;> simp_all [Sem, le, beq_iff_eq]

theorem join_left {a b : AbsFlags} {x y : Bool} (h : Sem a x y) :
    Sem (a.join b) x y := by
  cases a with
  | hi => simp [join, Sem]
  | lo => cases b <;> simp_all [join, Sem]
  | known v => cases b with
    | hi => simp [join, Sem]
    | lo => simp_all [join, Sem]
    | known w => cases v <;> cases w <;> simp_all [join, Sem]

theorem join_right {a b : AbsFlags} {x y : Bool} (h : Sem b x y) :
    Sem (a.join b) x y := by
  cases b with
  | hi => cases a <;> simp [join, Sem]
  | lo => cases a <;> simp_all [join, Sem]
  | known v => cases a with
    | hi => simp [join, Sem]
    | lo => simp_all [join, Sem]
    | known w => cases v <;> cases w <;> simp_all [join, Sem]

end AbsFlags
/-- The four labels constrain the corresponding flags in both executions. The
comparison record has a separate interpretation because it refers to registers. -/
def FlagSem (fl : AFl) (s₁ s₂ : M0Crypto.Armv6M.State) : Prop :=
  AbsFlags.Sem fl.n s₁.n s₂.n ∧ AbsFlags.Sem fl.z s₁.z s₂.z ∧
  AbsFlags.Sem fl.c s₁.c s₂.c ∧ AbsFlags.Sem fl.v s₁.v s₂.v

/-- Each recorded stack slot describes the two words at that offset. Missing slots
    are secret and impose no constraint. -/
def StkSem (p : Params) (stk : Stk) (m₁ m₂ : M0Crypto.Armv6M.Mem) : Prop :=
  ∀ o : Int, AbsVal.Sem p (stkGet stk o)
    (M0Crypto.Armv6M.read32 m₁ (p.sp0 + BitVec.ofInt 32 o))
    (M0Crypto.Armv6M.read32 m₂ (p.sp0 + BitVec.ofInt 32 o))

end M0Crypto.Release.ConstantTime
