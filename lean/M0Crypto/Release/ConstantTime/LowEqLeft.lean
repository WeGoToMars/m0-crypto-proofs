import M0Crypto.Release.ConstantTime.StateSem

/-!
# The left projection of the relational state

Every interpretation in `ConstantTime.Sem` constrains each run separately or states an equality, so a
related pair `(x, y)` also relates `x` to itself. A premise about the first run that is
proved for a state paired with itself therefore applies to the first state of any related pair.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)

theorem AbsVal.sem_left {p : Params} {v : AbsVal} {x y : Word} (h : AbsVal.Sem p v x y) : AbsVal.Sem p v x x := by
  cases v with
  | hi => trivial
  | lo => rfl
  | num a b => exact ⟨rfl, h.2⟩
  | sp a b =>
    obtain ⟨k, h1, h2, h3, _⟩ := h
    exact ⟨k, h1, h2, h3, rfl⟩
  | ret r => exact ⟨h.1, rfl⟩
  | lr0 => exact ⟨h.1, rfl⟩

theorem AbsFlags.sem_left {a : AbsFlags} {x y : Bool} (h : AbsFlags.Sem a x y) : AbsFlags.Sem a x x := by
  cases a with
  | hi => trivial
  | lo => rfl
  | known b => exact ⟨h.1, h.1⟩

theorem FlagSem.left {fl : AFl} {s₁ s₂ : State} (h : FlagSem fl s₁ s₂) : FlagSem fl s₁ s₁ :=
  ⟨AbsFlags.sem_left h.1, AbsFlags.sem_left h.2.1, AbsFlags.sem_left h.2.2.1, AbsFlags.sem_left h.2.2.2⟩

theorem StkSem.left {p : Params} {stk : Stk} {m₁ m₂ : M0Crypto.Armv6M.Mem}
    (h : StkSem p stk m₁ m₂) : StkSem p stk m₁ m₁ :=
  fun o => AbsVal.sem_left (h o)

/-- A related pair relates its first state to itself. -/
theorem LowEq.left {p : Params} {bytes : List (BitVec 8)} {off : Nat} {st : AbsState} {x y : State}
    (h : LowEq p bytes off st x y) : LowEq p bytes off st x x where
  pc := h.pc
  pc_eq := rfl
  sp := h.sp
  sp_eq := rfl
  regs i hi hne := AbsVal.sem_left (h.regs i hi hne)
  flags := h.flags.left
  comparison c hc := ⟨(h.comparison c hc).1, (h.comparison c hc).1⟩
  stack := h.stack.left
  facts f hf := ⟨(h.facts f hf).1, (h.facts f hf).1⟩
  links l hl := ⟨(h.links l hl).1, (h.links l hl).1⟩
  size := h.size
  code₁ := h.code₁
  code₂ := h.code₁

end M0Crypto.Release.ConstantTime
