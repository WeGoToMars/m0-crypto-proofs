import M0Crypto.Release.ConstantTime.SemStack
import M0Crypto.Thumb.Program

/-! Relational interpretation of the abstract-state components. -/
namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word State addWithCarry)
open M0Crypto.Thumb (CodeAt)

def regAt (s : State) (i : Nat) : Word := s.regs ⟨i % 16, Nat.mod_lt _ (by decide)⟩

def operand (s : State) : Opnd → Word
  | .reg i => regAt s i
  | .imm n => BitVec.ofNat 32 n

/-- Meaning of a recorded comparison in one run. -/
def CmpSem (c : Cmp) (s : State) : Prop :=
  let x := regAt s c.a
  let y := operand s c.b
  if c.zOnly then s.z = (x == y)
  else
    let (r, carry, overflow) := addWithCarry x (~~~y) true
    s.n = r.msb ∧ s.z = (r == 0) ∧ s.c = carry ∧ s.v = overflow

def FactSem (f : Fact) (s : State) : Prop :=
  let (i, j, strict) := f
  (regAt s i).toNat + (if strict then 1 else 0) ≤ (regAt s j).toNat

def LnkSem (p : Params) (l : Lnk) (s : State) : Prop :=
  regAt s l.i = p.sp0 + BitVec.ofInt 32 (l.c + l.k * (regAt s l.j).toNat)

/-- Relational abstract state at one program point. Call context is represented
through return labels in registers and stack slots. -/
structure LowEq (p : Params) (bytes : List (BitVec 8)) (off : Nat) (st : AbsState)
    (s₁ s₂ : State) : Prop where
  pc : s₁.pc = p.base + BitVec.ofNat 32 off
  pc_eq : s₂.pc = s₁.pc
  sp : s₁.regs 13 = p.sp0 + BitVec.ofInt 32 st.spOff
  sp_eq : s₂.regs 13 = s₁.regs 13
  regs : ∀ i, i < numRegs → i ≠ 13 → AbsVal.Sem p (st.get i) (regAt s₁ i) (regAt s₂ i)
  flags : FlagSem st.fl s₁ s₂
  comparison : ∀ c, st.fl.cmp = some c → CmpSem c s₁ ∧ CmpSem c s₂
  stack : StkSem p st.stk s₁.mem s₂.mem
  facts : ∀ f, f ∈ st.rel → FactSem f s₁ ∧ FactSem f s₂
  links : ∀ l, l ∈ st.lnk → LnkSem p l s₁ ∧ LnkSem p l s₂
  size : bytes.length = p.size
  code₁ : CodeAt s₁.mem p.base bytes
  code₂ : CodeAt s₂.mem p.base bytes

end M0Crypto.Release.ConstantTime
