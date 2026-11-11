import M0Crypto.Release.ConstantTime.StateSem
import M0Crypto.Release.ConstantTime.SemIndex

/-! Register-write facts used to relate concrete execution to abstract updates. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word Reg)

/-- Canonical numeric register access agrees with the corresponding architectural
register index. -/
theorem regAt_eq_regs (s : State) (r : Nat) (h : r < 16) :
    regAt s r = s.regs ⟨r, h⟩ := by
  simp [regAt, Nat.mod_eq_of_lt h]

/-- A concrete write leaves every different canonical register unchanged. -/
theorem regAt_setReg_ne (s : State) (r i : Nat) (hr : r < 16) (hi : i < 16)
    (hne : i ≠ r) (v : Word) :
    regAt (s.setReg ⟨r, hr⟩ v) i = regAt s i := by
  rw [regAt_eq_regs _ _ hi, regAt_eq_regs _ _ hi]
  simp [State.setReg, Fin.ext_iff, hne]

/-- A concrete write is visible through its canonical numeric register. -/
theorem regAt_setReg_self (s : State) (r : Nat) (hr : r < 16) (v : Word) :
    regAt (s.setReg ⟨r, hr⟩ v) r = v := by
  rw [regAt_eq_regs _ _ hr]
  simp [State.setReg]

/-- Facts that do not reference a written register retain their meaning. -/
theorem factSem_setReg {f : Fact} {s : State} {r : Nat} (hr : r < 16) (v : Word)
    (hf : factIndexOk f) (hi : f.1 ≠ r) (hj : f.2.1 ≠ r) :
    FactSem f (s.setReg ⟨r, hr⟩ v) ↔ FactSem f s := by
  rcases f with ⟨i, j, strict⟩
  have hi16 : i < 16 := by have := hf.1.1; simp [numRegs] at this; omega
  have hj16 : j < 16 := by have := hf.2.1; simp [numRegs] at this; omega
  simp only [FactSem, regAt_setReg_ne s r i hr hi16 hi,
    regAt_setReg_ne s r j hr hj16 hj]

/-- Affine links that do not reference a written register retain their meaning. -/
theorem lnkSem_setReg {p : Params} {l : Lnk} {s : State} {r : Nat}
    (hr : r < 16) (v : Word) (hl : linkIndexOk l) (hi : l.i ≠ r) (hj : l.j ≠ r) :
    LnkSem p l (s.setReg ⟨r, hr⟩ v) ↔ LnkSem p l s := by
  have hi16 : l.i < 16 := by have := hl.1.1; simp [numRegs] at this; omega
  have hj16 : l.j < 16 := by have := hl.2.1; simp [numRegs] at this; omega
  simp only [LnkSem, regAt_setReg_ne s r l.i hr hi16 hi,
    regAt_setReg_ne s r l.j hr hj16 hj]

/-- A comparison record unaffected by a register write remains valid. -/
theorem cmpSem_setReg {c : Cmp} {s : State} {r : Nat} (hr : r < 16) (v : Word)
    (hc : cmpIndexOk c) (huses : c.uses r = false) :
    CmpSem c (s.setReg ⟨r, hr⟩ v) ↔ CmpSem c s := by
  have hn : c.a ≠ r := by
    simp [Cmp.uses] at huses
    exact huses.1
  have hi16 : c.a < 16 := by have := hc.1.1; simp [numRegs] at this; omega
  have hop : operand (s.setReg ⟨r, hr⟩ v) c.b = operand s c.b := by
    cases ho : c.b with
    | imm n => rfl
    | reg j =>
      have hj : j ≠ r := by
        simp [Cmp.uses] at huses
        simpa [ho] using huses.2
      have hjok : regIndexOk j := by simpa [ho, opndIndexOk] using hc.2
      have hj16 : j < 16 := by have := hjok.1; simp [numRegs] at this; omega
      simp [operand, ho, regAt_setReg_ne s r j hr hj16 hj]
  simp only [CmpSem, regAt_setReg_ne s r c.a hr hi16 hn, hop]
  rfl

end M0Crypto.Release.ConstantTime
