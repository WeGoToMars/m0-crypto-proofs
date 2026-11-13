import M0Crypto.Sym.Core

/-!
# Symbolic executor: `Sound` for the ALU forms

`sound_dp` covers all eleven `DpOp`s; `sound_lslImm` and `sound_lsrImm` cover the immediate
shifts. Each proof unfolds `symStep`, `Instr.next` and `Instr.exec` down to the
denotations of `Core.lean`. Only the immediate shifts need a case split, on `imm5 = 0`,
which both `symStep` and `Thumb.lslC` / `Thumb.lsrC` branch on.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb

theorem denote_c (s0 : State) (ss : SState) : (ss.denote s0).c = ss.c.denote s0 := rfl

theorem denote_withC (s0 : State) (ss : SState) (b : SBool) :
    ({ ss with c := b } : SState).denote s0 = { ss.denote s0 with c := b.denote s0 } := rfl

local macro "sound_alu" : tactic => `(tactic|
  simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, SState.denote_setNZ,
    denote_sAddFlags, denote_withC, denote_c, denote_regs, denote_reg, SExpr.denote,
    SBool.denote, SState.reg, SState.sp, State.reg, State.sp, State.pc, State.setNZC,
    State.setNZCV])

theorem sound_dp (op : DpOp) (dn m : LowReg) : Sound (.dp op dn m) := by
  intro s0 ss
  cases op <;> sound_alu

theorem sound_lslImm (d m : LowReg) (imm5 : BitVec 5) : Sound (.lslImm d m imm5) := by
  intro s0 ss
  sound_alu
  by_cases h : imm5.toNat = 0 <;> simp only [h, Thumb.lslC, SExpr.denote, ↓reduceIte]

theorem sound_lsrImm (d m : LowReg) (imm5 : BitVec 5) : Sound (.lsrImm d m imm5) := by
  intro s0 ss
  sound_alu
  by_cases h : imm5.toNat = 0 <;> simp only [h, Thumb.lsrC, ↓reduceIte]

end M0Crypto.Sym
