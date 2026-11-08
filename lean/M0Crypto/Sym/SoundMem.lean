import M0Crypto.Sym.SoundAlu

/-!
# Approach C, task H3 (part A): `Sound` for the memory and stack forms

`sound_ldrLit`, `sound_ldrSp`, `sound_strSp`, `sound_memImm`, `sound_memReg` cover the
single loads and stores; `sound_push`, `sound_pop` (PC bit clear), `sound_stm`,
`sound_ldm` cover the multiple transfers. `sound_of_falls` combines them with
`sound_basic`, `sound_dp`, `sound_lslImm` and `sound_lsrImm` into the statement that
every straight-line instruction is mirrored soundly.

Each per-form proof unfolds `symStep` and `Instr.exec` down to the denotations of
`Core.lean`. The two helpers that carry the work are `denote_sMemOp` (the single-access
dispatch, shared by the immediate and register forms) and `denote_sStoreWords` /
`denote_sLoadRegs` from `Core.lean` (the multiple transfers).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb

theorem denote_mem (s0 : State) (ss : SState) : (ss.denote s0).mem = ss.mem.denote s0 := rfl

theorem denote_withMem (s0 : State) (ss : SState) (m : SMem) :
    ({ ss with mem := m } : SState).denote s0 = { ss.denote s0 with mem := m.denote s0 } := rfl

/-- The register list of a multiple transfer, read through `SState.reg` and denoted,
is the list of the same registers read from the denoted state. -/
theorem denote_listRegs (s0 : State) (ss : SState) (l : BitVec 8) :
    ((listRegs l).map (fun x => ss.reg x)).map (SExpr.denote s0) =
      (listRegs l).map (fun x => (ss.denote s0).reg x) := by
  rw [List.map_map]
  rfl

/-- The single-access dispatch of `symStep`, against the one of `Instr.exec`. -/
theorem denote_sMemOp (s0 : State) (next : SState) (op : MemOp) (t : LowReg) (a : SExpr) :
    (symStep.sMemOp next op t a).denote s0 = Instr.exec.memOp (next.denote s0) op t (a.denote s0) := by
  cases op <;> simp only [symStep.sMemOp, Instr.exec.memOp, SState.denote_setReg, denote_withMem,
    denote_mem, denote_reg, SMem.denote, SExpr.denote]

/-! ## Single loads and stores -/

theorem sound_ldrLit (t : LowReg) (imm8 : BitVec 8) : Sound (.ldrLit t imm8) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, denote_regs, denote_mem,
    SExpr.denote, State.pc]

theorem sound_ldrSp (t : LowReg) (imm8 : BitVec 8) : Sound (.ldrSp t imm8) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, denote_regs, denote_mem,
    SExpr.denote, SState.sp, State.sp, State.pc]

theorem sound_strSp (t : LowReg) (imm8 : BitVec 8) : Sound (.strSp t imm8) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, denote_withMem, denote_regs,
    denote_reg, denote_mem, SExpr.denote, SMem.denote, SState.sp, State.sp, State.pc]

theorem sound_memImm (op : MemOp) (t n : LowReg) (imm5 : BitVec 5) : Sound (.memImm op t n imm5) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, denote_sMemOp, SState.denote_setReg, denote_regs,
    denote_reg, SExpr.denote, State.pc]

theorem sound_memReg (op : MemOp) (t n m : LowReg) : Sound (.memReg op t n m) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, denote_sMemOp, SState.denote_setReg, denote_regs,
    denote_reg, SExpr.denote, State.pc]

/-! ## Multiple transfers -/

theorem sound_push (l : BitVec 8) (lr : Bool) : Sound (.push l lr) := by
  intro s0 ss
  cases lr <;> simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, denote_withMem,
    denote_sStoreWords, denote_listRegs, denote_regs, denote_reg, denote_mem, SExpr.denote,
    SState.sp, State.sp, State.pc, List.map_append, List.map_cons, List.map_nil, List.append_nil,
    Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte]

theorem sound_pop (l : BitVec 8) : Sound (.pop l false) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, denote_sLoadRegs, SState.denote_setReg, denote_regs,
    SExpr.denote, SState.sp, State.sp, State.pc, Bool.toNat_false, Nat.add_zero,
    Bool.false_eq_true, ↓reduceIte]

theorem sound_stm (n : LowReg) (l : BitVec 8) : Sound (.stm n l) := by
  intro s0 ss
  simp only [symStep, Instr.next, Instr.exec, denote_withMem, SState.denote_setReg,
    denote_sStoreWords, denote_listRegs, denote_regs, denote_reg, denote_mem, SExpr.denote,
    State.pc]

theorem sound_ldm (n : LowReg) (l : BitVec 8) : Sound (.ldm n l) := by
  intro s0 ss
  cases hb : l.getLsbD n.val <;>
    simp only [symStep, Instr.next, Instr.exec, denote_sLoadRegs, SState.denote_setReg,
      denote_regs, denote_reg, SExpr.denote, State.pc, hb, Bool.false_eq_true, ↓reduceIte]

/-! ## Every straight-line instruction -/

/-- Every instruction that falls through is mirrored soundly. -/
theorem sound_of_falls (i : Instr) (h : i.falls = true) : Sound i := by
  cases i with
  | lslImm d m imm5 => exact sound_lslImm d m imm5
  | lsrImm d m imm5 => exact sound_lsrImm d m imm5
  | addReg d n m => exact sound_basic _ rfl
  | subReg d n m => exact sound_basic _ rfl
  | addImm3 d n imm3 => exact sound_basic _ rfl
  | subImm3 d n imm3 => exact sound_basic _ rfl
  | movImm d imm8 => exact sound_basic _ rfl
  | cmpImm n imm8 => exact sound_basic _ rfl
  | addImm8 dn imm8 => exact sound_basic _ rfl
  | subImm8 dn imm8 => exact sound_basic _ rfl
  | dp op dn m => exact sound_dp op dn m
  | movHi d m => exact sound_basic _ h
  | ldrLit t imm8 => exact sound_ldrLit t imm8
  | memReg op t n m => exact sound_memReg op t n m
  | memImm op t n imm5 => exact sound_memImm op t n imm5
  | strSp t imm8 => exact sound_strSp t imm8
  | ldrSp t imm8 => exact sound_ldrSp t imm8
  | addRdSp d imm8 => exact sound_basic _ rfl
  | addSp imm7 => exact sound_basic _ rfl
  | subSp imm7 => exact sound_basic _ rfl
  | uxth d m => exact sound_basic _ rfl
  | push l lr => exact sound_push l lr
  | pop l pc =>
    cases pc
    · exact sound_pop l
    · simp [Instr.falls] at h
  | stm n l => exact sound_stm n l
  | ldm n l => exact sound_ldm n l
  | bcond cond imm8 => simp [Instr.falls] at h
  | b imm11 => simp [Instr.falls] at h
  | bl imm25 => simp [Instr.falls] at h

end M0Crypto.Sym
