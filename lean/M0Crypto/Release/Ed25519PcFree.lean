import M0Crypto.Thumb.Seq

set_option linter.unusedSimpArgs false

/-!
# Blocks that do not read the pc

`execAll_setPc`: a straight-line block of `pcFree` instructions run from `s` with its pc
replaced is the same run with its final pc replaced. A block that the generator cuts by a
literal pool (`b` over the pool, then the rest) therefore has the effect of the uncut block on
every register but the pc and on memory.
-/

namespace M0Crypto.Release.PcFree

open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb

/-- Instructions whose effect, apart from the pc, does not depend on the pc. -/
def pcFree : Instr → Bool
  | .lslImm .. | .lsrImm .. | .asrImm .. | .addReg .. | .subReg .. | .addImm3 .. | .subImm3 ..
  | .movImm .. | .cmpImm .. | .addImm8 .. | .subImm8 .. | .dp .. | .memReg .. | .memImm ..
  | .strSp .. | .ldrSp .. | .addRdSp .. | .rev .. | .uxth .. | .ldm .. | .stm .. => true
  | .movHi d m => d.val != 15 && m.val != 15
  | _ => false

theorem setReg_setReg_15 (s : State) (a b : Word) : (s.setReg 15 a).setReg 15 b = s.setReg 15 b := by
  simp only [State.setReg]; congr 1; funext i; split <;> rfl

theorem setReg_comm (s : State) (r : Reg) (hr : r ≠ 15) (a b : Word) :
    (s.setReg 15 a).setReg r b = (s.setReg r b).setReg 15 a := by
  simp only [State.setReg]; congr 1; funext i
  by_cases h1 : i = r <;> by_cases h2 : i = 15 <;> simp_all

theorem state_ext {A B : State} (h1 : ∀ r, A.regs r = B.regs r) (h2 : A.n = B.n) (h3 : A.z = B.z)
    (h4 : A.c = B.c) (h5 : A.v = B.v) (h6 : A.mem = B.mem) : A = B := by
  cases A; cases B; simp only at h2 h3 h4 h5 h6; subst h2 h3 h4 h5 h6
  congr; funext r; exact h1 r

theorem loadRegs_setPc : ∀ (s : State) (v a : Word) (rs : List Reg), (15 : Reg) ∉ rs →
    loadRegs (s.setReg 15 v) a rs = (loadRegs s a rs).setReg 15 v
  | _, _, _, [], _ => rfl
  | s, v, a, r :: rs, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [loadRegs]
    rw [show (s.setReg 15 v).mem = s.mem from rfl, setReg_comm _ _ (Ne.symm h.1),
      loadRegs_setPc _ _ _ _ h.2]

theorem toReg_lt (x : LowReg) : x.toReg.val < 8 := x.isLt

theorem next_setPc (i : Instr) (h : pcFree i = true) (s : State) (v : Word) :
    i.next (s.setReg 15 v) = (i.next s).setReg 15 (v + BitVec.ofNat 32 i.size) := by
  have l15 : ∀ x : LowReg, (x.toReg = 15) = False := fun x => eq_false (toReg_ne_15 x)
  have l15' : ∀ x : LowReg, ((15 : Reg) = x.toReg) = False := fun x => eq_false (Ne.symm (toReg_ne_15 x))
  cases i
  case ldm n l =>
    have hn : (15 : Reg) ∉ (listRegs l).map LowReg.toReg := by simp [toReg_ne_15]
    simp only [Instr.next, Instr.exec, State.pc, State.reg]
    have e1 : (s.setReg 15 v).regs n.toReg = s.regs n.toReg := by simp [State.setReg, l15]
    have e2 : (s.setReg 15 v).setReg 15 ((s.setReg 15 v).regs 15 + BitVec.ofNat 32 (Instr.ldm n l).size) =
        (s.setReg 15 (s.regs 15 + BitVec.ofNat 32 (Instr.ldm n l).size)).setReg 15
          (v + BitVec.ofNat 32 (Instr.ldm n l).size) := by
      simp only [setReg_setReg_15]; simp [State.setReg]
    rw [e1, e2, loadRegs_setPc _ _ _ _ hn]
    by_cases hl : l.getLsbD n.val = true
    · simp only [hl, ite_true]
    · simp only [hl, Bool.false_eq_true, ite_false, setReg_comm _ _ (toReg_ne_15 n)]
  case movHi d m =>
    simp only [pcFree, bne_iff_ne, ne_eq, Bool.and_eq_true] at h
    have hd : d ≠ 15 := fun e => h.1 (by rw [e]; rfl)
    have hm : m ≠ 15 := fun e => h.2 (by rw [e]; rfl)
    apply state_ext <;> (try intro r) <;> (try by_cases hr : r = 15) <;>
      simp [Instr.next, Instr.exec, State.setReg, State.pc, hd, hm, Ne.symm hd, *]
  case memReg op t n m =>
    cases op <;> apply state_ext <;> (try intro r) <;> (try by_cases hr : r = 15) <;>
      simp [Instr.next, Instr.exec, State.setReg, Instr.exec.memOp, State.reg, State.pc, l15, l15', *]
  case memImm op t n m =>
    cases op <;> apply state_ext <;> (try intro r) <;> (try by_cases hr : r = 15) <;>
      simp [Instr.next, Instr.exec, State.setReg, Instr.exec.memOp, State.reg, State.pc, l15, l15', *]
  case dp op d m =>
    cases op <;> apply state_ext <;> (try intro r) <;> (try by_cases hr : r = 15) <;>
      simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.setNZC, State.setNZCV, addFlags,
        State.reg, State.pc, l15, l15', *]
  all_goals simp only [pcFree, Bool.false_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true] at h
  all_goals apply state_ext <;> (try intro r) <;> (try by_cases hr : r = 15) <;>
    simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.setNZC, State.setNZCV, addFlags,
      Instr.exec.memOp, State.reg, State.sp, State.pc, l15, l15', *]

/-- **A block that does not read the pc**, run with its pc replaced. -/
theorem execAll_setPc : ∀ (is : List Instr) (s : State) (v : Word), is.all pcFree = true →
    execAll is (s.setReg 15 v) = (execAll is s).setReg 15 (v + BitVec.ofNat 32 (seqSize is))
  | [], s, v, _ => by simp [execAll, seqSize, setReg_setReg_15]
  | i :: is, s, v, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [execAll]
    rw [next_setPc i h.1, execAll_setPc is _ _ h.2, BitVec.add_assoc, ← BitVec.ofNat_add]
    simp [seqSize]

end M0Crypto.Release.PcFree
