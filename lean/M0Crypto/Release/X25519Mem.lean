import M0Crypto.Release.X25519Macros
import M0Crypto.Release.X25519Frame

set_option linter.unusedSimpArgs false

/-!
Per-instruction effects of the loads, stores and flag-preserving instructions of the X25519
field routines: registers away from the PC, memory, and the
carry flag. One lemma per instruction form, generic in the registers, the list and the
offset. `regs_ldm` gives a load-multiple by the index of the register in its list
(`List.idxOf`), so a concrete list needs only `listRegs l` evaluated.
-/

namespace M0Crypto.Release.X25519Mem
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32)
open M0Crypto.Thumb

theorem toReg0 : LowReg.toReg 0 = 0 := rfl
theorem toReg1 : LowReg.toReg 1 = 1 := rfl
theorem toReg2 : LowReg.toReg 2 = 2 := rfl
theorem toReg3 : LowReg.toReg 3 = 3 := rfl
theorem toReg4 : LowReg.toReg 4 = 4 := rfl
theorem toReg5 : LowReg.toReg 5 = 5 := rfl
theorem toReg6 : LowReg.toReg 6 = 6 := rfl
theorem toReg7 : LowReg.toReg 7 = 7 := rfl

theorem loadRegs_c (s : State) (a : Word) (rs : List Reg) : (loadRegs s a rs).c = s.c := by
  induction rs generalizing s a with
  | nil => rfl
  | cons r rs ih => simp only [loadRegs]; rw [ih]; rfl

theorem regs_loadRegs (s : State) (a : Word) :
    ∀ (rs : List Reg) (r : Reg), rs.Nodup →
      (loadRegs s a rs).regs r =
        if r ∈ rs then read32 s.mem (a + BitVec.ofNat 32 (4 * rs.idxOf r)) else s.regs r
  | [], r, _ => by simp [loadRegs]
  | x :: rs, r, hn => by
    rw [List.nodup_cons] at hn
    simp only [loadRegs]
    rw [regs_loadRegs _ _ rs r hn.2]
    by_cases hx : r = x
    · subst hx
      simp [hn.1, State.setReg, List.idxOf_cons_self]
    · have hxr : (x == r) = false := by simp [Ne.symm hx]
      by_cases hm : r ∈ rs
      · simp only [hm, ite_true, List.mem_cons, hx, false_or, List.idxOf_cons, hxr,
          Bool.cond_false]
        show read32 s.mem _ = _
        rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
        congr 3
        simp; omega
      · simp [hm, hx, State.setReg]

theorem regs_ldm (s : State) (n : LowReg) (l : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldm n l).next s).regs r =
      if r ∈ (listRegs l).map LowReg.toReg then
        read32 s.mem (s.reg n + BitVec.ofNat 32 (4 * ((listRegs l).map LowReg.toReg).idxOf r))
      else if r = n.toReg then s.reg n + BitVec.ofNat 32 (4 * bitCount l) else s.regs r := by
  have hnd : ((listRegs l).map LowReg.toReg).Nodup := by
    refine List.Pairwise.map _ (fun x y h e => h ?_) ((List.nodup_finRange 8).filter _)
    apply Fin.ext; have := congrArg Fin.val e; simpa [LowReg.toReg] using this
  have hlow : ∀ x : LowReg, (x.toReg = n.toReg) ↔ x = n := fun x =>
    ⟨fun e => Fin.ext (by have := congrArg Fin.val e; simpa [LowReg.toReg] using this),
     fun e => e ▸ rfl⟩
  have hnL : n.toReg ∈ (listRegs l).map LowReg.toReg ↔ l.getLsbD n.val = true := by
    simp only [List.mem_map, listRegs, List.mem_filter, List.mem_finRange, true_and, hlow]
    exact ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun h => ⟨n, h, rfl⟩⟩
  simp only [Instr.next, Instr.exec]
  by_cases hin : l.getLsbD n.val = true
  · simp only [hin, ite_true]
    rw [regs_loadRegs _ _ _ r hnd]
    by_cases hm : r ∈ (listRegs l).map LowReg.toReg
    · simp only [hm, ite_true]; rfl
    · have : r ≠ n.toReg := fun e => hm (e ▸ hnL.mpr hin)
      simp [hm, this, State.setReg, hr]
  · simp only [hin, Bool.false_eq_true, ite_false]
    by_cases e : r = n.toReg
    · subst e
      have : n.toReg ∉ (listRegs l).map LowReg.toReg := fun h => hin (hnL.mp h)
      simp [this, State.setReg]
    · rw [State.setReg]; simp only [e, ite_false]
      rw [regs_loadRegs _ _ _ r hnd]
      by_cases hm : r ∈ (listRegs l).map LowReg.toReg
      · simp only [hm, ite_true]; rfl
      · simp [hm, e, State.setReg, hr]

theorem mem_ldm (s : State) (n : LowReg) (l : BitVec 8) : ((Instr.ldm n l).next s).mem = s.mem := by
  simp only [Instr.next, Instr.exec]
  by_cases hin : l.getLsbD n.val = true <;>
    simp only [hin, ite_true, Bool.false_eq_true, ite_false] <;> simp [loadRegs_mem, State.setReg]

theorem c_ldm (s : State) (n : LowReg) (l : BitVec 8) : ((Instr.ldm n l).next s).c = s.c := by
  simp only [Instr.next, Instr.exec]
  by_cases hin : l.getLsbD n.val = true <;>
    simp only [hin, ite_true, Bool.false_eq_true, ite_false] <;> simp [loadRegs_c, State.setReg]

theorem regs_stm (s : State) (n : LowReg) (l : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.stm n l).next s).regs r =
      if r = n.toReg then s.reg n + BitVec.ofNat 32 (4 * bitCount l) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg, hr]

theorem mem_stm (s : State) (n : LowReg) (l : BitVec 8) :
    ((Instr.stm n l).next s).mem = storeWords s.mem (s.reg n) ((listRegs l).map s.reg) := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg]; rfl

theorem c_stm (s : State) (n : LowReg) (l : BitVec 8) : ((Instr.stm n l).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_ldrSp (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldrSp t i).next s).regs r =
      if r = t.toReg then read32 s.mem (s.sp + BitVec.ofNat 32 (i.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_ldrSp (s : State) (t : LowReg) (i : BitVec 8) : ((Instr.ldrSp t i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem c_ldrSp (s : State) (t : LowReg) (i : BitVec 8) : ((Instr.ldrSp t i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_addRdSp (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addRdSp d i).next s).regs r =
      if r = d.toReg then s.sp + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_addRdSp (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.addRdSp d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem c_addRdSp (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.addRdSp d i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_ldrImm (s : State) (t n : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memImm .ldr t n i).next s).regs r =
      if r = t.toReg then read32 s.mem (s.reg n + BitVec.ofNat 32 (i.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, State.setReg, hr]

theorem mem_ldrImm (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .ldr t n i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem c_ldrImm (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .ldr t n i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem regs_strImm (s : State) (t n : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memImm .str t n i).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, hr]

theorem mem_strImm (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .str t n i).next s).mem =
      write32 s.mem (s.reg n + BitVec.ofNat 32 (i.toNat * 4)) (s.reg t) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, State.setReg, State.reg, toReg_ne_15]

theorem c_eors (s : State) (d m : LowReg) : ((Instr.dp .eors d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem regs_mvns (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .mvns d m).next s).regs r = if r = d.toReg then ~~~(s.reg m) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem c_mvns (s : State) (d m : LowReg) : ((Instr.dp .mvns d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem c_muls (s : State) (d m : LowReg) : ((Instr.dp .muls d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem c_uxth (s : State) (d m : LowReg) : ((Instr.uxth d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_cmp (s : State) (n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .cmp n m).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, hr]

/-- `cmp r, r` sets the carry. -/
theorem c_cmp_self (s : State) (n : LowReg) : ((Instr.dp .cmp n n).next s).c = true := by
  have e := X25519Carry.adc_nat (s.reg n) (~~~(s.reg n)) true
  have := X25519Carry.carry_le (s.reg n) (~~~(s.reg n)) true
  have := (addWithCarry (s.reg n) (~~~(s.reg n)) true).1.isLt
  rw [BitVec.toNat_not] at e
  have := (s.reg n).isLt
  simp only [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setReg]
  cases h : (addWithCarry (s.reg n) (~~~(s.reg n)) true).2.1
  · rw [h] at e; simp at e; omega
  · rfl

theorem regs_subImm8 (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subImm8 d i).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (~~~(i.setWidth 32)) true).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, hr]

theorem regs_addImm8 (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addImm8 d i).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (i.setWidth 32) false).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, hr]

end M0Crypto.Release.X25519Mem
