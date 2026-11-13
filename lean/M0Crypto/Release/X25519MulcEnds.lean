import M0Crypto.Release.X25519MulcStep

set_option linter.unusedSimpArgs false

/-!
The straight-line pieces of `m0c_fe_mulc_add` around the chain, each as a `ReachW` block lemma:

* `pre`: `push {lr}; mov r12, r0; ldr r7, =60833; movs r6, #0` (`pre_run_w`; the literal's
  value is left as a read of the code word, which the routine proof evaluates);
* `fold`: after word 7, `q = 2 * hi + bit 31 of lo` times 19 into `r3`, and `lo mod 2^31`
  into `r8` (`fold_run_w`);
* `fin`: `r8 + k` stored at word 7 of `r12` (`fin_run_w`);
* `pop {pc}` (`pop_run_w`).

`feMulcAddList_split` cuts the routine's list into these pieces and the macro calls.
-/

namespace M0Crypto.Release.X25519MulcEnds
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion)
open M0Crypto.Release.X25519Mem (regs_strImm mem_strImm)
open M0Crypto.Release.InstrNext (regs_movHi regs_movImm)
open M0Crypto.Release.X25519Mul (regs_lsr regs_lsl regs_muls regs_adds toReg_inj)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519MulcWord (mem_dp mem_lsl mem_lsr mem_adds)
open M0Crypto.Release.X25519MulcStep (sAddr)
open M0Crypto.Release.X25519Macros (mulcWord mulcStep feMulcAddList)
open M0Crypto.Release.X25519Carry (adc_nat)

def pre2 : List Instr := [.push 0 true, .movHi 12 0]
def pre (lit : BitVec 8) : List Instr := pre2 ++ [.ldrLit 7 lit, .movImm 6 0]
def fold : List Instr :=
  [.lslImm 3 3 1, .lsrImm 5 4 31, .addReg 3 3 5, .lslImm 4 4 1, .lsrImm 4 4 1, .movHi 8 4,
   .movImm 5 19, .dp .muls 3 5]
def fin : List Instr := [.movHi 1 8, .addReg 1 1 0, .movHi 0 12, .memImm .str 1 0 7]

theorem feMulcAddList_split (lit : BitVec 8) :
    feMulcAddList lit = pre lit ++ mulcWord 7 none 3 4 5 ++ fold ++ mulcStep 0 3 0 ++
      mulcStep 1 0 3 ++ mulcStep 2 3 0 ++ mulcStep 3 0 3 ++ mulcStep 4 3 0 ++ mulcStep 5 0 3 ++
      mulcStep 6 3 0 ++ fin ++ [.pop 0 true] := by
  simp only [feMulcAddList, pre, pre2, fin, fold, List.append_assoc, List.cons_append,
    List.nil_append]

theorem mem_ldrLit (s : State) (t : LowReg) (i : BitVec 8) : ((Instr.ldrLit t i).next s).mem = s.mem :=
  next_mem rfl s

theorem regs_ldrLit (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldrLit t i).next s).regs r =
      if r = t.toReg then read32 s.mem (((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (i.toNat * 4))
      else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_movHi (s : State) (d m : Reg) : ((Instr.movHi d m).next s).mem = s.mem := next_mem rfl s
theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem :=
  next_mem rfl s

/-! ## `pre` -/

theorem pre2_exec (s : State) :
    let s' := execAll pre2 s
    s'.mem = storeWords s.mem (s.regs 13 - 4#32) [s.regs 14] ∧ s'.regs 13 = s.regs 13 - 4#32 ∧
      s'.regs 12 = s.regs 0 ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 13 → r ≠ 12 → s'.regs r = s.regs r := by
  intro s'
  have hb : bitCount (0 : BitVec 8) = 0 := by decide
  have hl : listRegs (0 : BitVec 8) = [] := by decide
  have hb0' : bitCount 0#8 = 0 := by decide
  have hl' : listRegs 0#8 = [] := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [s', pre2, execAll, mem_movHi]
    simp [Instr.next, Instr.exec, State.setReg, State.sp, hb, hl]; rfl
  · simp (config := {decide := true}) only [s', pre2, execAll, regs_movHi, ite_false, ne_eq]
    simp [Instr.next, Instr.exec, State.setReg, State.sp, hb]; rfl
  · simp (config := {decide := true}) only [s', pre2, execAll, regs_movHi, ite_true, ne_eq]
    simp [Instr.next, Instr.exec, State.setReg]
  · intro r h15 h13 h12
    simp only [s', pre2, execAll, regs_movHi _ _ _ _ h15, h12, ite_false]
    simp [Instr.next, Instr.exec, State.setReg, h15, h13]

theorem pre_falls (lit : BitVec 8) : (pre lit).all Instr.falls = true := by
  simp [pre, pre2, Instr.falls]; decide

theorem pre2_falls : pre2.all Instr.falls = true := by
  simp [pre2, Instr.falls]; decide

/-- `pre` in a `ReachW` proof. `L` is the literal's address; the routine proof reads the
literal from the code. -/
theorem pre_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off : Nat} {lit : BitVec 8} (hseq : seqAt B off (pre lit) = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize (pre lit)))
    (hsp : (x.regs 13).toNat % 4 = 0) (hW : ∀ q < 4, Wr (x.regs 13 - 4#32 + BitVec.ofNat 32 q))
    (hL : ((((base + BitVec.ofNat 32 (off + seqSize pre2)) + 4#32) &&& ~~~3#32) +
      BitVec.ofNat 32 (lit.toNat * 4)).toNat % 4 = 0) {Q : State → Prop}
    (cont : ∀ y : State, y.pc = base + BitVec.ofNat 32 (off + seqSize (pre lit)) →
      y.mem = storeWords x.mem (x.regs 13 - 4#32) [x.regs 14] →
      y.regs 13 = x.regs 13 - 4#32 → y.regs 12 = x.regs 0 → y.reg 6 = 0#32 →
      y.reg 7 = read32 (storeWords x.mem (x.regs 13 - 4#32) [x.regs 14])
        ((((base + BitVec.ofNat 32 (off + seqSize pre2)) + 4#32) &&& ~~~3#32) +
          BitVec.ofNat 32 (lit.toNat * 4)) →
      (∀ r : Reg, r ≠ 15 → r ≠ 13 → r ≠ 12 → r ≠ 6 → r ≠ 7 → y.regs r = x.regs r) →
      ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  have hf := pre_falls lit
  obtain ⟨m2, r13, r12, ro⟩ := pre2_exec x
  have pc2 := execAll_pc pre2 x pre2_falls
  have hpre : pre lit = pre2 ++ [.ldrLit 7 lit, .movImm 6 0] := rfl
  refine ReachW.blockAcc hb _ off hpc ho hseq hf ?_ hr ?_
  · rw [hpre]
    refine accAll_append ?_ ?_
    · refine accAll_cons ?_ (accAll_cons (fun a ha => by simp [Instr.accesses] at ha) (accAll_nil _ _))
      have hb0 : bitCount (0 : BitVec 8) = 0 := by decide
      intro a ha
      simp only [Instr.accesses, hb0, Bool.toNat_true, Nat.zero_add, State.sp] at ha
      refine wordAccesses_ok ?_ (fun _ i hi q hq => ?_) a ha
      · have := x.regs 13 |>.isLt
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · have : i = 0 := by omega
        subst this
        simpa using hW q hq
    · refine accAll_cons (fun a ha => ?_) (accAll_cons (fun a ha => by simp [Instr.accesses] at ha)
        (accAll_nil _ _))
      simp only [Instr.accesses, List.mem_singleton] at ha
      subst ha
      rw [pc2, hpc, ofNat_add_assoc base off (seqSize pre2)]
      exact ⟨by simp only [Access.aligned, hL, beq_self_eq_true], fun e => by cases e⟩
  · rw [hpre, execAll_append]
    generalize hx2 : execAll pre2 x = x2 at m2 r13 r12 ro pc2
    refine cont _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← hx2, ← execAll_append, ← hpre, execAll_pc _ _ hf, hpc, ofNat_add_assoc]
    · simp only [execAll, mem_movImm, mem_ldrLit, m2]
    · simp (config := {decide := true}) only [execAll, regs_movImm, regs_ldrLit, ne_eq, ite_false, r13]
    · simp (config := {decide := true}) only [execAll, regs_movImm, regs_ldrLit, ne_eq, ite_false, r12]
    · simp (config := {decide := true}) only [execAll, State.reg, regs_movImm, ne_eq, ite_true,
        X25519Mem.toReg6]
    · simp (config := {decide := true}) only [execAll, State.reg, regs_movImm, regs_ldrLit, ne_eq,
        ite_true, ite_false, X25519Mem.toReg6, X25519Mem.toReg7, mem_movImm, pc2, hpc, m2,
        ofNat_add_assoc]
    · intro r h15 h13 h12 h6 h7
      simp only [execAll, regs_movImm _ _ _ _ h15, regs_ldrLit _ _ _ _ h15, X25519Mem.toReg6,
        X25519Mem.toReg7, h6, h7, ite_false, ro r h15 h13 h12]

/-! ## `fold` -/

open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg3 toReg4 toReg5) in
theorem fold_exec (s : State) (hh : (s.reg 3).toNat < 2 ^ 26) :
    let s' := execAll fold s
    (s'.reg 3).toNat = 19 * (2 * (s.reg 3).toNat + (s.reg 4).toNat / 2 ^ 31) ∧
      (s'.regs 8).toNat = (s.reg 4).toNat % 2 ^ 31 ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 8 → s'.regs r = s.regs r := by
  intro s'
  have k1 : (1 : BitVec 5).toNat = 1 := rfl
  have k31 : (31 : BitVec 5).toNat = 31 := rfl
  have k19 : (19 : BitVec 8).setWidth 32 = 19#32 := rfl
  have kw : (19#32 : Word).toNat = 19 := rfl
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [fold, Instr.writesMem])
  refine ⟨?_, ?_, hm, ?_⟩
  · simp (config := {decide := true}) only [s', fold, execAll, State.reg, regs_lsl, regs_lsr,
      regs_adds, regs_movHi, regs_movImm, regs_muls, toReg3, toReg4, toReg5, ite_true, ite_false,
      ne_eq, not_false_eq_true]
    simp only [State.reg, toReg3, toReg4] at hh
    simp only [k1, k31, k19, kw] at *
    generalize s.regs 3 = H at *
    generalize s.regs 4 = L at *
    have e := adc_nat (H <<< 1) (L >>> 31) false
    generalize addWithCarry (H <<< 1) (L >>> 31) false = Z at *
    have := L.isLt
    simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Bool.toNat_false, Nat.add_zero, kw, BitVec.toNat_ofNat, Nat.reduceMod] at e ⊢
    omega
  · simp (config := {decide := true}) only [s', fold, execAll, State.reg, regs_lsl, regs_lsr,
      regs_adds, regs_movHi, regs_movImm, regs_muls, toReg3, toReg4, toReg5, ite_true, ite_false,
      ne_eq, not_false_eq_true]
    have := (s.regs 4).isLt
    simp only [k1, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  · intro r h15 h3 h4 h5 h8
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have v : ∀ n : Reg, r ≠ n → r.val ≠ n.val := fun n h e => h (Fin.ext e)
      have v3 : r.val ≠ 3 := v 3 h3
      have v4 : r.val ≠ 4 := v 4 h4
      have v5 : r.val ≠ 5 := v 5 h5
      have v8 : r.val ≠ 8 := v 8 h8
      have l3 : ((3 : LowReg) : Nat) = 3 := rfl
      have l4 : ((4 : LowReg) : Nat) = 4 := rfl
      have l5 : ((5 : LowReg) : Nat) = 5 := rfl
      have l8 : ((8 : Reg) : Nat) = 8 := rfl
      simp [fold, Instr.dsts, l3, l4, l5, l8, v3, v4, v5, v8])

theorem fold_falls : fold.all Instr.falls = true := by simp [fold, Instr.falls]; decide

theorem fold_regOnly : fold.all X25519Mul.regOnly = true := by simp [fold, X25519Mul.regOnly]

theorem fold_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off : Nat} (hseq : seqAt B off fold = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize fold))
    (hh : (x.reg 3).toNat < 2 ^ 26) {Q : State → Prop}
    (cont : ∀ y : State, y.pc = base + BitVec.ofNat 32 (off + seqSize fold) →
      (y.reg 3).toNat = 19 * (2 * (x.reg 3).toNat + (x.reg 4).toNat / 2 ^ 31) →
      (y.regs 8).toNat = (x.reg 4).toNat % 2 ^ 31 → y.mem = x.mem →
      (∀ r : Reg, r ≠ 15 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 8 → y.regs r = x.regs r) →
      ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  refine ReachW.blockAcc hb _ off hpc ho hseq fold_falls
    (X25519MulcWord.accAll_regOnly _ _ fold_regOnly) hr ?_
  obtain ⟨v3, v8, m, o⟩ := fold_exec x hh
  exact cont _ (by rw [execAll_pc _ _ fold_falls, hpc, ofNat_add_assoc]) v3 v8 m o

/-! ## `fin` and `pop {pc}` -/

open M0Crypto.Release.X25519Mem (toReg0 toReg1) in
theorem fin_exec (s : State) :
    let s' := execAll fin s
    s'.mem = write32 s.mem (sAddr s 7) (addWithCarry (s.regs 8) (s.reg 0) false).1 ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 0 → r ≠ 1 → s'.regs r = s.regs r := by
  intro s'
  refine ⟨?_, fun r h15 h0 h1 => ?_⟩
  · simp (config := {decide := true}) only [s', fin, execAll, mem_strImm, mem_movHi, mem_adds,
      State.reg, regs_movHi, regs_adds, toReg0, toReg1, ite_true, ite_false, ne_eq,
      not_false_eq_true, sAddr]
    rfl
  · have v : ∀ n : Reg, r ≠ n → r.val ≠ n.val := fun n h e => h (Fin.ext e)
    have v0 : r.val ≠ 0 := v 0 h0
    have v1 : r.val ≠ 1 := v 1 h1
    have l0 : ((0 : Reg) : Nat) = 0 := rfl
    have l1 : ((1 : Reg) : Nat) = 1 := rfl
    have m0 : ((0 : LowReg) : Nat) = 0 := rfl
    have m1 : ((1 : LowReg) : Nat) = 1 := rfl
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      simp [fin, Instr.dsts, MemOp.isLoad, l0, l1, m0, m1, v0, v1])

theorem fin_falls : fin.all Instr.falls = true := by simp [fin, Instr.falls]

theorem fin_acc {Wr : Word → Prop} (s : State) (h12 : (s.regs 12).toNat % 4 = 0)
    (hW : ∀ q < 4, Wr (sAddr s 7 + BitVec.ofNat 32 q)) : AccAll (AccOk Wr) fin s := by
  have hpre : fin = [.movHi 1 8, .addReg 1 1 0, .movHi 0 12] ++ [.memImm .str 1 0 7] := rfl
  rw [hpre]
  refine accAll_append (X25519MulcWord.accAll_regOnly _ _ (by simp [X25519Mul.regOnly]))
    (accAll_cons (fun a ha => ?_) (accAll_nil _ _))
  have e : (execAll [.movHi 1 8, .addReg 1 1 0, .movHi 0 12] s).reg 0 = s.regs 12 := by
    simp (config := {decide := true}) only [execAll, State.reg, regs_movHi, regs_adds,
      X25519Mem.toReg0, X25519Mem.toReg1, ite_true, ite_false, ne_eq, not_false_eq_true]
  simp only [Instr.accesses, MemOp.isLoad, MemOp.width, e, List.mem_singleton] at ha
  subst ha
  exact ⟨aligned_word (word_add_aligned h12 (by omega)), fun _ q hq => hW q hq⟩

theorem fin_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off : Nat} (hseq : seqAt B off fin = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize fin))
    (h12 : (x.regs 12).toNat % 4 = 0) (hW : ∀ q < 4, Wr (sAddr x 7 + BitVec.ofNat 32 q))
    {Q : State → Prop}
    (cont : ∀ y : State, y.pc = base + BitVec.ofNat 32 (off + seqSize fin) →
      y.mem = write32 x.mem (sAddr x 7) (addWithCarry (x.regs 8) (x.reg 0) false).1 →
      (∀ r : Reg, r ≠ 15 → r ≠ 0 → r ≠ 1 → y.regs r = x.regs r) →
      ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  refine ReachW.blockAcc hb _ off hpc ho hseq fin_falls (fin_acc x h12 hW) hr ?_
  obtain ⟨m, o⟩ := fin_exec x
  exact cont _ (by rw [execAll_pc _ _ fin_falls, hpc, ofNat_add_assoc]) m o

/-- `pop {pc}`: return to the saved word at SP. -/
theorem pop_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off : Nat} (hat : instrAt B off = some (.pop 0 true)) (hsz : off + 2 ≤ B.length)
    (ho : off % 2 = 0) (hpc : x.pc = base + BitVec.ofNat 32 off) (hr : Pc (base + BitVec.ofNat 32 off))
    (hsp : (x.regs 13).toNat % 4 = 0) (hlr : (read32 x.mem (x.regs 13)).getLsbD 0 = true)
    {Q : State → Prop}
    (hq : ∀ y : State, y.pc = read32 x.mem (x.regs 13) &&& ~~~1#32 →
      y.regs 13 = x.regs 13 + 4#32 → y.mem = x.mem → Q y) :
    ReachW base Pc Wr x Q := by
  have hb0 : bitCount (0 : BitVec 8) = 0 := by decide
  have hl : listRegs (0 : BitVec 8) = [] := by decide
  have hb0' : bitCount 0#8 = 0 := by decide
  have hl' : listRegs 0#8 = [] := by decide
  have ha : x.regs 13 + BitVec.ofNat 32 (4 * bitCount (0 : BitVec 8)) = x.regs 13 := by
    rw [hb0]; simp
  have hex : (Instr.pop 0 true).exec x = .ok
      ((((loadRegs (x.setReg 15 (x.pc + BitVec.ofNat 32 (Instr.pop 0 true).size)) x.sp
        ((listRegs 0).map LowReg.toReg)).setReg 13
          (x.sp + BitVec.ofNat 32 (4 * (bitCount 0 + true.toNat))))).setReg 15
          (read32 x.mem (x.regs 13) &&& ~~~1#32)) := by
    simp only [Instr.exec, State.sp, ha, hlr, ite_true]
  refine ReachW.step hb off (.pop 0 true) hpc ho hat hsz ?_ hex ?_ hr (ReachS.done (hq _ ?_ ?_ ?_))
  · simp [Instr.accesses, wordAccesses, hb0, Access.aligned, State.sp, hsp]
  · intro y ⟨a, ha', hw, _⟩
    simp [Instr.accesses, wordAccesses, hb0] at ha'
    obtain ⟨_, _, rfl⟩ := ha'
    cases hw
  · simp [State.setReg, State.pc]
  · simp [State.setReg, hb0, hb0', loadRegs, hl, hl', State.sp]
  · simp [State.setReg, loadRegs, hl, hl']

end M0Crypto.Release.X25519MulcEnds
