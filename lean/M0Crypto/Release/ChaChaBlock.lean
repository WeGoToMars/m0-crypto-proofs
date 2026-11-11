import M0Crypto.Release.ChaChaInit
import M0Crypto.Release.ChaChaLayout
import M0Crypto.Release.ChaChaLoop
import M0Crypto.Release.AccessReach

set_option linter.unusedSimpArgs false

/-!
One block of `m0c_chacha20_xor`: `.Lblock` (offset `bpreOff`) copies rows a-c of `j` to `x`,
puts row d in r8-r11 and x[2] in r0, sets the rotation counts and the round count,
then runs the round loop (`ChaChaLoop.loop`).
-/

namespace M0Crypto.Release.ChaChaBlock
open M0Crypto.Release.CT

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaChaSetup (setReg15_regs setReg15_pc fp4 fp_toNat wr_frame)
open M0Crypto.Release.ChaChaInit (fw_other fw_same)
open M0Crypto.Release.ChaChaLayout (bpreOff ptr1Off ptr2Off ptr3Off btailOff droundOff postOff slotJ slotX slotCtr slotNon chFrameWords)

set_option maxRecDepth 100000

theorem slot_succ (sp : Word) (i : Nat) : slot sp i + 4#32 = slot sp (i + 1) := by
  simp only [slot, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]; congr 2

theorem slot_add (sp : Word) (i k : Nat) : slot sp i + BitVec.ofNat 32 (4 * k) = slot sp (i + k) := by
  simp only [slot, ofNat_add_assoc]; congr 2; omega

theorem listRegs_0f : listRegs 0x0f = [0, 1, 2, 3] := by decide
theorem listRegs_15 : listRegs 15#8 = [0, 1, 2, 3] := by decide
theorem bitCount_0f : bitCount 0x0f = 4 := by decide
theorem bitCount_15 : bitCount 15#8 = 4 := by decide

/-- `ldmia r4!, {r0-r3}; stmia r5!, {r0-r3}` copies slots `a..a+3` to `b..b+3`. -/
theorem pair (t : State) (sp : Word) (a b : Nat) (h4 : t.regs 4 = slot sp a) (h5 : t.regs 5 = slot sp b) :
    let t' := execAll [.ldm 4 0x0f, .stm 5 0x0f] t
    t'.regs 4 = slot sp (a + 4) ∧ t'.regs 5 = slot sp (b + 4) ∧
    t'.regs 0 = read32 t.mem (slot sp a) ∧ t'.regs 1 = read32 t.mem (slot sp (a + 1)) ∧
    t'.regs 2 = read32 t.mem (slot sp (a + 2)) ∧ t'.regs 3 = read32 t.mem (slot sp (a + 3)) ∧
    (∀ r : Reg, 5 < r.val → r.val ≠ 15 → t'.regs r = t.regs r) ∧
    t'.mem = write32 (write32 (write32 (write32 t.mem (slot sp b) (read32 t.mem (slot sp a)))
      (slot sp (b + 1)) (read32 t.mem (slot sp (a + 1)))) (slot sp (b + 2)) (read32 t.mem (slot sp (a + 2))))
      (slot sp (b + 3)) (read32 t.mem (slot sp (a + 3))) := by
  simp only [execAll, Instr.next, Instr.exec, listRegs_0f, listRegs_15, bitCount_0f, bitCount_15, List.map,
    loadRegs, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, storeWords, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4,
    M0Crypto.Proofs.toReg_5]
  simp (config := { decide := true }) only [ite_true, ite_false, h4, h5, slot_succ, slot_add]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r h1 h2 => ?_, ?_⟩
  · repeat' split
    all_goals first
      | rfl
      | (rename_i h; subst h; first | exact absurd h1 (by decide) | exact absurd h2 (by decide))
  · trivial

theorem pair_aligned (t : State) (sp : Word) (a b : Nat) (hsp : sp.toNat % 4 = 0)
    (h4 : t.regs 4 = slot sp a) (h5 : t.regs 5 = slot sp b) : alignedAll [.ldm 4 0x0f, .stm 5 0x0f] t = true := by
  have h5' : ((Instr.ldm 4 0x0f).next t).regs 5 = slot sp b := by
    rw [next_regs_other t 5 (by decide) (by rw [show Instr.dsts (.ldm 4 0x0f) = [0, 1, 2, 3, 4] by decide]; decide)]; exact h5
  simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_4,
    M0Crypto.Proofs.toReg_5, h4, h5', bitCount_0f, wordAccesses, List.range_succ, List.range_zero,
    List.nil_append, List.map, List.all_cons, List.all_nil, Access.aligned, Bool.and_true, beq_iff_eq,
    Bool.and_eq_true, slot_add]
  simp only [List.singleton_append, List.cons_append, List.map, List.all_cons, List.all_nil, Access.aligned,
    beq_iff_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, slot, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [List.nil_append, List.singleton_append, List.cons_append, List.map, List.all_cons, List.all_nil,
    Access.aligned, beq_iff_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem pair_writes (t : State) (sp : Word) (b : Nat) (h5 : t.regs 5 = slot sp b) :
    ∀ e ∈ traceAll [.ldm 4 0x0f, .stm 5 0x0f] t, ∀ y, Writes e.accesses y →
      ∃ o < 4 * (b + 4), y = sp + BitVec.ofNat 32 o := by
  have h5' : ((Instr.ldm 4 0x0f).next t).regs 5 = slot sp b := by
    rw [next_regs_other t 5 (by decide) (by rw [show Instr.dsts (.ldm 4 0x0f) = [0, 1, 2, 3, 4] by decide]; decide)]; exact h5
  intro e he y ⟨a, ha, hw, q, hq, hy⟩
  simp only [traceAll, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha; cases hw
  · simp only [Instr.accesses, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_5, h5', wordAccesses,
      List.mem_map, List.mem_range, bitCount_0f] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨4 * b + 4 * i + q, by simp at hq; omega, ?_⟩
    rw [hy]; simp only [slot, ofNat_add_assoc]

theorem noWrite_traceAll : ∀ (is : List Instr) (s : State), is.all (!·.writesMem) = true →
    ∀ e ∈ traceAll is s, ∀ y, ¬ Writes e.accesses y := M0Crypto.Release.noWrite_traceAll

/-! ## `.Lblock`: `bpreOff` - `droundOff` -/

theorem bset_at : seqAt B bpreOff bset = true := by decide

theorem bpre_effect (t : State) (sp : Word) (h13 : t.regs 13 = sp) :
    let u := execAll bpre t
    u.regs 4 = slot sp slotJ ∧ u.regs 5 = slot sp slotX ∧ u.mem = t.mem ∧
    (∀ r : Reg, r.val ≠ 4 → r.val ≠ 5 → r.val ≠ 15 → u.regs r = t.regs r) := by
  refine ⟨?_, ?_, execAll_mem _ _ (by decide), fun r h4 h5 h15 =>
    execAll_regs_other _ _ r h15 (by simp [bpre, Instr.dsts]; omega)⟩
  · simp only [bpre, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, slotJ, slotX]
    simp (config := { decide := true }) only [ite_true, ite_false, h13]
    simp [slot]
  · simp only [bpre, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, slotJ, slotX]
    simp (config := { decide := true }) only [ite_true, ite_false, h13]
    simp [slot]

theorem btail_effect (t : State) (sp : Word) (h13 : t.regs 13 = sp) (h4 : t.regs 4 = slot sp slotCtr) :
    let u := execAll btail t
    u.mem = t.mem ∧ u.regs 13 = sp ∧ u.regs 0 = read32 t.mem (slot sp (slotX + 2)) ∧
    u.regs 8 = read32 t.mem (slot sp slotCtr) ∧ u.regs 9 = read32 t.mem (slot sp slotNon) ∧
    u.regs 10 = read32 t.mem (slot sp (slotNon + 1)) ∧ u.regs 11 = read32 t.mem (slot sp (slotNon + 2)) ∧
    u.regs 4 = 16#32 ∧ u.regs 5 = 20#32 ∧ u.regs 6 = 24#32 ∧ u.regs 7 = 25#32 ∧ u.regs 12 = 10#32 := by
  have hm : (execAll btail t).mem = t.mem := execAll_mem _ _ (by decide)
  refine ⟨hm, (execAll_regs_other btail t 13 (by decide) (by decide)).trans h13, ?_⟩
  all_goals
    simp only [btail, execAll, Instr.next, Instr.exec, listRegs_0f, listRegs_15, bitCount_0f, bitCount_15, slotX, slotJ, slotCtr, slotNon,
      List.map, loadRegs, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6,
      M0Crypto.Proofs.toReg_7]
    simp (config := { decide := true }) only [ite_true, ite_false, h4, h13, slot_succ, slot_add]
  all_goals first | rfl | simp [slot, slotX, slotJ, slotCtr, slotNon]

theorem btail_aligned (t : State) (sp : Word) (hsp : sp.toNat % 4 = 0) (h13 : t.regs 13 = sp)
    (h4 : t.regs 4 = slot sp slotCtr) : alignedAll btail t = true := by
  have e : btail = [.ldm 4 0x0f] ++ ([.movHi 8 0, .movHi 9 1, .movHi 10 2, .movHi 11 3] ++
      ([.ldrSp 0 2] ++ [.movImm 4 16, .movImm 5 20, .movImm 6 24, .movImm 7 25, .movImm 1 10, .movHi 12 1])) := rfl
  rw [e, alignedAll_append, alignedAll_append, alignedAll_append]
  have r1 := execAll_regs_other [.ldm 4 0x0f] t 13 (by decide) (by decide)
  have r2 := execAll_regs_other [.movHi 8 0, .movHi 9 1, .movHi 10 2, .movHi 11 3] (execAll [.ldm 4 0x0f] t) 13
    (by decide) (by decide)
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_4, h4, slotCtr, bitCount_0f,
      wordAccesses, List.range_succ, List.range_zero, List.nil_append, List.map, List.all_cons, List.all_nil,
      Access.aligned, Bool.and_true, beq_iff_eq, Bool.and_eq_true, slot_add, List.singleton_append,
      List.cons_append, decide_eq_true_eq, slot, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp [alignedAll, Instr.accesses]
  · simp only [alignedAll, Instr.accesses, List.all_cons, List.all_nil, Bool.and_true]
    simp only [Access.aligned, M0Crypto.Armv6M.State.sp, r1, r2, h13, beq_iff_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    omega
  · simp [alignedAll, Instr.accesses]

theorem bpre_aligned (t : State) : alignedAll bpre t = true := by simp [alignedAll, bpre, Instr.accesses]

/-- The memory after one `ldm/stm` pair. -/
def w4 (m : Mem) (sp : Word) (a b : Nat) : Mem :=
  write32 (write32 (write32 (write32 m (slot sp b) (read32 m (slot sp a)))
      (slot sp (b + 1)) (read32 m (slot sp (a + 1)))) (slot sp (b + 2)) (read32 m (slot sp (a + 2))))
      (slot sp (b + 3)) (read32 m (slot sp (a + 3)))

theorem w4_read (m : Mem) (sp : Word) (a b j : Nat) (hb : b + 4 ≤ 64) (hj : j < 64)
    (hab : b + 4 ≤ a) :
    read32 (w4 m sp a b) (slot sp j) =
      if b ≤ j ∧ j < b + 4 then read32 m (slot sp (a + (j - b))) else read32 m (slot sp j) := by
  have hs : ∀ i, i < 64 → i < 2 ^ 28 := fun i h => by omega
  unfold w4
  rw [read32_write32_slot' _ _ _ _ _ (hs _ (by omega)) (hs _ hj),
    read32_write32_slot' _ _ _ _ _ (hs _ (by omega)) (hs _ hj),
    read32_write32_slot' _ _ _ _ _ (hs _ (by omega)) (hs _ hj),
    read32_write32_slot' _ _ _ _ _ (hs _ (by omega)) (hs _ hj)]
  by_cases hj' : b ≤ j ∧ j < b + 4
  · rw [if_pos hj']
    have : j = b ∨ j = b + 1 ∨ j = b + 2 ∨ j = b + 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp
  · rw [if_neg hj', if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem w4_memOk (c : Ctx) {P : Nat} {m : Mem} (h : c.MemOk P m) (a b : Nat) (hb : b + 4 ≤ chFrameWords) :
    c.MemOk P (w4 m c.fp a b) := by
  have sFW := ChaChaLayout.chFrameWords_eq
  unfold w4
  exact c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot h _ (by omega) _)
    _ (by omega) _) _ (by omega) _) _ (by omega) _

/-- One `ldm/stm` pair at offset `off`, in `Reach` form. -/
theorem pair_block_events (c : Ctx) (hv : Valid c) (t : State) (off a b : Nat) (ho : off % 2 = 0)
    (hpc : t.pc = c.base + BitVec.ofNat 32 off) (hseq : seqAt B off ptr = true)
    (h4 : t.regs 4 = slot c.fp a) (h5 : t.regs 5 = slot c.fp b) (hb : b + 4 ≤ chFrameWords)
    (allowed : Word → Kind → Word → Prop) (hacc : EventAccessesTo allowed (traceAll ptr t)) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (off + 4) → t'.regs 4 = slot c.fp (a + 4) →
      t'.regs 5 = slot c.fp (b + 4) → (∀ r : Reg, 5 < r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      t'.mem = w4 t.mem c.fp a b → ReachEvents c.base allowed t' Q) :
    ReachEvents c.base allowed t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sSB := ChaChaLayout.chStackBytes_eq
  have sFW := ChaChaLayout.chFrameWords_eq
  apply ReachEvents.block hb2 ptr off hpc ho hseq (by decide) (pair_aligned t c.fp a b (fp4 hv) h4 h5)
    hacc
  obtain ⟨p4, p5, -, -, -, -, pr, pm⟩ := pair t c.fp a b h4 h5
  apply cont _ _ p4 p5 pr pm
  rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl

theorem pair_block (c : Ctx) (hv : Valid c) (t : State) (off a b : Nat) (ho : off % 2 = 0)
    (hpc : t.pc = c.base + BitVec.ofNat 32 off) (hseq : seqAt B off ptr = true)
    (h4 : t.regs 4 = slot c.fp a) (h5 : t.regs 5 = slot c.fp b) (hb : b + 4 ≤ chFrameWords) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (off + 4) → t'.regs 4 = slot c.fp (a + 4) →
      t'.regs 5 = slot c.fp (b + 4) → (∀ r : Reg, 5 < r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      t'.mem = w4 t.mem c.fp a b → Reach c.base c.Wr t' Q) :
    Reach c.base c.Wr t Q := by
  apply (pair_block_events c hv t off a b ho hpc hseq h4 h5 hb (writeOnlyPolicy c.Wr) ?_ Q ?_).toReach
  · intro _ _ h
    rcases h with h | h
    · cases h
    · exact h
  · apply WritesTo.toEventAccesses
    intro e he y hy
    obtain ⟨o, hlt, rfl⟩ := pair_writes t c.fp b h5 e he y hy
    have := ChaChaLayout.chStackBytes_eq
    have := ChaChaLayout.chFrameWords_eq
    exact .inl ⟨o, by omega, rfl⟩
  · intro u hp hr4 hr5 hr hm
    exact Reach.toReachEvents (cont u hp hr4 hr5 hr hm)

theorem ptr_at1 : seqAt B ptr1Off ptr = true := by decide
theorem ptr_at2 : seqAt B ptr2Off ptr = true := by decide
theorem ptr_at3 : seqAt B ptr3Off ptr = true := by decide
theorem bpre_at : seqAt B bpreOff bpre = true := by decide
theorem btail_at : seqAt B btailOff btail = true := by decide
theorem ptr1_next : ptr1Off + 4 = ptr2Off := by decide
theorem ptr2_next : ptr2Off + 4 = ptr3Off := by decide
theorem ptr3_next : ptr3Off + 4 = btailOff := by decide

/-- The three pairs copy `j` (slots 16..27) to `x` (slots 0..11). -/
theorem w4_3_read (m : Mem) (sp : Word) (j : Nat) (hj : j < 64) :
    read32 (w4 (w4 (w4 m sp slotJ slotX) sp (slotJ + 4) (slotX + 4)) sp (slotJ + 4 + 4) (slotX + 4 + 4)) (slot sp j) =
      if j < 12 then read32 m (slot sp (slotJ + j)) else read32 m (slot sp j) := by
  simp only [slotJ, slotX]
  simp (disch := omega) only [w4_read]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (congr 2; omega)

theorem noWrites (is : List Instr) (s : State) (h : is.all (!·.writesMem) = true) (Wr : Word → Prop) :
    WritesTo Wr (traceAll is s) := WritesTo.of_noWritesMem is s h Wr

open M0Crypto.Release.ChaChaRound (RotRegs view dregOf) in
/-- **`.Lblock` setup** (`bpreOff` - `droundOff`): from `BlockInv c k` to the round-loop start with
the state `j` of block `k` in the loop's view. -/
theorem bsetup_events (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) (allowed : Word → Kind → Word → Prop)
    (hpre : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 bpreOff →
      EventAccessesTo allowed (traceAll bpre u))
    (hpair : ∀ (off a b : Nat) (u : State), (off = ptr1Off ∨ off = ptr2Off ∨ off = ptr3Off) →
      u.pc = c.base + BitVec.ofNat 32 off →
      seqAt B off ptr = true → u.regs 4 = slot c.fp a → u.regs 5 = slot c.fp b →
      b + 4 ≤ chFrameWords → EventAccessesTo allowed (traceAll ptr u))
    (htail : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 btailOff →
      EventAccessesTo allowed (traceAll btail u)) (Q : State → Prop)
    (cont : ∀ u, u.pc = c.base + BitVec.ofNat 32 droundOff → RotRegs u → u.regs 13 = c.fp →
      u.regs 12 = 10#32 → view (some 2) u = c.J k →
      (∀ j, 12 ≤ j → j < 64 → c.fw u j = c.fw t j) → c.MemOk (64 * k) u.mem → ReachEvents c.base allowed u Q) :
    ReachEvents c.base allowed t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ReachEvents.block hb2 bpre bpreOff h.pc (by decide) bpre_at (by decide) (bpre_aligned t)
    (hpre t h.pc)
  obtain ⟨p4, p5, pm, pr⟩ := bpre_effect t c.fp h.sp
  have pc0 : (execAll bpre t).pc = c.base + BitVec.ofNat 32 ptr1Off := by
    rw [execAll_pc _ _ (by decide), h.pc, ofNat_add_assoc]; rfl
  have sp0 : (execAll bpre t).regs 13 = c.fp := by rw [pr 13 (by decide) (by decide) (by decide)]; exact h.sp
  apply pair_block_events c hv _ ptr1Off slotJ slotX (by decide) pc0 ptr_at1 p4 p5 (by decide)
    allowed (hpair _ _ _ _ (by simp) pc0 ptr_at1 p4 p5 (by decide))
  intro t1 pc1 a1 b1 r1 m1
  rw [ptr1_next] at pc1
  apply pair_block_events c hv t1 ptr2Off (slotJ + 4) (slotX + 4) (by decide) pc1 ptr_at2 a1 b1 (by decide)
    allowed (hpair _ _ _ t1 (by simp) pc1 ptr_at2 a1 b1 (by decide))
  intro t2 pc2 a2 b2 r2 m2
  rw [ptr2_next] at pc2
  apply pair_block_events c hv t2 ptr3Off (slotJ + 4 + 4) (slotX + 4 + 4) (by decide) pc2 ptr_at3 a2 b2 (by decide)
    allowed (hpair _ _ _ t2 (by simp) pc2 ptr_at3 a2 b2 (by decide))
  intro t3 pc3 a3 b3 r3 m3
  rw [ptr3_next] at pc3
  have sp3 : t3.regs 13 = c.fp := by
    rw [r3 13 (by decide) (by decide), r2 13 (by decide) (by decide), r1 13 (by decide) (by decide), sp0]
  have hM : t3.mem = w4 (w4 (w4 t.mem c.fp slotJ slotX) c.fp (slotJ + 4) (slotX + 4)) c.fp (slotJ + 4 + 4)
      (slotX + 4 + 4) := by rw [m3, m2, m1, pm]
  have rd : ∀ j, j < 64 → read32 t3.mem (slot c.fp j) =
      if j < 12 then c.fw t (slotJ + j) else c.fw t j := fun j hj => by rw [hM, w4_3_read _ _ _ hj]; rfl
  apply ReachEvents.block hb2 btail btailOff pc3 (by decide) btail_at (by decide)
    (btail_aligned t3 c.fp (fp4 hv) sp3 a3) (htail t3 pc3)
  obtain ⟨um, u13, u0, u8, u9, u10, u11, u4, u5, u6, u7, u12⟩ := btail_effect t3 c.fp sp3 a3
  apply cont _ (by rw [execAll_pc _ _ (by decide), pc3, ofNat_add_assoc]; rfl) ⟨u4, u5, u6, u7⟩ u13 u12
  · funext i
    unfold ChaChaRound.view
    by_cases hi : i < 12
    · rw [if_pos hi]
      split
      · rename_i h2; cases h2; rw [u0, rd (slotX + 2) (by decide), if_pos (by decide)]; exact h.j 2 (by decide)
      · rw [u13, um, rd i (by omega), if_pos hi]; exact h.j i (by omega)
    · rw [if_neg hi]
      by_cases hi' : i < 16
      · rw [if_pos hi']
        have : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
        rcases this with rfl | rfl | rfl | rfl
        · show (execAll btail t3).regs 8 = _
          rw [u8, rd slotCtr (by decide), if_neg (by decide)]; exact h.j 12 (by decide)
        · show (execAll btail t3).regs 9 = _
          rw [u9, rd slotNon (by decide), if_neg (by decide)]; exact h.j 13 (by decide)
        · show (execAll btail t3).regs 10 = _
          rw [u10, rd (slotNon + 1) (by decide), if_neg (by decide)]; exact h.j 14 (by decide)
        · show (execAll btail t3).regs 11 = _
          rw [u11, rd (slotNon + 2) (by decide), if_neg (by decide)]; exact h.j 15 (by decide)
      · rw [if_neg hi']; simp [Ctx.J, hi']
  · intro j hj hj'
    show read32 (execAll btail t3).mem (slot c.fp j) = _
    rw [um, rd j hj', if_neg (by omega)]
  · rw [um, hM]
    exact w4_memOk c (w4_memOk c (w4_memOk c (by rw [← pm]; exact h.mem) _ _ (by decide)) _ _ (by decide)) _ _
      (by decide)

open M0Crypto.Release.ChaChaRound (RotRegs view dregOf) in
theorem bsetup (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) (Q : State → Prop)
    (cont : ∀ u, u.pc = c.base + BitVec.ofNat 32 droundOff → RotRegs u → u.regs 13 = c.fp →
      u.regs 12 = 10#32 → view (some 2) u = c.J k →
      (∀ j, 12 ≤ j → j < 64 → c.fw u j = c.fw t j) → c.MemOk (64 * k) u.mem → Reach c.base c.Wr u Q) :
    Reach c.base c.Wr t Q := by
  apply (bsetup_events c hv k t h (writeOnlyPolicy c.Wr) ?_ ?_ ?_ Q ?_).toReach
  · intro _ _ h
    rcases h with h | h
    · cases h
    · exact h
  · intro u _
    exact WritesTo.toEventAccesses (noWrites bpre u (by decide) c.Wr)
  · intro off a b u hoff hp hseq h4 h5 hb
    apply WritesTo.toEventAccesses
    intro e he y hy
    obtain ⟨o, ho, rfl⟩ := pair_writes u c.fp b h5 e he y hy
    have := ChaChaLayout.chStackBytes_eq
    have := ChaChaLayout.chFrameWords_eq
    exact Or.inl ⟨o, by omega, rfl⟩
  · intro u _
    exact WritesTo.toEventAccesses (noWrites btail u (by decide) c.Wr)
  · intro u hp hr hs h12 hv' hf hm
    exact Reach.toReachEvents (cont u hp hr hs h12 hv' hf hm)

/-! ## The keystream words of block `k` -/

open M0Crypto.Proofs.ChaCha20DRound (innerBlockF toArr toArr_getElem!)
open M0Crypto.Spec.ChaCha20 (initState initState_size block bytesOfWord)

/-- Keystream word `i` of block `k`: `j[i] + x[i]` after ten double rounds. -/
def ks (c : Ctx) (k i : Nat) : Word := c.J k i + ChaChaLoop.iter innerBlockF 10 (c.J k) i

theorem J_toArr (c : Ctx) (k : Nat) : toArr (c.J k) = initState c.keyB (c.ctr + BitVec.ofNat 32 k) c.nonceB := by
  have hs := initState_size c.keyB c.nonceB (c.ctr + BitVec.ofNat 32 k) (bytesAt_length _ _ _) (bytesAt_length _ _ _)
  apply Array.ext
  · simp [toArr, hs]
  · intro i h1 h2
    simp only [toArr, Array.getElem_ofFn, Ctx.J]
    have : i < 16 := by simpa [toArr] using h1
    simp only [this, if_true]; exact getElem!_pos (initState c.keyB (c.ctr + BitVec.ofNat 32 k) c.nonceB) i h2

theorem block_ks (c : Ctx) (k j : Nat) (hj : j < 64) :
    (block c.keyB (c.ctr + BitVec.ofNat 32 k) c.nonceB)[j]? = (bytesOfWord (ks c k (j / 4)))[j % 4]? := by
  rw [ChaChaSpec.block_get _ _ _ _ hj, ← J_toArr, ← ChaChaLoop.iter_toArr, toArr_getElem! _ _ (by omega),
    toArr_getElem! _ _ (by omega)]
  rfl

open M0Crypto.Release.ChaChaRound (view) in
/-- **One block's rounds**: from `BlockInv c k` through `.Lblock` and the ten double rounds
to offset `postOff`. -/
theorem bround_events (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) (allowed : Word → Kind → Word → Prop)
    (hpre : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 bpreOff →
      EventAccessesTo allowed (traceAll bpre u))
    (hpair : ∀ (off a b : Nat) (u : State), (off = ptr1Off ∨ off = ptr2Off ∨ off = ptr3Off) →
      u.pc = c.base + BitVec.ofNat 32 off →
      seqAt B off ptr = true → u.regs 4 = slot c.fp a → u.regs 5 = slot c.fp b →
      b + 4 ≤ chFrameWords → EventAccessesTo allowed (traceAll ptr u))
    (htail : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 btailOff →
      EventAccessesTo allowed (traceAll btail u))
    (hloop : ∀ (u : State) tr, u.regs 13 = c.fp → WritesIn tr (u.regs 13) ChaChaRound.droundBytes →
      ChaChaLoop.TraceBeforeOutput c.base tr → AccessesIn tr (u.regs 13) ChaChaRound.droundBytes →
      EventAccessesTo allowed tr) (Q : State → Prop)
    (cont : ∀ v, v.pc = c.base + BitVec.ofNat 32 postOff → v.regs 13 = c.fp →
      ChaChaRound.view (some 2) v = ChaChaLoop.iter innerBlockF 10 (c.J k) →
      (∀ j, 12 ≤ j → j < 64 → c.fw v j = c.fw t j) → c.MemOk (64 * k) v.mem → ReachEvents c.base allowed v Q) :
    ReachEvents c.base allowed t Q := by
  have sSB := ChaChaLayout.chStackBytes_eq
  have sFB := ChaChaLayout.chFrameBytes_eq
  have hdb := ChaChaLayout.droundBytes_le_chFrameBytes
  have hfs := ChaChaLayout.chFrameBytes_le_chStackBytes
  have hsp := ChaChaLayout.droundBytes_le_spilled
  apply bsetup_events c hv k t h allowed hpre hpair htail
  intro u pc rot sp r12 hview hfw hmem
  obtain ⟨v, tr, hrun, vpc, vview, -, v13, -, -, vmem, vw, hpcs, haccess⟩ :=
    ChaChaLoop.loop_bounded hv.base4 10 (by decide) (by decide) u pc rot (by rw [sp]; exact fp4 hv) (by rw [r12])
  apply ReachEvents.bind
  refine ⟨_, v, tr, hrun, hloop u tr sp vw hpcs haccess, ?_⟩
  apply cont v vpc (v13.trans sp) (by rw [vview, hview])
  · intro j hj hj'
    rw [← hfw j hj hj']
    apply read32_congr
    intro q hq
    apply vmem
    intro o ho e
    have := congrArg BitVec.toNat e
    simp only [slot, sp, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · intro y hy
    rw [vmem y (fun o ho e => hy o (by omega) (by rw [e, sp]))]
    exact hmem y hy

open M0Crypto.Release.ChaChaRound (view) in
theorem bround (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) (Q : State → Prop)
    (cont : ∀ v, v.pc = c.base + BitVec.ofNat 32 postOff → v.regs 13 = c.fp →
      ChaChaRound.view (some 2) v = ChaChaLoop.iter innerBlockF 10 (c.J k) →
      (∀ j, 12 ≤ j → j < 64 → c.fw v j = c.fw t j) → c.MemOk (64 * k) v.mem → Reach c.base c.Wr v Q) :
    Reach c.base c.Wr t Q := by
  apply (bround_events c hv k t h (writeOnlyPolicy c.Wr) ?_ ?_ ?_ ?_ Q ?_).toReach
  · intro _ _ h
    rcases h with h | h
    · cases h
    · exact h
  · intro u _
    exact WritesTo.toEventAccesses (noWrites bpre u (by decide) c.Wr)
  · intro off a b u hoff hp hseq h4 h5 hb
    apply WritesTo.toEventAccesses
    intro e he y hy
    obtain ⟨o, ho, rfl⟩ := pair_writes u c.fp b h5 e he y hy
    have := ChaChaLayout.chStackBytes_eq
    have := ChaChaLayout.chFrameWords_eq
    exact Or.inl ⟨o, by omega, rfl⟩
  · intro u _
    exact WritesTo.toEventAccesses (noWrites btail u (by decide) c.Wr)
  · intro u tr hs hw _ _
    apply WritesTo.toEventAccesses
    exact WritesTo.of_writesIn hw (fun o ho => Or.inl ⟨o, by
      have := ChaChaLayout.droundBytes_le_chFrameBytes
      have := ChaChaLayout.chFrameBytes_le_chStackBytes
      omega, by rw [hs]⟩)
  · intro u hp hs hv' hf hm
    exact Reach.toReachEvents (cont u hp hs hv' hf hm)

/-- The functional block setup and round loop access memory only before the
output instruction region. -/
theorem bround_before_output (c : Ctx) (hv : Valid c) (k : Nat) (t : State)
    (h : BlockInv c k t) :
    ReachEvents c.base (fun pc kind y => PCBefore c.base ChaChaLayout.achOff pc ∧ writeOnlyPolicy c.Wr pc kind y) t (fun v =>
      v.pc = c.base + BitVec.ofNat 32 postOff ∧ v.regs 13 = c.fp ∧
      ChaChaRound.view (some 2) v = ChaChaLoop.iter innerBlockF 10 (c.J k) ∧
      (∀ j, 12 ≤ j → j < 64 → c.fw v j = c.fw t j) ∧ c.MemOk (64 * k) v.mem) := by
  apply bround_events c hv k t h (fun pc kind y => PCBefore c.base ChaChaLayout.achOff pc ∧ writeOnlyPolicy c.Wr pc kind y)
  · intro u hp
    exact (traceAll_pcBefore c.base ChaChaLayout.achOff bpreOff bpre u (by decide) hp (by decide +kernel)).and
      (WritesTo.toEventAccesses (noWrites bpre u (by decide) c.Wr))
  · intro off a b u hoff hp hseq h4 h5 hb
    rcases hoff with rfl | rfl | rfl
    · apply EventAccessesTo.and (traceAll_pcBefore c.base ChaChaLayout.achOff ptr1Off ptr u (by decide) hp (by decide +kernel))
      apply WritesTo.toEventAccesses
      intro e he y hy
      obtain ⟨o, ho, rfl⟩ := pair_writes u c.fp b h5 e he y hy
      have := ChaChaLayout.chStackBytes_eq
      have := ChaChaLayout.chFrameWords_eq
      exact Or.inl ⟨o, by omega, rfl⟩
    · apply EventAccessesTo.and (traceAll_pcBefore c.base ChaChaLayout.achOff ptr2Off ptr u (by decide) hp (by decide +kernel))
      apply WritesTo.toEventAccesses
      intro e he y hy
      obtain ⟨o, ho, rfl⟩ := pair_writes u c.fp b h5 e he y hy
      have := ChaChaLayout.chStackBytes_eq
      have := ChaChaLayout.chFrameWords_eq
      exact Or.inl ⟨o, by omega, rfl⟩
    · apply EventAccessesTo.and (traceAll_pcBefore c.base ChaChaLayout.achOff ptr3Off ptr u (by decide) hp (by decide +kernel))
      apply WritesTo.toEventAccesses
      intro e he y hy
      obtain ⟨o, ho, rfl⟩ := pair_writes u c.fp b h5 e he y hy
      have := ChaChaLayout.chStackBytes_eq
      have := ChaChaLayout.chFrameWords_eq
      exact Or.inl ⟨o, by omega, rfl⟩
  · intro u hp
    exact (traceAll_pcBefore c.base ChaChaLayout.achOff btailOff btail u (by decide) hp (by decide +kernel)).and
      (WritesTo.toEventAccesses (noWrites btail u (by decide) c.Wr))
  · intro u tr hs hw hpcs haccess
    apply EventAccessesTo.and
    · intro e he a ha q hq; exact hpcs e he
    · apply WritesTo.toEventAccesses
      exact WritesTo.of_writesIn hw (fun o ho => Or.inl ⟨o, by
        have := ChaChaLayout.droundBytes_le_chFrameBytes
        have := ChaChaLayout.chFrameBytes_le_chStackBytes
        omega, by rw [hs]⟩)
  · intro u hp hs hv' hf hm
    exact ReachEvents.done ⟨hp, hs, hv', hf, hm⟩

end M0Crypto.Release.ChaChaBlock
