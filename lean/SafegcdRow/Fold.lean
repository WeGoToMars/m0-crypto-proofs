import SafegcdRow.FoldCode
import SafegcdRow.Correct

namespace SafegcdRow.FoldCode
set_option linter.unusedSimpArgs false
open M0Crypto.Armv6M (State Reg Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr slot_byte_ne')

def truncated (m : Mem) (a : Word) : Mem :=
  write32 m (slot a 15) (truncate (read32 m (slot a 15)))

def incoming (m : Mem) (a : Word) : Nat → Word
  | 0 => 19#32 * spill m a
  | i+1 => carry (incoming m a i + read32 (truncated m a) (slot a i))

def outDigit (m : Mem) (a : Word) (i : Nat) : Word :=
  low (incoming m a i + read32 (truncated m a) (slot a i))

def foldPrefix (m : Mem) (a : Word) (n : Nat) : Mem :=
  storeWords (truncated m a) a ((List.range n).map (outDigit m a))

def foldedMemory (m : Mem) (a : Word) : Mem :=
  write32 (foldPrefix m a 16) (slot a 16) (incoming m a 16)

private theorem prefix_succ (m : Mem) (a : Word) (i : Nat) :
    foldPrefix m a (i+1) = write32 (foldPrefix m a i) (slot a i) (outDigit m a i) := by
  simp only [foldPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    store_append_one, List.length_map, List.length_range]

private theorem prefix_read (m : Mem) (a : Word) (i : Nat) (hi : i < 16) :
    read32 (foldPrefix m a i) (slot a i) = read32 (truncated m a) (slot a i) := by
  apply read32_congr
  intro k hk
  unfold foldPrefix
  apply storeWords_other
  intro j l hj hl
  simp only [List.length_map, List.length_range] at hj
  exact (slot_byte_ne' a j i l k (by omega) (by omega) hl hk (by omega)).symm

private theorem head_keeps (s : State) (r : Reg)
    (hr : r = 0 ∨ r = 13 ∨ r = 14) : (execAll head s).regs r = s.regs r := by
  rcases hr with rfl | rfl | rfl <;> exact execAll_regs_other _ _ _ (by decide) (by decide)

private theorem tail_keeps (s : State) (r : Reg) (hr : r.val ≠ 15) :
    (execAll tail s).regs r = s.regs r :=
  execAll_regs_other _ _ _ hr rfl

private structure Ready (m : Mem) (a ret sp : Word) (i : Nat) (s : State) : Prop where
  mem : s.mem = foldPrefix m a i
  addr : s.regs 0 = a
  nextCarry : s.regs 1 = incoming m a i
  ret : s.regs 14 = ret
  sp : s.regs 13 = sp

private theorem column_ready (m : Mem) (a ret sp : Word) (i : Nat) (s : State)
    (hi : i < 16) (h : Ready m a ret sp i s) :
    Ready m a ret sp (i+1) (execAll (column (BitVec.ofNat 5 i)) s) := by
  have hj : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  obtain ⟨hm, hc⟩ := column_effect s (BitVec.ofNat 5 i)
  rw [h.mem, h.addr, hj, h.nextCarry, prefix_read _ _ _ hi] at hm hc
  refine ⟨hm.trans (prefix_succ m a i).symm, ?_, hc, ?_, ?_⟩
  · rw [column_keeps _ _ _ (by decide)]; exact h.addr
  · rw [column_keeps _ _ _ (by decide)]; exact h.ret
  · rw [column_keeps _ _ _ (by decide)]; exact h.sp

private theorem run_columns (m : Mem) (a ret sp : Word) (n i : Nat) (s : State)
    (hi : i+n = 16) (h : Ready m a ret sp i s) :
    let code := (List.range' i n).flatMap (fun j => column (BitVec.ofNat 5 j)) ++ tail
    let t := execAll code s
    t.mem = foldedMemory m a ∧ t.regs 14 = ret ∧ t.regs 13 = sp := by
  induction n generalizing i s with
  | zero =>
    have hei : i = 16 := by omega
    subst i
    simp only [List.range'_zero, List.flatMap_nil, List.nil_append]
    exact ⟨by rw [tail_effect, h.mem, h.addr, h.nextCarry]; rfl,
      (tail_keeps _ _ (by decide)).trans h.ret, (tail_keeps _ _ (by decide)).trans h.sp⟩
  | succ n ih =>
    have hnext := column_ready m a ret sp i s (by omega) h
    have hs := ih (i+1) (execAll (column (BitVec.ofNat 5 i)) s) (by omega) hnext
    dsimp only at hs ⊢
    simp only [List.range'_succ, List.flatMap_cons, List.append_assoc, execAll_append] at hs ⊢
    exact hs

theorem body_memory (s : State) :
    let t := execAll body s
    t.mem = foldedMemory s.mem (s.regs 0) ∧
      t.regs 14 = s.regs 14 ∧ t.regs 13 = s.regs 13 := by
  obtain ⟨hm, hc⟩ := head_effect s
  have h : Ready s.mem (s.regs 0) (s.regs 14) (s.regs 13) 0 (execAll head s) :=
    ⟨hm, head_keeps _ _ (.inl rfl), hc, head_keeps _ _ (.inr (.inr rfl)),
      head_keeps _ _ (.inr (.inl rfl))⟩
  have hg := run_columns _ _ _ _ 16 0 _ (by decide) h
  have hl : List.range' 0 16 = List.range 16 := by decide +kernel
  simp only [hl] at hg
  simpa only [body, List.append_assoc, execAll_append] using hg

private def foldAccess (a : Word) : Instr → List Access
  | .memImm .ldr _ _ i => [loadAt a i.toNat]
  | .memImm .str _ _ i => [storeAt a i.toNat]
  | _ => []

private def foldInstr : Instr → Bool
  | .memImm .ldr _ 0 i | .memImm .str _ 0 i => i.toNat < 17
  | i => quiet i

private theorem fold_accesses (s : State) (i : Instr) (h : foldInstr i = true) :
    i.accesses s = foldAccess (s.regs 0) i := by
  cases i <;> simp_all [foldInstr, quiet, Instr.accesses, foldAccess]
  case memImm op t n i =>
    cases op <;> by_cases hn : n = 0 <;> simp_all [foldInstr, quiet]
    all_goals
      subst n
      simp [loadAt, storeAt, State.reg, slot, MemOp.isLoad, MemOp.width, Nat.mul_comm]
      rfl

private theorem fold_trace (is : List Instr) (s : State) (hf : is.all Instr.falls = true)
    (ha : is.all foldInstr = true) (hd : is.all (fun i => !i.dsts.contains 0) = true) :
    traceAll is s = annotate s.pc is (is.map (foldAccess (s.regs 0))) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hf ha hd
    rw [traceAll, fold_accesses _ _ ha.1, ih _ hf.2 ha.2 (by simpa using hd.2),
      next_regs_other s 0 (by decide) hd.1, exec_pc hf.1 (exec_ok_of_falls hf.1 s)]
    rfl

private theorem fold_aligned (is : List Instr) (s : State) (hf : is.all foldInstr = true)
    (hd : is.all (fun i => !i.dsts.contains 0) = true) (ha : (s.regs 0).toNat % 4 = 0) :
    alignedAll is s = true := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hf hd
    have hn : ((i.next s).regs 0).toNat % 4 = 0 := by
      rwa [next_regs_other s 0 (by decide) hd.1]
    rw [alignedAll, fold_accesses _ _ hf.1, ih _ hf.2 (by simpa using hd.2) hn]
    cases i <;> try rfl
    case memImm op t n k =>
      cases op <;> simp [foldAccess, loadAt, storeAt, Access.aligned, slot_aligned _ ha]

def predictedTrace (pc a : Word) : List Event :=
  annotate pc body (body.map (foldAccess a)) ++ [⟨nextPC pc body, .bx 14, []⟩]

theorem predicted_eq (s : State) :
    predictedTrace s.pc (s.regs 0) = traceAll body s ++ [⟨nextPC s.pc body, .bx 14, []⟩] := by
  rw [fold_trace _ _ (by decide) (by decide) (by decide)]
  rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 1700000 in
theorem run_fold {bytes : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : bytes.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt bytes off (body ++ [.bx 14]) = true)
    (ha : (s.regs 0).toNat % 4 = 0) (hr : (s.regs 14).getLsbD 0 = true) :
    ∃ t, runH bytes base (body.length + 1) s = .ok (t, predictedTrace s.pc (s.regs 0)) ∧
      t.mem = foldedMemory s.mem (s.regs 0) ∧ t.sp = s.sp ∧
      t.pc = (s.regs 14 &&& ~~~1#32) := by
  let u := execAll body s
  obtain ⟨hm, hl, hs⟩ := body_memory s
  have hf : body.all Instr.falls = true := by decide
  have ha' : alignedAll body s = true := fold_aligned _ _ (by decide) (by decide) ha
  have he : (off + seqSize body) % 2 = 0 := by
    have hz : seqSize body % 2 = 0 := by decide +kernel
    omega
  have hR : (u.regs 14).getLsbD 0 = true := by
    change ((execAll body s).regs 14).getLsbD 0 = true
    rw [hl, hr]
  have hrun := runH_leaf hb hlen hpc ho hat hf ha' he hR
  dsimp only at hrun
  rw [fold_trace _ _ hf (by decide) (by decide), execAll_pc _ _ hf] at hrun
  let ret := u.regs 14 &&& ~~~1#32
  let t := u.setReg 15 ret
  refine ⟨t, hrun, ?_, ?_, ?_⟩
  · have heq (v : State) (a : Word) : (v.setReg 15 a).mem = v.mem := rfl
    exact (heq u ret).trans hm
  · have heq (v : State) (a : Word) : (v.setReg 15 a).sp = v.regs 13 := by
      simp [State.sp, State.setReg]
    exact (heq u ret).trans hs
  · have heq (v : State) (a : Word) : (v.setReg 15 a).pc = a := by
      simp [State.pc, State.setReg]
    exact (heq u ret).trans (congrArg (fun x => x &&& ~~~1#32) hl)

theorem fold_frame (m : Mem) (a addr : Word) (h : ∀ i < 68, addr ≠ a + BitVec.ofNat 32 i) :
    foldedMemory m a addr = m addr := by
  have slot_out (i : Nat) (hi : i < 17) (j : Nat) (hj : j < 4) :
      addr ≠ slot a i + BitVec.ofNat 32 j := by
    simp only [slot, ofNat_add_assoc]
    exact h _ (by omega)
  rw [foldedMemory, M0Crypto.Armv6M.write32_other _ _ _ _ (slot_out 16 (by decide))]
  unfold foldPrefix
  rw [storeWords_other]
  · exact M0Crypto.Armv6M.write32_other _ _ _ _ (slot_out 15 (by decide))
  · intro i j hi hj
    simp only [List.length_map, List.length_range] at hi
    exact slot_out i (by omega) j hj

end SafegcdRow.FoldCode
