import SafegcdTermination.Bank

namespace SafegcdTermination.RowCalls

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.CoreRows
open SafegcdTermination.RowsRefine
open M0Crypto.Armv6M (State Mem read32)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1300000

structure Setup (sp : Word) (r : RowCall) : Prop where
  frame : FrameOk sp
  dst : InSlot r.dst
  x : InSlot r.x
  y : InSlot r.y
  aliasX : r.dst = r.x ∨ Separate r.dst r.x
  aliasY : r.dst = r.y ∨ Separate r.dst r.y
  coeff : r.coeff ≤ 2

def qAt (sp : Word) (r : RowCall) (m : Mem) (a b t lr : Word) : Input :=
  ⟨⟨addr sp r.dst, addr sp r.x, addr sp r.y, a, b, t, lr, sp⟩, m⟩

theorem Setup.layout {sp : Word} {r : RowCall} (h : Setup sp r) (m : Mem)
    (a b t lr : Word) : Layout (qAt sp r m a b t lr).pins :=
  ⟨in_range h.frame h.dst, in_range h.frame h.x, in_range h.frame h.y,
    row_alias h.frame h.dst h.x h.aliasX, row_alias h.frame h.dst h.y h.aliasY⟩

theorem Setup.aligned {sp : Word} {r : RowCall} (h : Setup sp r) (m : Mem)
    (a b t lr : Word) : Aligned (qAt sp r m a b t lr).pins :=
  ⟨Bank.aligned h.frame h.dst, Bank.aligned h.frame h.x, Bank.aligned h.frame h.y⟩

theorem Setup.prepare {r : RowCall} {s : State} (h : Setup s.sp r) :
    let t := execAll (prepareRow r) s
    t.regs 0 = addr s.sp r.dst ∧ t.regs 1 = addr s.sp r.x ∧ t.regs 2 = addr s.sp r.y ∧
      t.regs 3 = stackWord s (matrixAt + 4 * r.coeff) ∧
      t.regs 4 = stackWord s (matrixAt + 4 * (r.coeff+1)) ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have hdst := h.dst.1
  have hx := h.x.1
  have hy := h.y.1
  have hN : frameBytes < 1024 := by decide
  exact row_arguments r s ⟨h.dst.2, by omega⟩ ⟨h.x.2, by omega⟩ ⟨h.y.2, by omega⟩ h.coeff

theorem prepareRow_falls (r : RowCall) : (prepareRow r).all Instr.falls = true := rfl

theorem prepareRow_sp (r : RowCall) : SpBlock (prepareRow r) (fun p => p.2 % 4 = 0) := by
  have h := spBlock_of_B (is := prepareRow r) (ok := fun p => p.2 % 4 == 0) (by
    simp [spBlockB, prepareRow, withSp, loadSp, Instr.spRel, Instr.dsts] <;> decide)
  exact h.mono (fun _ hp => beq_iff_eq.mp hp)

def linkedRet (base : Word) (off : Nat) : Word := (base + BitVec.ofNat 32 (off+4)) ||| 1#32

theorem linkedRet_odd (base : Word) (off : Nat) : (linkedRet base off).getLsbD 0 = true := by
  simp [linkedRet, BitVec.getLsbD_or]

theorem linkedRet_clear {base : Word} {off : Nat} (h₁ : base.toNat % 2 = 0) (h₂ : off % 2 = 0) :
    linkedRet base off &&& ~~~1#32 = base + BitVec.ofNat 32 (off+4) :=
  clear_thumb_return_bit _ (pc_even base (off+4) h₁ (by omega))

theorem entered_regs (base : Word) (off dest : Nat) (s : State) (r : M0Crypto.Armv6M.Reg)
    (hr : r ≠ 14) (hpc : r ≠ 15) : (entered base off dest s).regs r = s.regs r := by
  simp [entered, State.setReg, hr, hpc]

theorem entered_lr (base : Word) (off dest : Nat) (s : State) :
    (entered base off dest s).regs 14 = linkedRet base off := by
  simp [entered, linkedRet, State.setReg]

theorem entered_pc (base : Word) (off dest : Nat) (s : State) :
    (entered base off dest s).pc = base + BitVec.ofNat 32 dest := by
  simp [entered, State.pc, State.setReg]

theorem entered_mem (base : Word) (off dest : Nat) (s : State) :
    (entered base off dest s).mem = s.mem := rfl

theorem entered_sp (base : Word) (off dest : Nat) (s : State) :
    (entered base off dest s).sp = s.sp :=
  entered_regs base off dest s 13 (by decide) (by decide)

theorem prepared_exact {r : RowCall} {base : Word} {off dest : Nat} {s : State}
    (h : Setup s.sp r) :
    let t := entered base off dest (execAll (prepareRow r) s)
    let q := qAt s.sp r s.mem (stackWord s (matrixAt + 4*r.coeff))
      (stackWord s (matrixAt + 4*(r.coeff+1))) 0 (linkedRet base off)
    q = ⟨Pins.load t false, t.mem⟩ := by
  obtain ⟨hDst, hX, hY, hA, hB, hMem, hSp⟩ := h.prepare
  dsimp only [qAt, Pins.load]
  rw [entered_mem, entered_sp, entered_lr,
    entered_regs _ _ _ _ 0 (by decide) (by decide), entered_regs _ _ _ _ 1 (by decide) (by decide),
    entered_regs _ _ _ _ 2 (by decide) (by decide), entered_regs _ _ _ _ 3 (by decide) (by decide),
    entered_regs _ _ _ _ 4 (by decide) (by decide), hDst, hX, hY, hA, hB, hMem, hSp]
  rfl

theorem exact_call {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State} {r : RowCall}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (hob : off + seqSize (prepareRow r) + 4 < 2^23) (hdb : dest < 2^23)
    (link : seqAt code off (prepareRow r ++ [callTo (off + seqSize (prepareRow r)) dest]) = true)
    (leaf : seqAt code dest (body false ++ [.bx 12]) = true)
    (hs : Setup s.sp r) (m : Row) (n : Int) (hn : m.norm ≤ batchScale)
    (hA : stackWord s (matrixAt + 4*r.coeff) = BitVec.ofInt 32 m.a)
    (hB : stackWord s (matrixAt + 4*(r.coeff+1)) = BitVec.ofInt 32 m.b)
    (hx : VecWellFormed (vec s.mem (addr s.sp r.x))) (hy : VecWellFormed (vec s.mem (addr s.sp r.y)))
    (hnum : m.apply (value s.mem (addr s.sp r.x)) (value s.mem (addr s.sp r.y)) = batchScale * n) :
    let call := off + seqSize (prepareRow r)
    let q := qAt s.sp r s.mem (BitVec.ofInt 32 m.a) (BitVec.ofInt 32 m.b) 0 (linkedRet base call)
    ∃ t, runH code base ((prepareRow r).length + ((body false).length + 1 + 1)) s =
      .ok (t, traceAll (prepareRow r) s ++
        (⟨base + BitVec.ofNat 32 call, callTo call dest, []⟩ ::
        (predictedBody q.pins (base + BitVec.ofNat 32 dest) false ++
          [⟨nextPC (base + BitVec.ofNat 32 dest) (body false), .bx 12, []⟩]))) ∧
      t.pc = base + BitVec.ofNat 32 (call + 4) ∧ t.sp = s.sp ∧
      value t.mem (addr s.sp r.dst) = n ∧ Vectors.LowLimbs t.mem (addr s.sp r.dst) ∧
      WritesOnly s.mem t.mem (addr s.sp r.dst) vectorBytes := by
  let pre := prepareRow r
  let call := off + seqSize pre
  let u := execAll pre s
  let entry := entered base call dest u
  let q := qAt s.sp r s.mem (BitVec.ofInt 32 m.a) (BitVec.ofInt 32 m.b) 0 (linkedRet base call)
  have hq : q = ⟨Pins.load entry false, entry.mem⟩ := by
    have h := prepared_exact (base := base) (off := call) (dest := dest) hs
    simpa only [hA, hB, q, entry, u, pre] using h
  have hc : (q.pins.t.toNat : Int) = correction (rowInput q m) := by
    change (0 : Int) = correction (m.apply (value s.mem (addr s.sp r.x)) (value s.mem (addr s.sp r.y)))
    exact (exact_correction_zero _ _ _ _ hnum).symm
  have hpr : entry.pc = base + BitVec.ofNat 32 dest := entered_pc _ _ _ _
  have hret : (entry.regs 14).getLsbD 0 = true := by rw [entered_lr]; exact linkedRet_odd _ _
  obtain ⟨t, ht, hp, hsp, hm, hv, hw, _⟩ :=
    row_at_quotient hb hlen hpr hd leaf hret m q hq (hs.layout ..) (hs.aligned ..)
      hn rfl rfl hx hy hc
  have hf := prepareRow_falls r
  have hal : alignedAll pre s = true := alignedAll_sp pre s (prepareRow_sp r) hs.frame.1
  rw [seqAt_append, Bool.and_eq_true] at link
  obtain ⟨hpre, hpc'⟩ := execute_pre hb hlen hpc ho link.1 hf hal
  have hoe : call % 2 = 0 := by
    change (off + seqSize pre) % 2 = 0
    have hz := seqSize_mod_two pre
    omega
  have hcall := run_call hb hlen hpc' hoe hob hdb link.2 ht
  rw [hpc', hpr] at hcall
  refine ⟨t, ?_, ?_, hsp.trans ((entered_sp _ _ _ _).trans hs.prepare.2.2.2.2.2.2),
    ?_, hw, ?_⟩
  · exact runH_compose hpre hcall
  · exact hp.trans (linkedRet_clear hb hoe)
  · exact hv.trans (exact_output _ _ _ _ hnum)
  · intro a ha
    rw [hm]
    exact row_frame q a ha

end SafegcdTermination.RowCalls
