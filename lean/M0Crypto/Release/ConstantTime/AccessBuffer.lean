import M0Crypto.Release.ConstantTime.AccessStackLoad

/-! Soundness of buffer accesses, conditional on concrete separation. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem State LowReg read32)
open M0Crypto.Thumb

/-- A store does not alter a byte outside its write footprint. -/
theorem storeMem_other (op : MemOp) (m : Mem) (a v q : Word)
    (h : ∀ k, k < op.width → q ≠ a + BitVec.ofNat 32 k) :
    storeMem op m a v q = m q := by
  cases op with
  | str => exact M0Crypto.Armv6M.write32_other m a v q h
  | strh =>
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    simp only [BitVec.add_zero] at h0
    exact write16_other m a v q h0 h1
  | strb =>
    have h0 := h 0 (by decide)
    simp only [BitVec.add_zero] at h0
    exact write8_other m a v q h0
  | ldr | ldrh | ldrb => rfl

/-- A store separated from the artifact preserves its bytes. -/
theorem buffer_store_code {m : Mem} {base a v : Word} {bytes : List (BitVec 8)}
    (op : MemOp) (hc : CodeAt m base bytes)
    (hd : M0Crypto.Release.Frame.Disj base bytes.length a op.width) :
    CodeAt (storeMem op m a v) base bytes := by
  intro i hi
  rw [storeMem_other op m a v _ (by
    intro k hk
    exact M0Crypto.Release.Frame.ne_of_disj hd.1 hd.2.1 hd.2.2 hi hk)]
  exact hc i hi

/-- A store disjoint from the stack window preserves all tracked public words. -/
theorem buffer_store_stack {p : Params} {s : Stk} {m₁ m₂ : Mem} {a v₁ v₂ : Word}
    (w : StackWindow) (op : MemOp) (hslots : s.slotsOk w) (hs : StkSem p s m₁ m₂)
    (hd : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 w.below)
      (w.below + w.above) a op.width) :
    StkSem p s (storeMem op m₁ a v₁) (storeMem op m₂ a v₂) := by
  intro o
  cases hp : (stkGet s o).pub with
  | false =>
    have hv : stkGet s o = .hi := by cases hv : stkGet s o <;> simp_all [AbsVal.pub]
    simp [hv, AbsVal.Sem]
  | true =>
    obtain ⟨v, hv⟩ := stkGet_public_mem s o hp
    have ⟨_, ho⟩ := hslots (o, v) hv
    have ho' := ho
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at ho'
    have ha := stack_offset_rebase p.sp0 w.below o ho'.1
    have hb (i : Nat) (hi : i < 4) : ∀ k, k < op.width →
        p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 k := by
      intro k hk
      rw [ha, ofNat_add_assoc]
      apply M0Crypto.Release.Frame.ne_of_disj hd.1 hd.2.1 hd.2.2 _ hk
      have hcast : (((o + (w.below : Int)).toNat : Nat) : Int) = o + (w.below : Int) :=
        Int.toNat_of_nonneg (by omega)
      omega
    have hread (m : Mem) (value : Word) :
        read32 (storeMem op m a value) (p.sp0 + BitVec.ofInt 32 o) =
          read32 m (p.sp0 + BitVec.ofInt 32 o) := by
      apply M0Crypto.Release.Frame.read32_congr
      intro k hk
      exact storeMem_other op m a value _ (hb k hk)
    rw [hread m₁ v₁, hread m₂ v₂]
    exact hs o

/-- Public non-stack addresses use the buffer-store transfer. -/
theorem access_public_buffer_store (env : Env) (st : AbsState) (a : AbsVal) (w t : Nat)
    (hp : a.pub = true) (hn : a.isSp = false) :
    access env st a w false t = .ok (st, [.store]) := by
  cases a <;> simp_all [access, AbsVal.pub, AbsVal.isSp]

/-- Immediate-offset buffer stores preserve paired states under concrete
code and stack separation for the written range. -/
theorem memImm_buffer_store_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State}
    (op : MemOp) (t n : LowReg) (imm : BitVec 5) (hop : op.isLoad = false)
    (hpub : ((st.get n.val).addK (imm.toNat * op.width)).pub = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hslots : st.stk.slotsOk env.win)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length
      (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width)
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
      (env.win.below + env.win.above) (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width) :
    ∃ u₁ u₂, (Instr.memImm op t n imm).exec s₁ = .ok u₁ ∧
      (Instr.memImm op t n imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memImm op t n imm).size) st u₁ u₂ := by
  have haddr := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
  have heq := AbsVal.sem_public haddr hpub
  have hstk := buffer_store_stack (v₁ := s₁.reg t) (v₂ := s₂.reg t) env.win op hslots h.stack hstack
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hcode₁ := buffer_store_code (v := s₁.reg t) op hc₁ hcode
  have hcode₂ := buffer_store_code (v := s₂.reg t) op hc₂ hcode
  have hnext := h.withPC hidx (next := off + (Instr.memImm op t n imm).size)
  rcases hnext with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, _, hrel,
    hlnk, hsize, _, _⟩
  have hp₁ := h.pc
  have hp₂ := h.pc_eq.trans h.pc
  have htne : t.toReg ≠ 15 := by
    intro he
    have ht := t.isLt
    have heval := congrArg Fin.val he
    simp [M0Crypto.Armv6M.LowReg.toReg] at heval
    omega
  refine ⟨{ (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.memImm op t n imm).size))) with
      mem := storeMem op s₁.mem (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) (s₁.reg t) },
    { (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.memImm op t n imm).size))) with
      mem := storeMem op s₂.mem (s₂.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) (s₂.reg t) }, ?_, ?_, ?_⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, storeMem, hp₁, ofNat_add_assoc,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, htne]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, storeMem, hp₂, ofNat_add_assoc,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, htne]
  · refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, ?_, hrel, hlnk, hsize, hcode₁, ?_⟩
    · simpa only [← heq] using hstk
    · simpa only [← heq] using hcode₂

/-- Register-offset buffer stores preserve paired states under concrete
code and stack separation for the written range. -/
theorem memReg_buffer_store_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State}
    (op : MemOp) (t n m : LowReg) (hop : op.isLoad = false)
    (hpub : ((st.get n.val).add (st.get m.val)).pub = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hslots : st.stk.slotsOk env.win)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length
      (s₁.reg n + s₁.reg m) op.width)
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
      (env.win.below + env.win.above) (s₁.reg n + s₁.reg m) op.width) :
    ∃ u₁ u₂, (Instr.memReg op t n m).exec s₁ = .ok u₁ ∧
      (Instr.memReg op t n m).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memReg op t n m).size) st u₁ u₂ := by
  have haddr := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
  have heq := AbsVal.sem_public haddr hpub
  have hstk := buffer_store_stack (v₁ := s₁.reg t) (v₂ := s₂.reg t) env.win op hslots h.stack hstack
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hcode₁ := buffer_store_code (v := s₁.reg t) op hc₁ hcode
  have hcode₂ := buffer_store_code (v := s₂.reg t) op hc₂ hcode
  have hnext := h.withPC hidx (next := off + (Instr.memReg op t n m).size)
  rcases hnext with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, _, hrel,
    hlnk, hsize, _, _⟩
  have hp₁ := h.pc
  have hp₂ := h.pc_eq.trans h.pc
  have htne : t.toReg ≠ 15 := by
    intro he
    have ht := t.isLt
    have heval := congrArg Fin.val he
    simp [M0Crypto.Armv6M.LowReg.toReg] at heval
    omega
  refine ⟨{ (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.memReg op t n m).size))) with
      mem := storeMem op s₁.mem (s₁.reg n + s₁.reg m) (s₁.reg t) },
    { (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.memReg op t n m).size))) with
      mem := storeMem op s₂.mem (s₂.reg n + s₂.reg m) (s₂.reg t) }, ?_, ?_, ?_⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, storeMem, hp₁, ofNat_add_assoc,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, htne]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, storeMem, hp₂, ofNat_add_assoc,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, htne]
  · refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, ?_, hrel, hlnk, hsize, hcode₁, ?_⟩
    · simpa only [← heq] using hstk
    · simpa only [← heq] using hcode₂

/-- A non-stack immediate store advances paired certificate executions when
its concrete write is disjoint from the code and tracked stack. -/
theorem certPoint_memImm_buffer_store_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n : LowReg) (imm : BitVec 5)
    (hop : op.isLoad = false)
    (hn : ((st.get n.val).addK (imm.toNat * op.width)).isSp = false)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memImm op t n imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length
      (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width)
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
      (env.win.below + env.win.above) (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have hslot := ((AbsState.stackCheck_iff env.win st).mp (certPoint_stackCheck hslots hm hp)).2
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hpub : ((st.get n.val).addK (imm.toNat * op.width)).pub = true := by
    cases ha : (st.get n.val).addK (imm.toNat * op.width) <;>
      simp_all [xfer, xferCore, access, AbsVal.pub]
  have haccess := access_public_buffer_store env st _ op.width t.val hpub hn
  have hout : out = ⟨[(.pt (off + 2) b.ctx, st)], [.store]⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, hop, haccess] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memImm_accesses_eq op t n imm hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memImm op t n imm).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memImm_buffer_store_sound op t n imm hop hpub hidx hrel hslot hcode hstack
    have hs₁ := step_of_instrAt hc₁ off (.memImm op t n imm) hrel.pc heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.memImm op t n imm) (hrel.pc_eq.trans hrel.pc)
      heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [hrel.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.memImm op t n imm) hdecode hlen
    have hd₂ := decode_at hc₂ off (.memImm op t n imm) hdecode hlen
    have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    apply certAt_paired_fault (fault := .unaligned s₁.pc)
    · simp [step, hrel.pc, heven', hd₁, hal]
    · simp [step, hrel.pc, hrel.pc_eq.trans hrel.pc, heven', hd₂, hal₂]

/-- A non-stack register-offset store advances paired certificate executions when
its concrete write is disjoint from the code and tracked stack. -/
theorem certPoint_memReg_buffer_store_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n m : LowReg)
    (hop : op.isLoad = false)
    (hn : ((st.get n.val).add (st.get m.val)).isSp = false)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memReg op t n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length
      (s₁.reg n + s₁.reg m) op.width)
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
      (env.win.below + env.win.above) (s₁.reg n + s₁.reg m) op.width)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have hslot := ((AbsState.stackCheck_iff env.win st).mp (certPoint_stackCheck hslots hm hp)).2
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hpub : ((st.get n.val).add (st.get m.val)).pub = true := by
    cases ha : (st.get n.val).add (st.get m.val) <;>
      simp_all [xfer, xferCore, access, AbsVal.pub]
  have haccess := access_public_buffer_store env st _ op.width t.val hpub hn
  have hout : out = ⟨[(.pt (off + 2) b.ctx, st)], [.store]⟩ := by
    cases hna : st.get n.val <;> cases hma : st.get m.val <;>
      simp_all [xfer, xferCore, AbsVal.add, access, AbsVal.isSp, AbsVal.pub]
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memReg_accesses_eq op t n m hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memReg op t n m).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memReg_buffer_store_sound op t n m hop hpub hidx hrel hslot hcode hstack
    have hs₁ := step_of_instrAt hc₁ off (.memReg op t n m) hrel.pc heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.memReg op t n m) (hrel.pc_eq.trans hrel.pc)
      heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [hrel.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.memReg op t n m) hdecode hlen
    have hd₂ := decode_at hc₂ off (.memReg op t n m) hdecode hlen
    have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    apply certAt_paired_fault (fault := .unaligned s₁.pc)
    · simp [step, hrel.pc, heven', hd₁, hal]
    · simp [step, hrel.pc, hrel.pc_eq.trans hrel.pc, heven', hd₂, hal₂]

end M0Crypto.Release.ConstantTime
