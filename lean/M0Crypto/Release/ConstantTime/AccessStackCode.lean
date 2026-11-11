import M0Crypto.Release.ConstantTime.AccessStackStore
import M0Crypto.Release.ConstantTime.StackStoreSound
import M0Crypto.Release.ConstantTime.Reach

/-! Code preservation for writes inside the stack window. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem write32)
open M0Crypto.Thumb

/-- Any supported store contained in a stack window disjoint from code leaves
the artifact intact. -/
theorem codeAt_stack_store {m : Mem} {base sp value : Word} {bytes : List (BitVec 8)}
    (w : StackWindow) (o : Int) (op : MemOp) (hop : op.isLoad = false)
    (hcode : CodeAt m base bytes)
    (hdisj : M0Crypto.Release.Frame.Disj base bytes.length
      (sp - BitVec.ofNat 32 w.below) (w.below + w.above))
    (hwin : w.covers o (o + op.width) = true) :
    CodeAt (storeMem op m (sp + BitVec.ofInt 32 o) value) base bytes := by
  intro i hi
  have hbyte : ∀ k, k < op.width →
      base + BitVec.ofNat 32 i ≠ (sp + BitVec.ofInt 32 o) + BitVec.ofNat 32 k := by
    intro k hk
    have hwin' := hwin
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hwin'
    rw [stack_offset_rebase sp w.below o hwin'.1, ofNat_add_assoc]
    apply M0Crypto.Release.Frame.ne_of_disj hdisj.1 hdisj.2.1 hdisj.2.2 hi
    have hk' : (((o + (w.below : Int)).toNat : Nat) : Int) = o + (w.below : Int) :=
      Int.toNat_of_nonneg (by omega)
    omega
  cases op with
  | str =>
    rw [show storeMem .str m (sp + BitVec.ofInt 32 o) value =
      write32 m (sp + BitVec.ofInt 32 o) value from rfl]
    rw [M0Crypto.Armv6M.write32_other _ _ _ _ (by simpa [MemOp.width] using hbyte)]
    exact hcode i hi
  | strh =>
    have h0 := hbyte 0 (by decide)
    have h1 := hbyte 1 (by decide)
    simp only [BitVec.add_zero] at h0
    rw [show storeMem .strh m (sp + BitVec.ofInt 32 o) value =
      write16 m (sp + BitVec.ofInt 32 o) value from rfl]
    rw [write16_other _ _ _ _ h0 h1]
    exact hcode i hi
  | strb =>
    have h0 := hbyte 0 (by decide)
    simp only [BitVec.add_zero] at h0
    rw [show storeMem .strb m (sp + BitVec.ofInt 32 o) value =
      write8 m (sp + BitVec.ofInt 32 o) value from rfl]
    rw [write8_other _ _ _ _ h0]
    exact hcode i hi
  | ldr | ldrh | ldrb => simp [MemOp.isLoad] at hop

/-- The abstract stack-address interpretation and its checked range discharge
code preservation in both executions. -/
theorem access_stack_store_code {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {x y : Int} {a₁ a₂ v₁ v₂ : Word} {m₁ m₂ : Mem}
    (op : MemOp) (hop : op.isLoad = false)
    (haddr : AbsVal.Sem p (.sp x y) a₁ a₂)
    (hcover : env.win.covers x (y + op.width) = true)
    (hc₁ : CodeAt m₁ p.base bytes) (hc₂ : CodeAt m₂ p.base bytes)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above)) :
    CodeAt (storeMem op m₁ a₁ v₁) p.base bytes ∧
    CodeAt (storeMem op m₂ a₂ v₂) p.base bytes := by
  obtain ⟨o, hxo, hoy, ha₁, ha₂⟩ := haddr
  subst a₂
  subst a₁
  have ho : env.win.covers o (o + op.width) = true := by
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hcover ⊢
    omega
  exact ⟨codeAt_stack_store env.win o op hop hc₁ hdisj ho,
    codeAt_stack_store env.win o op hop hc₂ hdisj ho⟩

/-- An immediate-offset store classified as a stack access advances paired
certificate executions or produces matching alignment faults. -/
theorem certPoint_memImm_stack_store_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hop : op.isLoad = false)
    (ha : (st.get n.val).addK (imm.toNat * op.width) = .sp x y)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memImm op t n imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have hstack := certPoint_stackCheck hslots hm hp
  have hslot := ((AbsState.stackCheck_iff env.win st).mp hstack).2
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hcover : env.win.covers x (y + op.width) = true := by
    cases hcover' : env.win.covers x (y + op.width) <;>
      simp_all [xfer, xferCore, access]
  have hout : out = ⟨[(.pt (off + 2) b.ctx,
      {st with stk := stkStore st x y op.width (st.get t.val)})], []⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, ha, access, hop, hcover] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memImm_accesses_eq op t n imm hx hrel
  have haddr := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n hrel)
  rw [ha] at haddr
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  have ⟨hcode₁, hcode₂⟩ := access_stack_store_code (v₁ := s₁.reg t) (v₂ := s₂.reg t) op hop haddr hcover hc₁ hc₂ hdisj
  by_cases hal : ((Instr.memImm op t n imm).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memImm_stack_store_sound op t n imm hop ha hcover hidx hrel hslot hwidth hcode₁ hcode₂
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

/-- An register-offset store classified as a stack access advances paired
certificate executions or produces matching alignment faults. -/
theorem certPoint_memReg_stack_store_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hop : op.isLoad = false)
    (ha : (st.get n.val).add (st.get m.val) = .sp x y)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memReg op t n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have hstack := certPoint_stackCheck hslots hm hp
  have hslot := ((AbsState.stackCheck_iff env.win st).mp hstack).2
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hcover : env.win.covers x (y + op.width) = true := by
    cases hcover' : env.win.covers x (y + op.width) <;>
      simp_all [xfer, xferCore, access]
  have hout : out = ⟨[(.pt (off + 2) b.ctx,
      {st with stk := stkStore st x y op.width (st.get t.val)})], []⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, ha, access, hop, hcover] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memReg_accesses_eq op t n m hx hrel
  have haddr := AbsVal.add_sound (lowReg_sem n hrel) (lowReg_sem m hrel)
  rw [ha] at haddr
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  have ⟨hcode₁, hcode₂⟩ := access_stack_store_code (v₁ := s₁.reg t) (v₂ := s₂.reg t) op hop haddr hcover hc₁ hc₂ hdisj
  by_cases hal : ((Instr.memReg op t n m).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memReg_stack_store_sound op t n m hop ha hcover hidx hrel hslot hwidth hcode₁ hcode₂
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
