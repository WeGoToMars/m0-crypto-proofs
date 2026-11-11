import M0Crypto.Release.ConstantTime.StackForgetFrame
import M0Crypto.Release.ConstantTime.AccessAddress

/-! Soundness of stores through checked stack-relative addresses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem write32)
open M0Crypto.Thumb

/-- The memory component of a store operation. -/
def storeMem (op : MemOp) (m : Mem) (a v : Word) : Mem :=
  match op with
  | .str => write32 m a v
  | .strh => write16 m a v
  | .strb => write8 m a v
  | _ => m

/-- A checked stack-address store updates the stack abstraction soundly for
all supported store widths. -/
theorem access_stack_store_sem {env : Env} {p : Params} {st : AbsState}
    {x y : Int} {a₁ a₂ v₁ v₂ : Word} {m₁ m₂ : Mem} {t : Nat}
    (op : MemOp) (hop : op.isLoad = false)
    (haccess : access env st (.sp x y) op.width false t =
      .ok ({ st with stk := stkStore st x y op.width (st.get t) }, []))
    (haddr : AbsVal.Sem p (.sp x y) a₁ a₂)
    (hval : AbsVal.Sem p (st.get t) v₁ v₂)
    (hslots : st.stk.slotsOk env.win)
    (hnarrow : env.win.below + env.win.above < 2 ^ 32)
    (hstack : StkSem p st.stk m₁ m₂) :
    StkSem p (stkStore st x y op.width (st.get t))
      (storeMem op m₁ a₁ v₁) (storeMem op m₂ a₂ v₂) := by
  have hcover : env.win.covers x (y + op.width) = true := by
    simp only [access] at haccess
    split at haccess <;> simp_all
  obtain ⟨o, hxo, hoy, ha₁, ha₂⟩ := haddr
  subst a₂
  subst a₁
  have ho : env.win.covers o (o + op.width) = true := by
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hcover ⊢
    omega
  cases op with
  | str =>
    exact stkStore_word_write_sem env.win hnarrow hslots ho hxo hoy hstack hval
  | strh =>
    exact stkStore_half_write_sem env.win hnarrow hslots ho hxo hoy hstack
  | strb =>
    exact stkStore_byte_write_sem env.win hnarrow hslots ho hxo hoy hstack
  | ldr | ldrh | ldrb => simp [MemOp.isLoad] at hop

/-- A checked immediate-offset stack store preserves the paired state when
its concrete writes also preserve the instruction bytes. -/
theorem memImm_stack_store_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hop : op.isLoad = false)
    (ha : (st.get n.val).addK (imm.toNat * op.width) = .sp x y)
    (hcover : env.win.covers x (y + op.width) = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hslots : st.stk.slotsOk env.win)
    (hnarrow : env.win.below + env.win.above < 2 ^ 32)
    (hc₁ : CodeAt (storeMem op s₁.mem
      (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) (s₁.reg t)) p.base bytes)
    (hc₂ : CodeAt (storeMem op s₂.mem
      (s₂.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) (s₂.reg t)) p.base bytes) :
    ∃ u₁ u₂, (Instr.memImm op t n imm).exec s₁ = .ok u₁ ∧
      (Instr.memImm op t n imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memImm op t n imm).size)
        {st with stk := stkStore st x y op.width (st.get t.val)} u₁ u₂ := by
  have hv := lowReg_sem t h
  have haddr := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
  rw [ha] at haddr
  have haccess : access env st (.sp x y) op.width false t.val =
      .ok ({ st with stk := stkStore st x y op.width (st.get t.val) }, []) := by
    simp [access, hcover]
  have hstack := access_stack_store_sem op hop haccess haddr hv hslots hnarrow
    h.stack
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
  · exact ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstack, hrel, hlnk, hsize, hc₁, hc₂⟩

/-- A checked register-offset stack store preserves the paired state when
its concrete writes also preserve the instruction bytes. -/
theorem memReg_stack_store_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hop : op.isLoad = false)
    (ha : (st.get n.val).add (st.get m.val) = .sp x y)
    (hcover : env.win.covers x (y + op.width) = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hslots : st.stk.slotsOk env.win)
    (hnarrow : env.win.below + env.win.above < 2 ^ 32)
    (hc₁ : CodeAt (storeMem op s₁.mem
      (s₁.reg n + s₁.reg m) (s₁.reg t)) p.base bytes)
    (hc₂ : CodeAt (storeMem op s₂.mem
      (s₂.reg n + s₂.reg m) (s₂.reg t)) p.base bytes) :
    ∃ u₁ u₂, (Instr.memReg op t n m).exec s₁ = .ok u₁ ∧
      (Instr.memReg op t n m).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memReg op t n m).size)
        {st with stk := stkStore st x y op.width (st.get t.val)} u₁ u₂ := by
  have hv := lowReg_sem t h
  have haddr := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
  rw [ha] at haddr
  have haccess : access env st (.sp x y) op.width false t.val =
      .ok ({ st with stk := stkStore st x y op.width (st.get t.val) }, []) := by
    simp [access, hcover]
  have hstack := access_stack_store_sem op hop haccess haddr hv hslots hnarrow
    h.stack
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
  · exact ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstack, hrel, hlnk, hsize, hc₁, hc₂⟩

end M0Crypto.Release.ConstantTime
