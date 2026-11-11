import M0Crypto.Release.ConstantTime.CallSound

/-! Return-address observations for paired executions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State read32)
open M0Crypto.Thumb

/-- A return slot labeled as the entry link register contains the same return
address in both executions. -/
theorem return_slot_value {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (l : BitVec 8)
    (h : LowEq p bytes off st s₁ s₂)
    (hslot : stkGet st.stk (st.spOff + (4 * bitCount l : Nat)) = .lr0) :
    read32 s₁.mem (s₁.sp + BitVec.ofNat 32 (4 * bitCount l)) = p.lr0 ∧
    read32 s₂.mem (s₂.sp + BitVec.ofNat 32 (4 * bitCount l)) = p.lr0 := by
  have ha : p.sp0 + BitVec.ofInt 32 st.spOff + BitVec.ofNat 32 (4 * bitCount l) =
      p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  have hs := h.stack (st.spOff + (4 * bitCount l : Nat))
  rw [hslot] at hs
  simp only [AbsVal.Sem] at hs
  constructor
  · simpa [State.sp, h.sp, ha] using hs.1
  · have hsp₂ := h.sp_eq
    simpa [State.sp, hsp₂, h.sp, ha, hs.1] using hs.2.trans hs.1

/-- Successful analysis of an outermost return requires the entry link-register
label in the stack slot loaded into PC. -/
theorem pop_exit_slot {env : Env} {off : Nat} {st : AbsState} {out : Out} (l : BitVec 8)
    (hx : xfer env off none (.pop l true) st = .ok out) :
    stkGet st.stk (st.spOff + (4 * bitCount l : Nat)) = .lr0 := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx
  simp only [ite_true] at hx
  split at hx
  · contradiction
  · simp only [regsOf, List.length_map, bitCount] at hx ⊢
    cases hv : stkGet st.stk (st.spOff + (4 * (listRegs l).length : Nat)) <;>
      simp_all

/-- An outermost checked pop either faults equally on alignment or sends both
executions to the entry return address with the same observation. -/
theorem certPoint_pop_exit_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.pop l true])
    (hctx : b.ctx = none) (h : LowEq p bytes off st s₁ s₂)
    (hlr : p.lr0.getLsbD 0 = true)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (RunRel env cert p bytes (p.lr0 &&& ~~~1#32)) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hx' : xfer env off none (.pop l true) st = .ok out := by simpa [hctx] using hx
  have ⟨hret₁, hret₂⟩ := return_slot_value l h (pop_exit_slot l hx')
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hsp : s₁.sp = s₂.sp := by simpa [State.sp] using h.sp_eq.symm
  have hacc : (Instr.pop l true).accesses s₁ = (Instr.pop l true).accesses s₂ := by
    simp [Instr.accesses, hsp]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  by_cases hal : ((Instr.pop l true).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.pop l true).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    let u₁ := ((loadRegs (s₁.setReg 15 (s₁.pc + BitVec.ofNat 32 (Instr.pop l true).size))
      s₁.sp ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
        (s₁.sp + BitVec.ofNat 32 (4 * (bitCount l + 1)))).setReg 15 (p.lr0 &&& ~~~1#32)
    let u₂ := ((loadRegs (s₂.setReg 15 (s₂.pc + BitVec.ofNat 32 (Instr.pop l true).size))
      s₂.sp ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
        (s₂.sp + BitVec.ofNat 32 (4 * (bitCount l + 1)))).setReg 15 (p.lr0 &&& ~~~1#32)
    have he₁ : (Instr.pop l true).exec s₁ = .ok u₁ := by
      simp [Instr.exec, hret₁, hlr, u₁]
    have he₂ : (Instr.pop l true).exec s₂ = .ok u₂ := by
      simp [Instr.exec, hret₂, hlr, u₂]
    have hs₁ := step_of_instrAt hc₁ off (.pop l true) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.pop l true) hpc₂ heven hdecode hlen hal₂ he₂
    have hpc₁' : u₁.pc = p.lr0 &&& ~~~1#32 := by simp [u₁, State.pc, State.setReg]
    have hpc₂' : u₂.pc = p.lr0 &&& ~~~1#32 := by simp [u₂, State.pc, State.setReg]
    unfold PairedStep
    simp only [hs₁, hs₂]
    simp [h.pc_eq, hacc, RunRel, hpc₁', hpc₂']
  · have hd₁ := decode_at hc₁ off (.pop l true) hdecode hlen
    have hd₂ := decode_at hc₂ off (.pop l true) hdecode hlen
    have hal₂ : ((Instr.pop l true).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]

end M0Crypto.Release.ConstantTime
