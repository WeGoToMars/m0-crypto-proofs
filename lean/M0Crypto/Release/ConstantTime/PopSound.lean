import M0Crypto.Release.ConstantTime.LoadRegsSound

/-! Relational execution of stack register restores. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

/-- A checked pop without PC preserves the paired execution relation, or
faults identically if its stack accesses are unaligned. -/
theorem certPoint_pop_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.pop l false :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  let next := loadStackRegs st.stk st.spOff (listRegs l) st
  have hout : out = ⟨[(.pt (off + (Instr.pop l false).size) b.ctx,
      { next with spOff := st.spOff + (4 * bitCount l : Nat) })], []⟩ := by
    have ht := hx
    simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at ht
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ht
    split at ht
    · contradiction
    · rw [pop_load_fold] at ht
      simpa [fall, regsOf, bitCount, next, Instr.size] using ht.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  have hpc := h.withPC hidx (next := off + (Instr.pop l false).size)
  have hloads := loadStackRegs_sound st.stk st.spOff (listRegs l) st _ _ hidx rfl hpc
  have hnidx := loadStackRegs_indices st.stk st.spOff (listRegs l) st hidx
  have hnext := hloads.withSP hnidx (st.spOff + (4 * bitCount l : Nat))
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have haddr : p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)) =
      (p.sp0 + BitVec.ofInt 32 st.spOff) + BitVec.ofNat 32 (4 * bitCount l) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp [Int.natCast_mul, BitVec.add_assoc] at haddr
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hacc : (Instr.pop l false).accesses s₁ = (Instr.pop l false).accesses s₂ := by
    simp [Instr.accesses, hsp₁, hsp₂]
  by_cases hal : ((Instr.pop l false).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.pop l false).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have he₁ : (Instr.pop l false).exec s₁ = .ok
        ((loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.pop l false).size)))
          (p.sp0 + BitVec.ofInt 32 st.spOff) ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
          (p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)))) := by
      simp [Instr.exec, hpc₁, hsp₁, haddr, BitVec.ofNat_add, BitVec.add_assoc]
    have he₂ : (Instr.pop l false).exec s₂ = .ok
        ((loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.pop l false).size)))
          (p.sp0 + BitVec.ofInt 32 st.spOff) ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
          (p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)))) := by
      simp [Instr.exec, hpc₂, hsp₂, haddr, BitVec.ofNat_add, BitVec.add_assoc]
    have hs₁ := step_of_instrAt hc₁ off (.pop l false) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.pop l false) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.pop l false) hdecode hlen
    have hd₂ := decode_at hc₂ off (.pop l false) hdecode hlen
    have hal₂ : ((Instr.pop l false).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]

/-- A checked return in a call context takes the saved return offset from the
stack and sends the updated state to the caller context. -/
theorem pop_internal_transfer {env : Env} {off ret : Nat} {st : AbsState} {out : Out}
    (l : BitVec 8) (hx : xfer env off (some ret) (.pop l true) st = .ok out) :
    stkGet st.stk (st.spOff + (4 * bitCount l : Nat)) = .ret ret ∧
    out = ⟨[(.pt ret none,
      { loadStackRegs st.stk st.spOff (listRegs l) st with
        spOff := st.spOff + (4 * (bitCount l + 1) : Nat) })], []⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx
  simp only [ite_true] at hx
  split at hx
  · contradiction
  · rw [pop_load_fold] at hx
    simp only [regsOf, List.length_map, bitCount, Int.natCast_mul, Int.natCast_add] at hx ⊢
    cases hv : stkGet st.stk (st.spOff + 4 * ((listRegs l).length : Int)) with
    | ret r =>
      by_cases hr : r = ret
      · subst r
        simpa [hv] using hx.symm
      · simp [hv, hr] at hx
    | hi | lo | num _ _ | sp _ _ | lr0 => simp [hv] at hx

/-- A checked return restores registers and transfers both executions to the
caller block when its target address is a valid aligned instruction address. -/
theorem certPoint_pop_return_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off ret : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.pop l true])
    (hctx : b.ctx = some ret) (h : LowEq p bytes off st s₁ s₂)
    (htarget : (((p.base + BitVec.ofNat 32 ret) ||| 1#32) &&& ~~~1#32) =
      p.base + BitVec.ofNat 32 ret)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  change (((p.base + BitVec.ofNat 32 ret) ||| 1#32) &&& 4294967294#32) =
    p.base + BitVec.ofNat 32 ret at htarget
  have hf := certPoint_final_successors hc hm hp hx
  have hx' : xfer env off (some ret) (.pop l true) st = .ok out := by simpa [hctx] using hx
  have ⟨hslot, hout⟩ := pop_internal_transfer l hx'
  let next := loadStackRegs st.stk st.spOff (listRegs l) st
  let spNext := st.spOff + (4 * (bitCount l + 1) : Nat)
  have hpc := h.withPC hidx (next := off + (Instr.pop l true).size)
  have hloads := loadStackRegs_sound st.stk st.spOff (listRegs l) st _ _ hidx rfl hpc
  have hnidx := loadStackRegs_indices st.stk st.spOff (listRegs l) st hidx
  have hsprel := hloads.withSP hnidx spNext
  have hfinal := hsprel.withPC hnidx (next := ret)
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have ha : p.sp0 + BitVec.ofInt 32 st.spOff + BitVec.ofNat 32 (4 * bitCount l) =
      p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  have hv := h.stack (st.spOff + (4 * bitCount l : Nat))
  rw [hslot] at hv
  have hv' := hv
  simp only [AbsVal.Sem] at hv'
  have hv₁ : M0Crypto.Armv6M.read32 s₁.mem (s₁.sp + BitVec.ofNat 32 (4 * bitCount l)) =
      (p.base + BitVec.ofNat 32 ret) ||| 1#32 := by simpa [hsp₁, ha] using hv'.1
  have hv₂ : M0Crypto.Armv6M.read32 s₂.mem (s₂.sp + BitVec.ofNat 32 (4 * bitCount l)) =
      (p.base + BitVec.ofNat 32 ret) ||| 1#32 := by simpa [hsp₂, ha, hv'.1] using hv'.2.trans hv'.1
  have haddr : p.sp0 + BitVec.ofInt 32 spNext =
      (p.sp0 + BitVec.ofInt 32 st.spOff) + BitVec.ofNat 32 (4 * (bitCount l + 1)) := by
    simp only [spNext, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp [BitVec.add_assoc] at haddr
  simp only [hsp₁, BitVec.add_assoc] at hv₁
  simp only [hsp₂, BitVec.add_assoc] at hv₂
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hacc : (Instr.pop l true).accesses s₁ = (Instr.pop l true).accesses s₂ := by
    simp [Instr.accesses, hsp₁, hsp₂]
  by_cases hal : ((Instr.pop l true).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.pop l true).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    let u₁ := ((loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.pop l true).size)))
      (p.sp0 + BitVec.ofInt 32 st.spOff) ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
      (p.sp0 + BitVec.ofInt 32 spNext)).setReg 15 (p.base + BitVec.ofNat 32 ret)
    let u₂ := ((loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.pop l true).size)))
      (p.sp0 + BitVec.ofInt 32 st.spOff) ((listRegs l).map M0Crypto.Armv6M.LowReg.toReg)).setReg 13
      (p.sp0 + BitVec.ofInt 32 spNext)).setReg 15 (p.base + BitVec.ofNat 32 ret)
    have he₁ : (Instr.pop l true).exec s₁ = .ok u₁ := by
      simp [Instr.exec, hpc₁, hsp₁, hv₁, htarget, haddr, u₁,
        BitVec.ofNat_add, BitVec.add_assoc]
    have he₂ : (Instr.pop l true).exec s₂ = .ok u₂ := by
      simp [Instr.exec, hpc₂, hsp₂, hv₂, htarget, haddr, u₂,
        BitVec.ofNat_add, BitVec.add_assoc]
    have hs₁ := step_of_instrAt hc₁ off (.pop l true) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.pop l true) hpc₂ heven hdecode hlen hal₂ he₂
    have hmember : (Tgt.pt ret none, { next with spOff := spNext }) ∈ out.succs := by
      rw [hout]
      simp [next, spNext]
    obtain ⟨target, hfind, hmem, hsub⟩ := checked_successor_relation hf hmember hi hfinal
    have hn := certAt_resolved hc hfind hmem hsub
    unfold PairedStep
    simp only [hs₁, hs₂]
    simpa [h.pc_eq, hacc, u₁, u₂, next, spNext] using hn
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
