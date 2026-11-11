import M0Crypto.Release.ConstantTime.Reach

/-! Paired execution of direct calls. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

/-- A checked direct call takes matching machine steps, records the return
address, and enters the validated callee block. -/
theorem certPoint_call_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (imm : BitVec 25)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.bl imm])
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hf := certPoint_final_successors hc hm hp hx
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hx' := hx
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx'
  cases hctx : b.ctx with
  | some r => simp [hctx] at hx'
  | none =>
    simp only [hctx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hx'
    cases ht : relTarget off (blDisp imm) with
    | none => simp [ht] at hx'
    | some target =>
      simp only [ht, Except.ok.injEq] at hx'
      subst out
      have htarget := relTarget_address p.base off target (blDisp imm) ht
      have hdisp : BitVec.ofInt 32 (blDisp imm) = imm.signExtend 32 := by simp [blDisp]
      rw [hdisp] at htarget
      simp only [BitVec.add_assoc] at htarget
      let link := (p.base + BitVec.ofNat 32 (off + 4)) ||| 1#32
      have hval : AbsVal.Sem p (.ret (off + 4)) link link := by simp [AbsVal.Sem, link]
      have hreg : regIndexOk 14 := by simp [regIndexOk, numRegs]
      have hwrite := paired_setReg_sound hreg hidx hrel hval
      have hnext := hwrite.withPC (AbsState.indicesOk_set hidx) (next := target)
      have hpc₁ := hrel.pc
      have hpc₂ := hrel.pc_eq.trans hpc₁
      have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
      have he₁ : (Instr.bl imm).exec s₁ =
          .ok ((s₁.setReg 14 link).setReg 15 (p.base + BitVec.ofNat 32 target)) := by
        simp [Instr.exec, hpc₁, ← htarget, link, BitVec.ofNat_add, BitVec.add_assoc]
      have he₂ : (Instr.bl imm).exec s₂ =
          .ok ((s₂.setReg 14 link).setReg 15 (p.base + BitVec.ofNat 32 target)) := by
        simp [Instr.exec, hpc₂, ← htarget, link, BitVec.ofNat_add, BitVec.add_assoc]
      have hs₁ := step_of_instrAt hc₁ off (.bl imm) hpc₁ heven hdecode hlen
        (by simp [Instr.accesses]) he₁
      have hs₂ := step_of_instrAt hc₂ off (.bl imm) hpc₂ heven hdecode hlen
        (by simp [Instr.accesses]) he₂
      have hmem : (Tgt.pt target (some (off + 4)), st.set 14 (.ret (off + 4))) ∈
          [(Tgt.pt target (some (off + 4)), st.set 14 (.ret (off + 4)))] := by simp
      obtain ⟨next, hfind, hmember, hsub⟩ := checked_successor_relation hf hmem hi hnext
      have hn := certAt_resolved hc hfind hmember hsub
      unfold PairedStep
      simp only [hs₁, hs₂]
      simpa [Instr.accesses, hrel.pc_eq] using hn

end M0Crypto.Release.ConstantTime
