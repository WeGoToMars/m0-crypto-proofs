import M0Crypto.Release.ConstantTime.RefineSound
import M0Crypto.Release.ConstantTime.BranchEval
import M0Crypto.Release.ConstantTime.StepBounds
import M0Crypto.Release.ConstantTime.BranchTarget
import M0Crypto.Release.ConstantTime.PcSound

/-! Conditional-branch successor selection for paired executions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

/-- A successful transfer contains the successor selected by the concrete
branch. At the designated declassification site, agreement of the two
branch decisions is a separate obligation. -/
theorem bcond_select_successor {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (cond : BitVec 4) (imm : BitVec 8)
    (hx : xfer env off ctx (.bcond cond imm) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂) :
    ∃ target nextSt, relTarget off (bcondDisp imm) = some target ∧
      condPassed cond s₁ = condPassed cond s₂ ∧
      (.pt (if condPassed cond s₁ then target else off + 2) ctx, nextSt) ∈ out.succs ∧
      LowEq p bytes off nextSt s₁ s₂ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hx' := hx
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx'
  cases ht : relTarget off (bcondDisp imm) with
  | none => simp [ht] at hx'
  | some target =>
    simp only [ht] at hx'
    by_cases hd : env.declass = some off
    · simp [hd] at hx'
      subst out
      refine ⟨target, st, rfl, hdeclass hd, ?_, h⟩
      cases condPassed cond s₁ <;> simp
    · simp only [hd, beq_iff_eq, ↓reduceIte] at hx'
      cases hp : condFlagsPub cond.toNat st.fl with
      | false => simp [hp] at hx'
      | true =>
        simp [hp] at hx'
        subst out
        have hagree := condFlagsPub_sound cond st.fl s₁ s₂ h.flags hp
        cases he : evalCond cond.toNat st.fl with
        | some b =>
          have heval := evalCond_sound cond st.fl s₁ s₂ b h.flags he
          refine ⟨target, st, rfl, hagree, ?_, h⟩
          cases hc : condPassed cond s₁ <;> simp_all
        | none =>
          obtain ⟨nextSt, href, hnext⟩ := refine_observed env.win cond (condPassed cond s₁) hidx h rfl
          refine ⟨target, nextSt, rfl, hagree, ?_, hnext⟩
          cases hc : condPassed cond s₁ <;> simp_all

/-- A checked conditional branch takes matching concrete steps. The successor
index obligation is supplied by the certificate's index check. -/
theorem bcond_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (cond : BitVec 4) (imm : BitVec 8)
    (hx : xfer env off ctx (.bcond cond imm) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂)
    (hsucc : ∀ target nextSt, (.pt target ctx, nextSt) ∈ out.succs → nextSt.indicesOk)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.bcond cond imm))
    (hlen : off + (Instr.bcond cond imm).size ≤ bytes.length) :
    ∃ target nextSt t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      ((.pt target ctx, nextSt) ∈ out.succs) ∧ LowEq p bytes target nextSt t₁ t₂ := by
  obtain ⟨target, nextSt, ht, hagree, hmem, hnext⟩ :=
    bcond_select_successor cond imm hx hidx h hdeclass
  let dest := if condPassed cond s₁ then target else off + 2
  have htarget := relTarget_address p.base off target (bcondDisp imm) ht
  have hdisp : BitVec.ofInt 32 (bcondDisp imm) = (imm ++ 0#1).signExtend 32 := by
    simp [bcondDisp]
  rw [hdisp] at htarget
  simp only [BitVec.add_assoc] at htarget
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hrel := hnext.withPC (hsucc dest nextSt hmem) (next := dest)
  have he₁ : (Instr.bcond cond imm).exec s₁ =
      .ok (s₁.setReg 15 (p.base + BitVec.ofNat 32 dest)) := by
    cases hc : condPassed cond s₁ <;>
      simp [Instr.exec, Instr.size, dest, hc, hpc₁, ← htarget, BitVec.ofNat_add, BitVec.add_assoc]
  have he₂ : (Instr.bcond cond imm).exec s₂ =
      .ok (s₂.setReg 15 (p.base + BitVec.ofNat 32 dest)) := by
    cases hc : condPassed cond s₁ <;>
      simp [Instr.exec, Instr.size, dest, hc, ← hagree, hpc₂, ← htarget, BitVec.ofNat_add, BitVec.add_assoc]
  have hs₁ := step_of_instrAt hc₁ off (.bcond cond imm) hpc₁ heven hi hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.bcond cond imm) hpc₂ heven hi hlen
    (by simp [Instr.accesses]) he₂
  refine ⟨dest, nextSt, _, _, ⟨s₁.pc, .bcond cond imm, []⟩, ?_, ?_, hmem, hrel⟩
  · simpa [Instr.accesses] using hs₁
  · simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
