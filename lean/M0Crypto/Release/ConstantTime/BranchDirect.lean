import M0Crypto.Release.ConstantTime.BranchTarget
import M0Crypto.Release.ConstantTime.PcSound
import M0Crypto.Release.ConstantTime.StepBounds

/-! Soundness of unconditional direct branch transfer. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

/-- A checked unconditional branch has matching concrete steps and events and
lands at the analyzed target. -/
theorem branch_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (imm : BitVec 11) (hx : xfer env off ctx (.b imm) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.b imm))
    (hlen : off + (Instr.b imm).size ≤ bytes.length) :
    ∃ target t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      out.sites = [] ∧ ((.pt target ctx, st) ∈ out.succs) ∧
      LowEq p bytes target st t₁ t₂ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hx' := hx
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx'
  cases ht : relTarget off (bDisp imm) with
  | none => simp [ht] at hx'
  | some target =>
    simp only [ht, if_true, Except.ok.injEq] at hx'
    subst out
    have htarget := relTarget_address p.base off target (bDisp imm) ht
    have hdisp : BitVec.ofInt 32 (bDisp imm) = (imm ++ 0#1).signExtend 32 := by
      simp [bDisp]
    rw [hdisp] at htarget
    have hpc₁ := h.pc
    have hpc₂ := h.pc_eq.trans hpc₁
    have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
    have hrel := h.withPC hidx (next := target)
    have he₁ : (Instr.b imm).exec s₁ =
        .ok (s₁.setReg 15 (p.base + BitVec.ofNat 32 target)) := by
      simp [Instr.exec, hpc₁, ← htarget]
    have he₂ : (Instr.b imm).exec s₂ =
        .ok (s₂.setReg 15 (p.base + BitVec.ofNat 32 target)) := by
      simp [Instr.exec, hpc₂, ← htarget]
    have hs₁ := step_of_instrAt hc₁ off (.b imm) hpc₁ heven hi hlen (by simp [Instr.accesses]) he₁
    have hs₂ := step_of_instrAt hc₂ off (.b imm) hpc₂ heven hi hlen (by simp [Instr.accesses]) he₂
    refine ⟨target, _, _, ⟨s₁.pc, .b imm, []⟩, ?_, ?_, rfl, ?_, hrel⟩
    · simpa [Instr.accesses] using hs₁
    · simpa [Instr.accesses, h.pc_eq] using hs₂
    · simp

end M0Crypto.Release.ConstantTime
