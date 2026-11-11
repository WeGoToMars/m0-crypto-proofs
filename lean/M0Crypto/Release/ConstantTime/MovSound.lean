import M0Crypto.Release.ConstantTime.PcSound
import M0Crypto.Release.ConstantTime.WriteSound
import M0Crypto.Release.ConstantTime.StepBounds

/-! Relational soundness of register-to-register moves. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Reg)
open M0Crypto.Thumb

/-- A move between tracked registers preserves the state relation after advancing
past the instruction. The decoder excludes SP and PC as move operands. -/
theorem movHi_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : Reg)
    (hd : regIndexOk d.val) (hm : regIndexOk m.val)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.movHi d m).exec s₁ = .ok t₁ ∧
      (Instr.movHi d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.movHi d m).size) (st.set d.val (st.get m.val)) t₁ t₂ := by
  have hpc₁ := h.pc
  have hpc₂ : s₂.pc = p.base + BitVec.ofNat 32 off := h.pc_eq.trans hpc₁
  have hsrc := h.regs m.val hm.1 hm.2
  have hm16 : m.val < 16 := m.isLt
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hsrc
  have hval₁ : s₁.regs ⟨m.val, hm16⟩ = s₁.regs m := by congr 1
  have hval₂ : s₂.regs ⟨m.val, hm16⟩ = s₂.regs m := by congr 1
  rw [hval₁, hval₂] at hsrc
  have hnext := h.withPC hidx (next := off + (Instr.movHi d m).size)
  have hw := paired_setReg_sound hd hidx hnext hsrc
  have hdeq : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : Reg) = d := by
    apply Fin.ext; rfl
  rw [hdeq] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · simp [Instr.exec, hpc₁, ofNat_add_assoc]
  · simp [Instr.exec, hpc₂, ofNat_add_assoc]

/-- The abstract transfer for a move records exactly the proved successor and no sites. -/
theorem movHi_transfer (env : Env) (off : Nat) (ctx : Option Nat) (st : AbsState)
    (d m : Reg) (hd : regIndexOk d.val) (hm : regIndexOk m.val)
    (hwin : env.win.covers st.spOff st.spOff = true) (hsp : st.spOff ≤ 0) :
    xfer env off ctx (.movHi d m) st =
      .ok ⟨[(.pt (off + (Instr.movHi d m).size) ctx, st.set d.val (st.get m.val))], []⟩ := by
  have hd15 := canonical_ne_pc hd
  have hm15 := canonical_ne_pc hm
  simp [xfer, xferCore, fall, hwin, hsp, hd.2, hd15, hm.2, hm15]

/-- Successful move analysis guarantees both operands are tracked registers. -/
theorem movHi_transfer_indices {env : Env} {off : Nat} {ctx : Option Nat} {st : AbsState}
    {d m : Reg} {out : Out} (h : xfer env off ctx (.movHi d m) st = .ok out) :
    regIndexOk d.val ∧ regIndexOk m.val := by
  unfold xfer at h
  split at h
  · simp only [xferCore] at h
    split at h
    · contradiction
    · rename_i hg
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hg
      refine ⟨⟨?_, hg.1.1.1⟩, ⟨?_, hg.1.2⟩⟩
      · have hh := d.isLt
        simp [numRegs]
        omega
      · have hh := m.isLt
        simp [numRegs]
        omega
  · contradiction

/-- The paired decoded steps emit the same event and reach the proved successor
relation. Decoding and the input indices are obligations of the certificate. -/
theorem movHi_step_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : Reg)
    (hd : regIndexOk d.val) (hm : regIndexOk m.val)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.movHi d m))
    (hlen : off + (Instr.movHi d m).size ≤ bytes.length) :
    ∃ t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      LowEq p bytes (off + (Instr.movHi d m).size) (st.set d.val (st.get m.val)) t₁ t₂ := by
  obtain ⟨t₁, t₂, he₁, he₂, hrel⟩ := movHi_sound d m hd hm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hs₁ := step_of_instrAt hc₁ off (.movHi d m) hpc₁ heven hi hlen (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.movHi d m) hpc₂ heven hi hlen (by simp [Instr.accesses]) he₂
  refine ⟨t₁, t₂, ⟨s₁.pc, .movHi d m, []⟩, ?_, ?_, hrel⟩
  · simpa [Instr.accesses] using hs₁
  · simpa [Instr.accesses, h.pc_eq] using hs₂

/-- A checked move transfer has a matching pair of concrete steps and events. -/
theorem movHi_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (d m : Reg) (hx : xfer env off ctx (.movHi d m) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.movHi d m))
    (hlen : off + (Instr.movHi d m).size ≤ bytes.length) :
    ∃ t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      out.sites = [] ∧
      ((.pt (off + (Instr.movHi d m).size) ctx, st.set d.val (st.get m.val)) ∈ out.succs) ∧
      LowEq p bytes (off + (Instr.movHi d m).size) (st.set d.val (st.get m.val)) t₁ t₂ := by
  have ⟨hd, hm⟩ := movHi_transfer_indices hx
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout := movHi_transfer env off ctx st d m hd hm hw hb.2.1
  rw [hx] at hout
  have heq : out = ⟨[(.pt (off + (Instr.movHi d m).size) ctx,
      st.set d.val (st.get m.val))], []⟩ := by injection hout
  subst out
  obtain ⟨t₁, t₂, e, hs₁, hs₂, hrel⟩ := movHi_step_sound d m hd hm hidx h heven hi hlen
  exact ⟨t₁, t₂, e, hs₁, hs₂, rfl, by simp, hrel⟩

end M0Crypto.Release.ConstantTime
