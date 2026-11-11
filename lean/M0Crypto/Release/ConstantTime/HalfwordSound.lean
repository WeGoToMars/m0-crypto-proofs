import M0Crypto.Release.ConstantTime.StackAddressSound

/-! Paired semantics of unsigned halfword extension. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg)
open M0Crypto.Thumb

def uxthResult : AbsVal → AbsVal
  | .num a b => if b < 65536 then .num a b else .num 0 65535
  | .hi => .hi
  | _ => .num 0 65535

/-- The abstract halfword-extension result preserves equality and bounds. -/
theorem uxthResult_sound {p : Params} {a : AbsVal} {x y : Word} (h : AbsVal.Sem p a x y) :
    AbsVal.Sem p (uxthResult a) ((x.setWidth 16).setWidth 32) ((y.setWidth 16).setWidth 32) := by
  have hbound (w : Word) : ((w.setWidth 16).setWidth 32).toNat ≤ 65535 := by
    simp only [BitVec.toNat_setWidth]
    omega
  have heq (hp : a.pub = true) : x = y := AbsVal.sem_public h hp
  cases a with
  | hi => trivial
  | num l u =>
    obtain ⟨rfl, hl, hu⟩ := h
    by_cases hsmall : u < 65536
    · have hx : x.toNat < 65536 := by omega
      have hv : ((x.setWidth 16).setWidth 32).toNat = x.toNat := by
        simp only [BitVec.toNat_setWidth]
        rw [Nat.mod_eq_of_lt hx]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [uxthResult, hsmall, ↓reduceIte, AbsVal.Sem]
      exact ⟨trivial, by rw [hv]; exact hl, by rw [hv]; exact hu⟩
    · simp only [uxthResult, hsmall, ↓reduceIte, AbsVal.Sem]
      exact ⟨trivial, Nat.zero_le _, hbound x⟩
  | lo | sp | ret | lr0 =>
    have hxy : x = y := heq (by rfl)
    simp only [uxthResult, AbsVal.Sem]
    exact ⟨by rw [hxy], Nat.zero_le _, hbound x⟩

/-- Unsigned halfword extension preserves the paired state relation. -/
theorem uxth_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.uxth d m).exec s₁ = .ok u₁ ∧
      (Instr.uxth d m).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.uxth d m).size)
        (st.set d.val (uxthResult (st.get m.val))) u₁ u₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hv := uxthResult_sound (lowReg_sem m h)
  have hw := paired_setReg_sound hd hidx (h.withPC hidx (next := off + (Instr.uxth d m).size)) hv
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked unsigned halfword extension advances paired certificate executions. -/
theorem certPoint_uxth_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.uxth d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.uxth d m).size) b.ctx,
      st.set d.val (uxthResult (st.get m.val)))], []⟩ := by
    cases hv : st.get m.val <;> simp_all [xfer, xferCore, fall, uxthResult]
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := uxth_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.uxth d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.uxth d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
