import M0Crypto.Release.ConstantTime.ConcreteRegs

/-! Preservation of state relations when both executions advance their PC. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)

theorem canonical_ne_pc {r : Nat} (hr : regIndexOk r) : r ≠ 15 := by
  have h := hr.1
  simp [numRegs] at h
  omega

theorem cmp_uses_pc_false {c : Cmp} (hc : cmpIndexOk c) : c.uses 15 = false := by
  have ha := canonical_ne_pc hc.1
  cases hb : c.b with
  | imm n => simp [Cmp.uses, ha, hb]
  | reg r =>
    have hr : regIndexOk r := by simpa [opndIndexOk, hb] using hc.2
    have hne := canonical_ne_pc hr
    simp [Cmp.uses, ha, hb, hne]

/-- Advancing both concrete PCs to the same artifact offset preserves all other
parts of the relational state, given well-formed recorded indices. -/
theorem LowEq.withPC {p : Params} {bytes : List (BitVec 8)} {off next : Nat}
    {st : AbsState} {s₁ s₂ : State} (h : LowEq p bytes off st s₁ s₂)
    (hidx : st.indicesOk) :
    LowEq p bytes next st
      (s₁.setReg 15 (p.base + BitVec.ofNat 32 next))
      (s₂.setReg 15 (p.base + BitVec.ofNat 32 next)) := by
  rcases h with ⟨_, _, hsp₁, hsp₂, hregs, hflags, hcmp,
    hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsize, ?_, ?_⟩
  · simp [State.pc, State.setReg]
  · simp [State.pc, State.setReg]
  · simpa [State.setReg] using hsp₁
  · simpa [State.setReg] using hsp₂
  · intro i hi hi13
    have hi16 : i < 16 := by simp [numRegs] at hi; omega
    have hne : i ≠ 15 := by simp [numRegs] at hi; omega
    change AbsVal.Sem p (st.get i)
      (regAt (s₁.setReg ⟨15, by decide⟩ (p.base + BitVec.ofNat 32 next)) i)
      (regAt (s₂.setReg ⟨15, by decide⟩ (p.base + BitVec.ofNat 32 next)) i)
    rw [regAt_setReg_ne s₁ 15 i (by decide) hi16 hne,
      regAt_setReg_ne s₂ 15 i (by decide) hi16 hne]
    exact hregs i hi hi13
  · exact hflags
  · intro c hc
    have hwf := hidx.1 c hc
    have hu := cmp_uses_pc_false hwf
    have h := hcmp c hc
    exact ⟨(cmpSem_setReg (by decide) _ hwf hu).mpr h.1,
      (cmpSem_setReg (by decide) _ hwf hu).mpr h.2⟩
  · exact hstk
  · intro f hf
    have hfi := hidx.2.1 f hf
    have h := hrel f hf
    exact ⟨(factSem_setReg (by decide) _ hfi (canonical_ne_pc hfi.1)
      (canonical_ne_pc hfi.2)).mpr h.1,
      (factSem_setReg (by decide) _ hfi (canonical_ne_pc hfi.1)
      (canonical_ne_pc hfi.2)).mpr h.2⟩
  · intro l hl
    have hli := hidx.2.2 l hl
    have h := hlnk l hl
    exact ⟨(lnkSem_setReg (by decide) _ hli (canonical_ne_pc hli.1)
      (canonical_ne_pc hli.2)).mpr h.1,
      (lnkSem_setReg (by decide) _ hli (canonical_ne_pc hli.1)
      (canonical_ne_pc hli.2)).mpr h.2⟩
  · exact hcode₁
  · exact hcode₂

end M0Crypto.Release.ConstantTime
