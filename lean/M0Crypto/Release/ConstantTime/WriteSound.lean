import M0Crypto.Release.ConstantTime.ConcreteRegs

/-! Relational interpretation of paired concrete and abstract register writes. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)

/-- Writing a tracked register in both runs preserves the relational state when the
new concrete values have the assigned label. -/
theorem paired_setReg_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} {r : Nat} {label : AbsVal} {v₁ v₂ : Word}
    (hr : regIndexOk r) (hidx : st.indicesOk)
    (h : LowEq p bytes off st s₁ s₂) (hv : AbsVal.Sem p label v₁ v₂) :
    LowEq p bytes off (st.set r label)
      (s₁.setReg ⟨r, by have := hr.1; simp [numRegs] at this; omega⟩ v₁)
      (s₂.setReg ⟨r, by have := hr.1; simp [numRegs] at this; omega⟩ v₂) := by
  have hr16 : r < 16 := by have := hr.1; simp [numRegs] at this; omega
  have hr15 : r ≠ 15 := by have := hr.1; simp [numRegs] at this; omega
  have h15v : (↑(15 : Fin 16) : Nat) ≠ r := by
    change 15 ≠ r
    exact Ne.symm hr15
  have h13v : (↑(13 : Fin 16) : Nat) ≠ r := by
    change 13 ≠ r
    exact Ne.symm hr.2
  rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp,
    hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsize, ?_, ?_⟩
  · simpa [State.pc, State.setReg, Fin.ext_iff, h15v] using hpc₁
  · simpa [State.pc, State.setReg, Fin.ext_iff, h15v] using hpc₂
  · simpa [State.setReg, Fin.ext_iff, AbsState.set, h13v] using hsp₁
  · simpa [State.setReg, Fin.ext_iff, AbsState.set, h13v] using hsp₂
  · intro i hi hi13
    have hi16 : i < 16 := by simp [numRegs] at hi; omega
    by_cases hir : i = r
    · subst i
      rw [regAt_setReg_self s₁ r hr16 v₁, regAt_setReg_self s₂ r hr16 v₂]
      by_cases hlen : r < st.regs.length
      · simpa [AbsState.set, AbsState.get, regGet, regSet, hr.2, List.getD_eq_getElem?_getD, hlen] using hv
      · simp [AbsState.set, AbsState.get, regGet, regSet, hr.2, List.getD_eq_getElem?_getD, hlen, AbsVal.Sem]
    · rw [regAt_setReg_ne s₁ r i hr16 hi16 hir v₁,
          regAt_setReg_ne s₂ r i hr16 hi16 hir v₂]
      have old := hregs i hi hi13
      simpa [AbsState.set, AbsState.get, regGet, regSet, hr.2, hi13, hir, Ne.symm hir,
        List.getD_eq_getElem?_getD] using old
  · cases hc : st.fl.cmp with
    | none => simpa [FlagSem, AbsState.set, AFl.touch, State.setReg, hc] using hflags
    | some c =>
      cases hu : c.uses r <;> simpa [FlagSem, AbsState.set, AFl.touch, State.setReg, hc, hu] using hflags
  · intro c hc
    have hold : st.fl.cmp = some c := by
      cases hcmpOld : st.fl.cmp with
      | none => simp [AbsState.set, AFl.touch, hcmpOld] at hc
      | some d =>
        by_cases hu : d.uses r
        · simp [AbsState.set, AFl.touch, hcmpOld, hu] at hc
        · simpa [AbsState.set, AFl.touch, hcmpOld, hu] using hc
    have hu : c.uses r = false := by
      cases ht : c.uses r with
      | false => rfl
      | true => simp [AbsState.set, AFl.touch, hold, ht] at hc
    have hcc := hidx.1 c hold
    have ho := hcmp c hold
    exact ⟨(cmpSem_setReg hr16 v₁ hcc hu).mpr ho.1,
      (cmpSem_setReg hr16 v₂ hcc hu).mpr ho.2⟩
  · exact hstk
  · intro f hf
    have hh : f ∈ st.rel ∧ f.1 ≠ r ∧ f.2.1 ≠ r := by
      simpa [AbsState.set] using hf
    have hfo := hrel f hh.1
    have hfi := hidx.2.1 f hh.1
    exact ⟨(factSem_setReg hr16 v₁ hfi hh.2.1 hh.2.2).mpr hfo.1,
      (factSem_setReg hr16 v₂ hfi hh.2.1 hh.2.2).mpr hfo.2⟩
  · intro l hl
    have hh : l ∈ st.lnk ∧ l.i ≠ r ∧ l.j ≠ r := by
      simpa [AbsState.set] using hl
    have hlo := hlnk l hh.1
    have hli := hidx.2.2 l hh.1
    exact ⟨(lnkSem_setReg hr16 v₁ hli hh.2.1 hh.2.2).mpr hlo.1,
      (lnkSem_setReg hr16 v₂ hli hh.2.1 hh.2.2).mpr hlo.2⟩
  · exact hcode₁
  · exact hcode₂

end M0Crypto.Release.ConstantTime
