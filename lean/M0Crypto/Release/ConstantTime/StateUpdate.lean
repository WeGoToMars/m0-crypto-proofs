import M0Crypto.Release.ConstantTime.SemEntails

/-! Helpers for preserving the concrete state relation when labels are refined. -/
namespace M0Crypto.Release.ConstantTime

/-- Replacing only register labels preserves the relation if the replacement labels
still describe the same pair of concrete register values. -/
theorem LowEq.withRegs {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (regs : List AbsVal)
    (h : LowEq p bytes off st s₁ s₂)
    (hr : ∀ i, i < numRegs → i ≠ 13 →
      AbsVal.Sem p (regGet regs i) (regAt s₁ i) (regAt s₂ i)) :
    LowEq p bytes off { st with regs := regs } s₁ s₂ := by
  rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, _, hflags, hcmp,
    hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  exact ⟨hpc₁, hpc₂, hsp₁, hsp₂, hr, hflags, hcmp, hstk, hrel, hlnk,
    hsize, hcode₁, hcode₂⟩

/-- A single refined label may replace an old label when it describes the same
concrete register pair. An out-of-range list update leaves the label secret. -/
theorem LowEq.withRegSet {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (r : Nat) (v : AbsVal)
    (h : LowEq p bytes off st s₁ s₂)
    (hv : AbsVal.Sem p v (regAt s₁ r) (regAt s₂ r)) :
    LowEq p bytes off { st with regs := regSet st.regs r v } s₁ s₂ := by
  apply h.withRegs
  intro i hi hne13
  by_cases hir : i = r
  · subst i
    by_cases hlen : r < st.regs.length
    · simpa [regGet, regSet, hne13, List.getD_eq_getElem?_getD, hlen] using hv
    · simp [regGet, regSet, hne13, List.getD_eq_getElem?_getD, hlen, AbsVal.Sem]
  · have horig := h.regs i hi hne13
    by_cases hr13 : r = 13 <;>
      simpa [AbsState.get, regGet, regSet, hne13, hir, Ne.symm hir, hr13,
        List.getD_eq_getElem?_getD] using horig

/-- A public interval can be narrowed when the first run's concrete value lies
within the narrower interval; publicness transfers the bound to the second run. -/
theorem narrow_interval {p : Params} {v : AbsVal} {x y : M0Crypto.Armv6M.Word}
    {lo hi newHi : Nat} (hs : AbsVal.Sem p v x y) (hiVal : ival v = some (lo, hi))
    (hbound : x.toNat ≤ newHi) : AbsVal.Sem p (.num lo newHi) x y := by
  have hb := interval_bounds hs hiVal
  have heq : x = y := by
    apply AbsVal.sem_public hs
    cases v <;> simp_all [ival, AbsVal.pub]
  exact ⟨heq, hb.1, hbound⟩

/-- A recorded unsigned comparison permits narrowing the upper bound of its left
operand using the right operand's upper bound. -/
theorem fact_narrow {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : M0Crypto.Armv6M.Word}
    {il ih jl jh : Nat} (strict : Bool)
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂)
    (hia : ival a = some (il, ih)) (hib : ival b = some (jl, jh))
    (hrel : x₁.toNat + (if strict then 1 else 0) ≤ y₁.toNat)
    (hnonneg : (if strict then 1 else 0) ≤ jh) :
    AbsVal.Sem p (.num il (jh - (if strict then 1 else 0))) x₁ x₂ := by
  apply narrow_interval ha hia
  have hbnd := interval_bounds hb hib
  omega

end M0Crypto.Release.ConstantTime
