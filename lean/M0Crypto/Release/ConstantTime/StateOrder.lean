import M0Crypto.Release.ConstantTime.StateSem

namespace M0Crypto.Release.ConstantTime

/-- The flag labels are monotone under the abstract flag ordering. -/
theorem flagSem_le {a b : AFl} {s₁ s₂ : M0Crypto.Armv6M.State}
    (hle : a.le b = true) (h : FlagSem a s₁ s₂) : FlagSem b s₁ s₂ := by
  simp only [AFl.le, Bool.and_eq_true] at hle
  rcases hle with ⟨⟨⟨⟨hn, hz⟩, hc⟩, hv⟩, _⟩
  exact ⟨AbsFlags.le_sem h.1 hn, AbsFlags.le_sem h.2.1 hz,
    AbsFlags.le_sem h.2.2.1 hc, AbsFlags.le_sem h.2.2.2 hv⟩

/-- Ordering may discard a comparison, but cannot invent one. -/
theorem cmpSem_le {a b : AFl} {s₁ s₂ : M0Crypto.Armv6M.State}
    (hle : a.le b = true)
    (h : ∀ c, a.cmp = some c → CmpSem c s₁ ∧ CmpSem c s₂) :
    ∀ c, b.cmp = some c → CmpSem c s₁ ∧ CmpSem c s₂ := by
  intro c hc
  have hcmp : (match b.cmp with
      | none => true
      | some c => a.cmp == some c) = true := by
    simp only [AFl.le, Bool.and_eq_true] at hle
    exact hle.2
  rw [hc] at hcmp
  exact h c (by simpa using hcmp)

/-- Register labels are monotone at every represented register. -/
theorem regsLe_sem {p : Params} {a b : List AbsVal} {s₁ s₂ : M0Crypto.Armv6M.State}
    (hle : regsLe a b = true)
    (h : ∀ i, i < numRegs → i ≠ 13 →
      AbsVal.Sem p (regGet a i) (regAt s₁ i) (regAt s₂ i)) :
    ∀ i, i < numRegs → i ≠ 13 →
      AbsVal.Sem p (regGet b i) (regAt s₁ i) (regAt s₂ i) := by
  intro i hi hn
  have hx : (regGet a i).le (regGet b i) = true := by
    unfold regsLe at hle
    exact (List.all_eq_true.mp hle) i (List.mem_range.mpr hi)
  exact AbsVal.le_sem hx (h i hi hn)

end M0Crypto.Release.ConstantTime
