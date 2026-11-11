import M0Crypto.Release.ConstantTime.ImmediateSound

/-! Soundness of ordering facts inferred from an increment. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb

/-- If an unsigned word is strictly below another, incrementing it cannot wrap
and yields a value below or equal to the other word. -/
theorem increment_le_of_lt (x y : Word) (h : x.toNat + 1 ≤ y.toNat) :
    (x + 1#32).toNat ≤ y.toNat := by
  have hsum : x.toNat + (1#32 : Word).toNat < 2 ^ 32 := by have := y.isLt; simp at *; omega
  rw [BitVec.toNat_add_of_lt hsum]
  simp
  omega

/-- Newly inferred facts use the destination and an already well-formed source
fact's second register. -/
theorem incFacts_indicesOk {pre post : AbsState} {d n k : Nat}
    (hd : regIndexOk d) (hpre : pre.indicesOk) (hpost : post.indicesOk) :
    (incFacts pre d n k post).indicesOk := by
  unfold incFacts
  split
  · refine ⟨hpost.1, ?_, hpost.2.2⟩
    intro f hf
    simp only [List.mem_eraseDups, List.mem_append, List.mem_filterMap] at hf
    rcases hf with hf | ⟨old, hold, hmap⟩
    · exact hpost.2.1 f hf
    · rcases old with ⟨i, j, strict⟩
      split at hmap
      · simp only [Option.some.injEq] at hmap
        subst f
        exact ⟨hd, (hpre.2.1 (i, j, strict) hold).2⟩
      · simp at hmap
  · exact hpost

/-- The analyzer's increment-derived facts hold when the destination contains
the incremented source and other named registers are unchanged. -/
theorem incFacts_new_sem {pre post : AbsState} {d n k : Nat} {s₁ s₂ u₁ u₂ : State}
    (hpre : ∀ f ∈ pre.rel, FactSem f s₁ ∧ FactSem f s₂)
    (hpost : ∀ f ∈ post.rel, FactSem f u₁ ∧ FactSem f u₂)
    (hindices : ∀ f ∈ pre.rel, factIndexOk f)
    (hvalue₁ : regAt u₁ d = regAt s₁ n + 1#32)
    (hvalue₂ : regAt u₂ d = regAt s₂ n + 1#32)
    (hother₁ : ∀ j, regIndexOk j → j ≠ d → regAt u₁ j = regAt s₁ j)
    (hother₂ : ∀ j, regIndexOk j → j ≠ d → regAt u₂ j = regAt s₂ j) :
    ∀ f ∈ (incFacts pre d n k post).rel, FactSem f u₁ ∧ FactSem f u₂ := by
  intro f hf
  unfold incFacts at hf
  split at hf
  · simp only [List.mem_eraseDups, List.mem_append, List.mem_filterMap] at hf
    rcases hf with hold | ⟨old, hold, hmap⟩
    · exact hpost f hold
    · rcases old with ⟨i, j, strict⟩
      simp only at hmap
      split at hmap
      · rename_i hcond
        simp only [Option.some.injEq] at hmap
        subst f
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcond
        obtain ⟨⟨⟨hin, hstrict⟩, hjd⟩, _⟩ := hcond
        subst i
        subst strict
        have h := hpre (n, j, true) hold
        have hj : regIndexOk j := (hindices (n, j, true) hold).2
        simp only [FactSem, ↓reduceIte] at h ⊢
        rw [hvalue₁, hvalue₂, hother₁ j hj hjd, hother₂ j hj hjd]
        exact ⟨increment_le_of_lt _ _ h.1, increment_le_of_lt _ _ h.2⟩
      · simp at hmap
  · exact hpost f hf

/-- Adding the increment-derived facts preserves the entire paired relation. -/
theorem LowEq.withIncFacts {p : Params} {bytes : List (BitVec 8)} {off off' : Nat}
    {pre post : AbsState} {d n k : Nat} {s₁ s₂ u₁ u₂ : State}
    (hpre : LowEq p bytes off pre s₁ s₂) (hidx : pre.indicesOk)
    (hpost : LowEq p bytes off' post u₁ u₂)
    (hvalue₁ : regAt u₁ d = regAt s₁ n + 1#32)
    (hvalue₂ : regAt u₂ d = regAt s₂ n + 1#32)
    (hother₁ : ∀ j, regIndexOk j → j ≠ d → regAt u₁ j = regAt s₁ j)
    (hother₂ : ∀ j, regIndexOk j → j ≠ d → regAt u₂ j = regAt s₂ j) :
    LowEq p bytes off' (incFacts pre d n k post) u₁ u₂ := by
  have hrel := incFacts_new_sem (k := k) hpre.facts hpost.facts
    hidx.2.1 hvalue₁ hvalue₂ hother₁ hother₂
  rcases hpost with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstk, _,
    hlnk, hsize, hcode₁, hcode₂⟩
  unfold incFacts at hrel ⊢
  split <;> rename_i hk <;> simp only [hk, ↓reduceIte] at hrel <;>
    exact ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩

end M0Crypto.Release.ConstantTime
