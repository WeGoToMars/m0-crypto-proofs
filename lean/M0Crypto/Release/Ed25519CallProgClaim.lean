import M0Crypto.Release.Routine
import M0Crypto.Release.RunStates
import M0Crypto.Release.Interrupt

set_option linter.unusedSimpArgs false

/-!
# Call programs: from a run to the released claim forms

A `ReachFT` run of an entry from its entry state, whose pcs avoid the return address and whose
writes miss the code, determines `runUntil` at every fuel: below the run's length it stops with
`.error .fuel`, from it on it returns the run's final state and trace (`run_facts`). The run's
states and events carry the footprints of `Step`. So one run gives the correctness, read, stack
and every-fuel trace forms; two runs with one trace condition that admits one trace give equal
traces at every fuel (`traceEq_of`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}
variable {Pc Rd Wr Sp : Word → Prop} {stop : Word}

theorem stepH_pc {s s1 : State} {e : Event} (h : stepH B base s = .ok (s1, e)) : e.pc = s.pc := by
  unfold stepH at h; simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]
      · cases h
    · cases h
  · cases h

/-- A successful Harvard step is at an instruction of the artifact. -/
theorem stepH_codePos {s s1 : State} {e : Event} (hc : CodeAt s.mem base B) (h : stepH B base s = .ok (s1, e)) :
    Interrupt.CodePos base B s := by
  unfold stepH at h; simp only at h
  split at h; · cases h
  split at h; · cases h
  rename_i i hi
  split at h
  · exact ⟨_, i, (base_add_sub s.pc).symm, hi, by assumption, hc⟩
  · cases h

/-- **The facts of a run** that ends at `stop` with every step in the footprints. -/
theorem run_facts (hpc : ∀ y, Pc y → y ≠ stop)
    (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i) :
    ∀ n s t tr, runH B base n s = .ok (t, tr) → StepsOk base (Step Pc Rd Wr Sp) n s →
      CodeAt s.mem base B → t.pc = stop →
      (∀ fuel, Thumb.runUntil stop fuel s = if n ≤ fuel then .ok (t, tr) else .error .fuel) ∧
      (∀ fuel, n ≤ fuel → ∃ states, runStates stop fuel s = .ok (states, tr) ∧
        ∀ u ∈ states, (Sp (u.regs 13) ∧ Interrupt.CodePos base B u) ∨ u = t) ∧
      (∀ e ∈ tr, (∀ y, Reads e.accesses y → Rd y) ∧ (∀ y, Writes e.accesses y → Wr y)) ∧
      tr.length = n
  | 0, s, t, tr, hr, _, _, hst => by
    simp only [runH, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨fun fuel => ?_, fun fuel _ => ⟨[s], ?_, fun u hu => Or.inr (by simpa using hu)⟩,
      fun e he => absurd he List.not_mem_nil, rfl⟩
    · cases fuel <;> simp [Thumb.runUntil, hst]
    · cases fuel <;> simp [runStates, hst]
  | n + 1, s, t, tr, hr, hok, hc, hst => by
    simp only [runH] at hr
    split at hr
    · cases hr
    rename_i s1 e h1
    split at hr
    · cases hr
    rename_i s2 es h2
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨⟨hP, hW, hR, hS⟩, hok1⟩ := hok s1 e h1
    have hs := step_of_stepH hc h1
    have hne : s.pc ≠ stop := by rw [← stepH_pc h1]; exact hpc _ hP
    have hc1 := codeAt_step hc hs fun i hi hw => hwc _ (hW _ hw) i hi rfl
    obtain ⟨i1, i2, i3, i4⟩ := run_facts hpc hwc n s1 s2 es h2 hok1 hc1 hst
    refine ⟨fun fuel => ?_, fun fuel hf => ?_, fun e' he' => ?_, by simp [i4]⟩
    · cases fuel with
      | zero => simp [Thumb.runUntil, hne]
      | succ f =>
        simp only [Thumb.runUntil, hne, ↓reduceIte, hs, i1 f]
        by_cases hn : n ≤ f
        · simp [hn]
        · simp [hn, show ¬ n + 1 ≤ f + 1 by omega]
    · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨states, hst1, hall⟩ := i2 f (by omega)
      refine ⟨s :: states, by simp [runStates, hne, hs, hst1], fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl ⟨hS, stepH_codePos hc h1⟩
      · exact hall u hu
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨hR, hW⟩
      · exact i3 e' he'

/-- **The claim forms of a run**: from a `ReachFT` run that ends at `stop`, the result, the
footprints of the trace and of the states, and the trace condition, at every fuel. -/
theorem claims_of {s : State} {Q : State → Prop} {Φ : TrP}
    (hpc : ∀ y, Pc y → y ≠ stop) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hc : CodeAt s.mem base B) (hq : ∀ t, Q t → t.pc = stop) (h : ReachFT base Pc Rd Wr Sp s Q Φ) :
    ∃ n t tr, Q t ∧ Φ tr ∧ tr.length = n ∧
      (∀ fuel, Thumb.runUntil stop fuel s = if n ≤ fuel then .ok (t, tr) else .error .fuel) ∧
      (∀ fuel, n ≤ fuel → ∃ states, runStates stop fuel s = .ok (states, tr) ∧
        ∀ u ∈ states, (Sp (u.regs 13) ∧ Interrupt.CodePos base B u) ∨ u = t) ∧
      (∀ e ∈ tr, (∀ y, Reads e.accesses y → Rd y) ∧ (∀ y, Writes e.accesses y → Wr y)) := by
  obtain ⟨n, t, tr, hr, hok, hQ, hΦ⟩ := h
  obtain ⟨f1, f2, f3, f4⟩ := run_facts hpc hwc n s t tr hr hok hc (hq t hQ)
  exact ⟨n, t, tr, hQ, hΦ, f4, f1, f2, f3⟩

/-- `Returns`-shaped result: from some fuel on, the run returns with `Q` and writes in `Wr`. -/
theorem returns_of {s : State} {Q : State → Prop} {Φ : TrP}
    (hpc : ∀ y, Pc y → y ≠ stop) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hc : CodeAt s.mem base B) (hq : ∀ t, Q t → t.pc = stop) (h : ReachFT base Pc Rd Wr Sp s Q Φ) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil stop fuel s = .ok (t, tr) ∧ Q t ∧
      (∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y) ∧ WritesTo Wr tr := by
  obtain ⟨n, t, tr, hQ, -, -, h1, -, h3⟩ := claims_of hpc hwc hc hq h
  exact ⟨n, fun fuel hf => ⟨t, tr, by rw [h1]; simp [hf], hQ, fun e he => (h3 e he).1,
    fun e he => (h3 e he).2⟩⟩

/-- Stack form: from some fuel on, every state of the run has `sp` in `Sp`. -/
theorem states_of {s : State} {Q : State → Prop} {Φ : TrP}
    (hpc : ∀ y, Pc y → y ≠ stop) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hc : CodeAt s.mem base B) (hq : ∀ t, Q t → t.pc = stop ∧ Sp (t.regs 13))
    (h : ReachFT base Pc Rd Wr Sp s Q Φ) :
    ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr, runStates stop fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, Sp (u.regs 13) := by
  obtain ⟨n, t, tr, hQ, -, -, -, h2, -⟩ := claims_of hpc hwc hc (fun t ht => (hq t ht).1) h
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, hs, hall⟩ := h2 fuel hf
  refine ⟨states, tr, hs, fun u hu => ?_⟩
  rcases hall u hu with h | rfl
  · exact h.1
  · exact (hq u hQ).2

/-- **Equal traces at every fuel**: two runs whose trace conditions are one condition that admits
one trace. -/
theorem traceEq_of {s₁ s₂ : State} {Q₁ Q₂ : State → Prop} {Φ : TrP} (hu : Tr.Uniq Φ)
    (hpc : ∀ y, Pc y → y ≠ stop) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    {Pc' Rd' Wr' Sp' : Word → Prop} (hpc' : ∀ y, Pc' y → y ≠ stop)
    (hwc' : ∀ y, Wr' y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hc₁ : CodeAt s₁.mem base B) (hc₂ : CodeAt s₂.mem base B)
    (hq₁ : ∀ t, Q₁ t → t.pc = stop) (hq₂ : ∀ t, Q₂ t → t.pc = stop)
    (h₁ : ReachFT base Pc Rd Wr Sp s₁ Q₁ Φ) (h₂ : ReachFT base Pc' Rd' Wr' Sp' s₂ Q₂ Φ) :
    ∀ fuel, (Thumb.runUntil stop fuel s₁).map Prod.snd = (Thumb.runUntil stop fuel s₂).map Prod.snd := by
  obtain ⟨n₁, t₁, tr₁, -, hΦ₁, hl₁, hr₁, -, -⟩ := claims_of hpc hwc hc₁ hq₁ h₁
  obtain ⟨n₂, t₂, tr₂, -, hΦ₂, hl₂, hr₂, -, -⟩ := claims_of hpc' hwc' hc₂ hq₂ h₂
  have he : tr₁ = tr₂ := hu _ _ hΦ₁ hΦ₂
  subst he
  have hn : n₁ = n₂ := by omega
  subst hn
  intro fuel
  rw [hr₁, hr₂]
  split <;> rfl

end M0Crypto.Release.Ed25519CallProg
