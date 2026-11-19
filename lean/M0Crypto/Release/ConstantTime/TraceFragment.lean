import M0Crypto.Release.ConstantTime.InstructionCases
import M0Crypto.Release.ReachInv

/-! A paired certificate can cross a separately checked trace before resuming
its ordinary step relation. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Release
open M0Crypto.Thumb

/-- The event of a step is at the PC of its pre-state. -/
theorem step_ev_pc {s t : State} {e : Event} (h : step s = .ok (t, e)) : e.pc = s.pc := by
  unfold step at h; simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]
    · cases h
  · cases h

/-- A machine trace whose steps have a common local guarantee, with no stop
address encountered before the final state. -/
inductive TraceFragment (stop : Word) (P : State → Event → Prop) :
    State → List Event → State → Prop where
  | nil (s) : TraceFragment stop P s [] s
  | cons {s u t : State} {e : Event} {es : List Event} :
      s.pc ≠ stop → step s = .ok (u,e) → P s e → TraceFragment stop P u es t →
        TraceFragment stop P s (e :: es) t

namespace TraceFragment

theorem of_runH {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base stop : Word}
    {P Q : State → Event → Prop} {n : Nat} {s t : State} {tr : List Event}
    (run : runH B base n s = .ok (t,tr)) (code : CodeAt s.mem base B)
    (checks : StepsOk base (fun u e => e.pc ≠ stop ∧ P u e ∧ MissesCode B base e.accesses) n s)
    (refineStep : ∀ u v ev, CodeAt u.mem base B → stepH B base u = .ok (v,ev) → P u ev → Q u ev) :
    TraceFragment stop Q s tr t := by
  induction n generalizing s tr with
  | zero =>
    cases run
    exact .nil _
  | succ n ih =>
    obtain ⟨u,e,es,hStep,hMore,rfl⟩ := runH_succ_ok run
    obtain ⟨⟨hStop,hP,hWrites⟩,hChecks⟩ := checks.uncons hStep
    have hs := step_of_stepH code hStep
    exact .cons (stepH_pc hStep ▸ hStop) hs (refineStep _ _ _ code hStep hP) (ih hMore (codeAt_step code hs hWrites) hChecks)

theorem pc_eq {stop : Word} {P : State → Event → Prop} {a b u v : State} {tr : List Event}
    (hA : TraceFragment stop P a tr u) (hB : TraceFragment stop P b tr v) (h : u.pc = v.pc) :
    a.pc = b.pc := by
  cases hA with
  | nil => cases hB; exact h
  | cons _ ha _ _ =>
    cases hB with
    | cons _ hb _ _ => exact (step_ev_pc ha).symm.trans (step_ev_pc hb)

end TraceFragment

/-- A pair is at an ordinary certificate point or has an equal trace remaining
before reaching related certificate points. -/
def FragmentRel (stop : Word) (P : State → Event → Prop) (R : State → State → Prop)
    (s₁ s₂ : State) : Prop :=
  R s₁ s₂ ∨ ∃ tr t₁ t₂, tr ≠ [] ∧
    TraceFragment stop P s₁ tr t₁ ∧ TraceFragment stop P s₂ tr t₂ ∧ R t₁ t₂

theorem FragmentRel.pc_eq {stop : Word} {P : State → Event → Prop} {R : State → State → Prop}
    {s₁ s₂ : State} (hpc : ∀ s t, R s t → s.pc = t.pc)
    (h : FragmentRel stop P R s₁ s₂) : s₁.pc = s₂.pc := by
  rcases h with h | ⟨_,u,v,_,hu,hv,h⟩
  · exact hpc _ _ h
  · exact hu.pc_eq hv (hpc u v h)

theorem FragmentRel.step {stop : Word} {P : State → Event → Prop} {R : State → State → Prop}
    {s₁ s₂ : State} {tr : List Event} {t₁ t₂ : State}
    (hne : tr ≠ []) (hA : TraceFragment stop P s₁ tr t₁) (hB : TraceFragment stop P s₂ tr t₂)
    (h : R t₁ t₂) : PairedStep (FragmentRel stop P R) s₁ s₂ := by
  cases hA with
  | nil => exact (hne rfl).elim
  | @cons a a' u e es _ ha _ hA =>
    cases hB with
    | @cons b b' v _ _ _ hb _ hB =>
      simp only [PairedStep,ha,hb,true_and]
      cases es with
      | nil => cases hA; cases hB; exact Or.inl h
      | cons e es => exact Or.inr ⟨_,_,_,List.cons_ne_nil _ _,hA,hB,h⟩

theorem PairedStep.mono {R S : State → State → Prop} {s t : State}
    (h : PairedStep R s t) (hs : ∀ a b, R a b → S a b) : PairedStep S s t := by
  unfold PairedStep at h ⊢
  cases hs₁ : step s <;> cases hs₂ : step t
  all_goals
    simp only [hs₁, hs₂] at h ⊢ <;> first | exact h | exact ⟨h.1,hs _ _ h.2⟩

theorem PairedStep.with_reach {stop : Word} {R : State → State → Prop} {u v s t : State}
    (h : PairedStep R s t) (hpc : s.pc = t.pc) (hne : s.pc ≠ stop)
    (hS : BeforeStop stop u s) (hT : BeforeStop stop v t) :
    PairedStep (fun a b => R a b ∧ BeforeStop stop u a ∧ BeforeStop stop v b) s t := by
  unfold PairedStep at h ⊢
  cases hs : step s with
  | error e => cases ht : step t <;> simp only [hs,ht] at h ⊢ <;> exact h
  | ok a =>
    cases ht : step t with
    | error e => simp only [hs,ht] at h ⊢
    | ok b =>
      obtain ⟨s',e⟩ := a
      obtain ⟨t',f⟩ := b
      simp only [hs,ht] at h ⊢
      exact ⟨h.1,h.2,.next hS hne hs,.next hT (hpc ▸ hne) ht⟩

end M0Crypto.Release.ConstantTime
