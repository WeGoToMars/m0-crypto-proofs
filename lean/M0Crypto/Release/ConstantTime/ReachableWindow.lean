import M0Crypto.Release.ConstantTime.StepBounds
import M0Crypto.Release.ConstantTime.InstructionCases

/-!
# Stack window of every state of a certified run

The certificate relates a run to itself (take both initial states equal). Every state of the run
before the stop address then sits at a certificate position whose abstract transfer succeeded,
and a successful transfer checks the stack offset against the entry window.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-- Along the paired run every state before the stop address has a related partner. -/
theorem certificate_reachable_partner {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s₂ u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s₁ s₂) :
    ∀ u, BeforeStop (p.lr0 &&& ~~~1#32) s₁ u →
      ∃ u₂, RunRel env cert p bytes (p.lr0 &&& ~~~1#32) u u₂ ∧
        BeforeStop (p.lr0 &&& ~~~1#32) s₂ u₂ := by
  intro u hu
  induction hu with
  | initial => exact ⟨s₂, Or.inl h, BeforeStop.initial⟩
  | @next s t event hreach hstop hstep ih =>
    obtain ⟨u₂, hrel, hr₂⟩ := ih
    have hcert : CertAt env cert p bytes s u₂ := by
      rcases hrel with hcert | ⟨hpc, _⟩
      · exact hcert
      · exact absurd hpc hstop
    have hs := certAt_run_paired hc hi ha hslots hwidth hdisj hsize hbase hnowrap hlr hcert
      (hlocal s u₂ hreach hr₂ hcert)
    have hstop₂ : u₂.pc ≠ p.lr0 &&& ~~~1#32 := by rw [← hcert.pc_eq]; exact hstop
    unfold PairedStep at hs
    rw [hstep] at hs
    cases h₂ : step u₂ with
    | error e => simp [h₂] at hs
    | ok b =>
      rcases b with ⟨t₂, e₂⟩
      simp only [h₂] at hs
      exact ⟨t₂, hs.2, BeforeStop.next hr₂ hstop₂ h₂⟩

/-- Every state before the stop address lies in the entry stack window. -/
theorem certificate_reachable_window {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s₂ u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s₁ s₂) {u : State}
    (hu : BeforeStop (p.lr0 &&& ~~~1#32) s₁ u) (hne : u.pc ≠ p.lr0 &&& ~~~1#32) :
    M0Crypto.Release.TraceSpec.InStackWindow p.sp0 env.win.below (u.regs 13) := by
  obtain ⟨u₂, hrel, -⟩ := certificate_reachable_partner hc hi ha hslots hwidth hdisj hsize hbase
    hnowrap hlr hlocal h u hu
  rcases hrel with ⟨b, off, st, code, hm, hp, hnil, hlow⟩ | ⟨hpc, _⟩
  · cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
      exact (xfer_stack_window hlow hx).1
  · exact absurd hpc hne

end M0Crypto.Release.ConstantTime
