import M0Crypto.Release.X25519StackEffect
import M0Crypto.Release.ConstantTime.HolesRun
import M0Crypto.Release.ConstantTime.X25519Holes

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.X25519Prologue (InpR)

/-- Every run of a valid call keeps the stack discipline, and each of its states before the
return is at an instruction of the artifact. -/
theorem x25519_run_discipline {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 X25519.stackBytes states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ c.ret →
        Interrupt.CodePos c.base Artifacts.Release.bytes u := by
  have hv := hp.valid
  obtain ⟨n, hn⟩ := X25519.x25519_correct c s hp
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, ?_⟩
  have hsp : s.regs 13 = (x25519Params c).sp0 := by
    rw [hp.entry.regs]; exact hp.entry.sp
  refine certificate_run_discipline_with_fragments x25519_certOk x25519_indicesFailure_eq_none
    x25519_certAligned x25519_win_width (x25519_code_stack_disjoint hv) x25519_env_size
    (x25519_base4 hv) (x25519_code_no_wrap hv) hsp x25519_loadFailure (InpR c)
    (ls := fun _ => none)
    (fun u t ev h1 h2 h3 off h4 h5 i h6 h7 y h8 =>
      Or.inl (x25519_load_site hp hrun u t ev h1 h2 h3 off h4 h5 i h6 h7 y h8))
    (fun y hy => by
      rcases hy with hy | hy
      · exact not_region_of_disj hv.scalarS hy
      · exact not_region_of_disj hv.pointS hy)
    x25519_holes hrun ?_ ?_
  · intro k u hu hn
    have ordinary : X25519CertPoint c u →
        ∃ b off st i is, b ∈ x25519Cert ∧ BlockPoint x25519Env b off st (i :: is) ∧
          LowEq (x25519Params c) Artifacts.Release.bytes off st u u ∧
          BufferStoreOk x25519Env (x25519Params c) Artifacts.Release.bytes st u i := by
      rintro ⟨b,off,st,code,hm,hpt,hne,hrel⟩
      cases code with
      | nil => exact absurd rfl hne
      | cons i is =>
        exact ⟨b,off,st,i,is,hm,hpt,hrel,
          x25519_store_site hp hrun u (List.mem_of_getElem? hu) u b off st i is hm hpt hrel⟩
    rcases x25519_recorded_position hp hrun k u hu hn with h | ⟨j,a,b,hj,hk,r⟩
    · exact .inl (ordinary h)
    · by_cases hEnd : k = j+(x25519_trace c).length
      · have hEndAt : states[k]? = some b := by rw [hEnd]; exact r.finish
        have hEq := Option.some.inj (hu.symm.trans hEndAt)
        subst u
        exact .inl (ordinary r.post)
      · exact .inr (x25519_fragment_discipline hp r hj (by omega) hu)
  · intro k u t ev hu ht he hn hs htne
    have ordinary : X25519CertPoint c u →
        (∃ b off st i is, b ∈ x25519Cert ∧ BlockPoint x25519Env b off st (i :: is) ∧
          LowEq (x25519Params c) Artifacts.Release.bytes off st u u ∧ x25519Env.frameCallAt off = none) ∨
        (EarlierHoles (env := x25519Env) (cert := x25519Cert) (p := x25519Params c)
          (bytes := Artifacts.Release.bytes) x25519Holes states tr (k+1) →
          HoleInv x25519Env x25519Cert (x25519Params c) Artifacts.Release.bytes x25519Holes states tr (k+1) t) := by
      intro h
      by_cases hpc : u.pc = c.base+BitVec.ofNat 32 x25519CallSite
      · obtain ⟨b,r⟩ := record_call hp hrun hu h hpc
        have hLen : 0 < (x25519_trace c).length := Nat.zero_lt_succ _
        exact .inr (x25519_fragment_advance hp hrun r (by omega) (by omega) ht)
      · obtain ⟨b,off,st,code,hm,hpt,hne,hrel⟩ := h
        cases code with
        | nil => exact absurd rfl hne
        | cons i is =>
          exact .inl ⟨b,off,st,i,is,hm,hpt,hrel,x25519_plain_position hpc hrel.pc⟩
    rcases x25519_recorded_position hp hrun k u hu hn with h | ⟨j,a,b,hj,hk,r⟩
    · exact ordinary h
    · by_cases hEnd : k = j+(x25519_trace c).length
      · have hEndAt : states[k]? = some b := by rw [hEnd]; exact r.finish
        have hEq := Option.some.inj (hu.symm.trans hEndAt)
        subst u
        exact ordinary r.post
      · exact .inr (x25519_fragment_advance hp hrun r (by omega) (by omega) ht)

/-- **`m0c_x25519` keeps the stack discipline below its entry SP.** -/
theorem _root_.M0Crypto.Release.X25519.x25519_stack_discipline :
    TraceSpec.X25519StackDiscipline := by
  intro c s hp
  obtain ⟨n, hn⟩ := x25519_run_discipline hp
  exact ⟨n, fun fuel hf => by
    obtain ⟨states, tr, hr, hd, -⟩ := hn fuel hf
    exact ⟨states, tr, hr, hd⟩⟩

/-- **`m0c_x25519` with interrupts.** -/
theorem _root_.M0Crypto.Release.X25519.x25519_interrupted : TraceSpec.X25519Interrupted := by
  intro K c s hp
  have hv := hp.valid
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (X25519.x25519_reads c s hp)
    (X25519.x25519_stack c s hp) (x25519_run_discipline hp)
  · rw [Artifacts.Release.bytes_length] at hy
    exact ⟨Or.inr (Or.inr (Or.inl hy)), not_region_of_disj hv.codeS hy⟩
  · obtain ⟨n, hn⟩ := X25519.x25519_correct c s hp
    exact ⟨n, fun fuel hf => by
      obtain ⟨t, tr, ht, hr, -⟩ := hn fuel hf
      exact ⟨t, tr, ht, hr⟩⟩

end M0Crypto.Release.ConstantTime
