import M0Crypto.Release.X25519TraceSteps
import M0Crypto.Release.ConstantTime.HolesRun
import M0Crypto.Release.ConstantTime.TraceSlice

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.X25519Layout (E)
open M0Crypto.Release.X25519SafegcdFrame (workSp)

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

abbrev x25519_trace (c : X25519.Ctx) := x25519CallTrace c.base (E c)

abbrev X25519CertPoint (c : X25519.Ctx) (u : State) :=
  CertAt x25519Env x25519Cert (x25519Params c) B u u

/-- The recorded trace between a checked invocation and its resume point. -/
structure X25519CallRecord (c : X25519.Ctx) (states : List State) (tr : List Event)
    (j : Nat) (a b : State) : Prop where
  start : states[j]? = some a
  finish : states[j+(x25519_trace c).length]? = some b
  invoc : a.pc = c.base + BitVec.ofNat 32 x25519CallSite
  pre : X25519CertPoint c a
  post : X25519CertPoint c b
  resume : b.pc = c.base + BitVec.ofNat 32 x25519CallRet
  sp : b.sp = workSp (E c)
  at_step : ∀ (i : Nat) ev, (x25519_trace c)[i]? = some ev →
    tr[j+i]? = some ev ∧ ∃ u, states[j+i]? = some u ∧ X25519SummaryStep c u ev
  core : ∀ ev ∈ (x25519_trace c).tail, X25519Ev.InvPc c.base ev.pc

theorem record_call {c : X25519.Ctx} {s a : State} (hp : X25519.Pre c s)
    {fuel j : Nat} {states : List State} {tr : List Event}
    (hr : runStates c.ret fuel s = .ok (states,tr)) (ha : states[j]? = some a)
    (hCert : X25519CertPoint c a) (hpc : a.pc = c.base+BitVec.ofNat 32 x25519CallSite) :
    ∃ b, X25519CallRecord c states tr j a b := by
  obtain ⟨b,d,hB,hD,hAfter,hSp,hResume,hRegion⟩ := x25519_enter_summary hp hCert hpc
  obtain ⟨hFin,hSteps⟩ := hB.recorded_slice hr ha
  have hFin' := (hD.recorded_slice hr ha).1
  have he := Option.some.inj (hFin.symm.trans hFin')
  subst d
  exact ⟨b,ha,hFin,hpc,hCert,hAfter,hResume,hSp,hSteps,hRegion⟩

/-- An interior point carries the index of its invocation, including at the
resume point so the byte effect can use initialization at entry. -/
def X25519RecordedPos (c : X25519.Ctx) (states : List State) (tr : List Event)
    (k : Nat) (u : State) : Prop :=
  X25519CertPoint c u ∨
    ∃ j a b, j < k ∧ k ≤ j+(x25519_trace c).length ∧ X25519CallRecord c states tr j a b

theorem x25519_recorded_position {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s)
    {fuel : Nat} {states : List State} {tr : List Event}
    (hr : runStates c.ret fuel s = .ok (states,tr)) :
    ∀ k u, states[k]? = some u → u.pc ≠ c.ret → X25519RecordedPos c states tr k u := by
  have ⟨h0,_,hBack⟩ := runStates_get hr
  have hLen : 0 < (x25519_trace c).length := Nat.zero_lt_succ _
  have next {k : Nat} {a b : State} {ev : Event} (ha : states[k]? = some a)
      (hCert : X25519CertPoint c a) (hStop : a.pc ≠ c.ret) (hb : b.pc ≠ c.ret)
      (hs : step a = .ok (b,ev)) : X25519RecordedPos c states tr (k+1) b := by
    by_cases hpc : a.pc = c.base+BitVec.ofNat 32 x25519CallSite
    · obtain ⟨d,hd⟩ := record_call hp hr ha hCert hpc
      exact .inr ⟨k,a,d,by omega,by omega,hd⟩
    · have hReach := runStates_beforeStop hr a (List.mem_of_getElem? ha)
      have h := x25519_plain_step hp hr hReach hReach hCert hpc
      simp only [PairedStep,hs] at h
      rcases h.2 with h | ⟨he,_⟩
      · exact .inl h
      · exact absurd he hb
  intro k
  induction k with
  | zero =>
    intro u hu _
    have he := Option.some.inj (h0.symm.trans hu)
    subst u
    exact .inl (x25519_entry_reachable hp hp rfl)
  | succ k ih =>
    intro u hu hne
    obtain ⟨a,ev,ha,hEv,hA,hs⟩ := hBack k u hu
    rcases ih a ha hA with hc | ⟨j,v,w,hj,hk,hR⟩
    · exact next ha hc hA hne hs
    · by_cases hEnd : k = j+(x25519_trace c).length
      · rw [hEnd,hR.finish] at ha
        have he := Option.some.inj ha
        subst a
        exact next (hEnd ▸ hR.finish) hR.post hA hne hs
      · exact .inr ⟨j,v,w,by omega,by omega,hR⟩

theorem X25519CallRecord.sp_at {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j i : Nat} {a b u : State} (r : X25519CallRecord c states tr j a b)
    (hi : i ≤ (x25519_trace c).length) (hu : states[j+i]? = some u) :
    u.sp = workSp (E c) := by
  by_cases hLast : i = (x25519_trace c).length
  · rw [hLast,r.finish] at hu
    cases hu
    exact r.sp
  · have hlt : i < (x25519_trace c).length := by omega
    obtain ⟨_,x,hx,hObs⟩ := r.at_step i _ (List.getElem?_eq_getElem hlt)
    rw [hu] at hx
    cases hx
    exact hObs.sp

theorem X25519CallRecord.core_at {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j k : Nat} {a b u : State} (r : X25519CallRecord c states tr j a b)
    (hj : j < k) (hk : k < j+(x25519_trace c).length)
    (hr : ∀ e, tr[k]? = some e → ∃ t, step u = .ok (t,e)) :
    X25519Ev.InvPc c.base u.pc := by
  let i := k-j
  have heq : j+i = k := by omega
  have hi : i < (x25519_trace c).length := by omega
  let ev := (x25519_trace c)[i]
  have he : (x25519_trace c)[i]? = some ev := List.getElem?_eq_getElem hi
  obtain ⟨ht,_,_,_⟩ := r.at_step i ev he
  rw [heq] at ht
  obtain ⟨_,hStep⟩ := hr ev ht
  rw [← step_ev_pc hStep]
  apply r.core ev
  have eI : i = (i-1)+1 := by omega
  rw [eI] at he
  exact List.mem_of_getElem? (show (x25519_trace c).tail[i-1]? = some ev from he)

end M0Crypto.Release.ConstantTime
