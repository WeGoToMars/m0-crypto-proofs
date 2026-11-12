import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ReadBounds
import M0Crypto.Release.ConstantTime.RunInvariant
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.TraceSpec

set_option linter.unusedSimpArgs false

/-!
# Read bounds along a certified run

A certificate relates the run to itself, so every position of the run has a certificate point.
A read at that point is in the entry stack window or the artifact (`xfer_reads`), unless the
instruction is a load through a non-stack address. Those loads are the *load sites*: the
certificate must list them (`certLoadFailure`), and the caller bounds the bytes they read.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release

theorem certificate_run_reads {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s s)
    {ok : Nat → Bool} (hl : certLoadFailure ok env cert = none) (R : Word → Prop)
    (hsite : ∀ u t ev, BeforeStop (p.lr0 &&& ~~~1#32) s u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → ∀ off, u.pc = p.base + BitVec.ofNat 32 off → ok off = true →
      ∀ i, instrAt bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → R y)
    {fuel : Nat} {states : List State} {tr : List Event}
    (hrun : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, tr)) :
    TraceSpec.ReadsFrom (fun y => ReadOk p env y ∨ R y) tr := by
  have hq := runStates_events_invariant (fun u => BeforeStop (p.lr0 &&& ~~~1#32) s u)
    (fun ev => ∀ y, Reads ev.accesses y → ReadOk p env y ∨ R y)
    (p.lr0 &&& ~~~1#32) ?_ fuel BeforeStop.initial hrun
  · intro e he y hy
    exact hq e he y hy
  · intro u t ev hu hne hst
    refine ⟨BeforeStop.next hu hne hst, ?_⟩
    obtain ⟨u₂, hrel, -⟩ := certificate_reachable_partner hc hi ha hslots hwidth hdisj hsize hbase
      hnowrap hlr hlocal h u hu
    rcases hrel with ⟨b, off, st, code, hm, hp, hnil, hlow⟩ | ⟨hpc, _⟩
    · cases code with
      | nil => exact absurd rfl hnil
      | cons i is =>
        have hbase2 : p.base.toNat % 2 = 0 := by omega
        have hev := certPoint_step_event i hc ha hbase2 hm hp hlow hst
        obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
        by_cases hld : loadSite st i = true
        · have hoff := certPoint_loadSite hl hm hp hld
          intro y hy
          exact Or.inr (hsite u t ev hu hne hst off hlow.pc hoff i (certPoint_instrAt hc hm hp).1
            (by rw [hev]) y hy)
        · have hl' : loadSite st i = false := by simpa using hld
          intro y hy
          subst hev
          obtain ⟨a, ha', hk, q, hq', rfl⟩ := hy
          exact Or.inl (xfer_reads i hlow hx hsize hbase hnowrap hl' a ha' hk q hq')
    · exact absurd hpc hne

end M0Crypto.Release.ConstantTime
