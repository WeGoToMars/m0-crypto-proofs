import M0Crypto.Release.Ed25519SignRun
import M0Crypto.Release.Ed25519CallProgEntryGood

/-!
# Stack discipline and interrupts of `m0c_ed25519_sign`

The trace of a valid call is `Good` by `entry_good`, so its states keep the stack discipline.
Each state before the return is at an instruction of the build, so the call is interruptible.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (State)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect

section
variable (C : ∀ b, Callees b)
include C

/-- Every long enough run of a valid call keeps the stack discipline, and each of its states
before the return is at an instruction of the build. -/
theorem sign_run {b : Build} {c : Ed25519.Sign.Ctx} {s : State} (hp : Ed25519.Sign.Pre b c s) :
    ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 Ed25519.Sign.stackBytes states tr ∧
      ∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ c.ret → Interrupt.CodePos c.base b.bytes u := by
  letI := b.codeBytes
  have k := sign_codeOk hp.valid
  obtain ⟨n, t, tr, hQ, hΦ, -, -, h2, -⟩ := claims_of k.pc_ne k.wc (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.ret.pc) (sign_reach b (C b) hp)
  have hg := entry_good (sign_geoOk hp.valid) rfl (sign_geo.1 ▸ hp.valid.call.spLo) (C b).ef
    (fun y ⟨r, hr, hh⟩ hb => by
      rw [List.mem_singleton.mp hr] at hh; rw [sign_geo.1] at hb
      exact disj_not hp.valid.call.codeS (rgn_region hh (size_lt b)) hb)
    signProg sign_entryOk sign_fin.1 rfl rfl (by decide +kernel) (sign_bok b) rfl tr hΦ
  rw [sign_geo.1] at hg
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, hs, hall⟩ := h2 fuel hf
  refine ⟨states, tr, hs, discipline_of hs (by rw [hp.entry.call.regs]; exact hp.entry.call.sp) hg,
    fun i u hu hne => ?_⟩
  rcases hall u (List.mem_of_getElem? hu) with h | rfl
  · exact h.2
  · exact absurd hQ.ret.pc hne

theorem sign_discipline : Ed25519.Sign.StackDiscipline := fun _ _ _ hp => by
  obtain ⟨m, hm⟩ := sign_run C hp
  exact ⟨m, fun fuel hf => let ⟨st, tr, h1, h2, _⟩ := hm fuel hf; ⟨st, tr, h1, h2⟩⟩

theorem sign_interrupted : Ed25519.Sign.Interrupted := fun K b c s hp => by
  letI := b.codeBytes
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (sign_reads C b c s hp) (sign_stack C b c s hp)
    (sign_run C hp)
  · rw [b.codeBytes.len] at hy
    exact ⟨.inr (.inr (.inl hy)), fun hb => disj_not hp.valid.call.codeS hy hb⟩
  · obtain ⟨n, hn⟩ := sign_correct C b c s hp
    exact ⟨n, fun fuel hf => let ⟨t, tr, ht, hr, _⟩ := hn fuel hf; ⟨t, tr, ht, hr⟩⟩

end

end M0Crypto.Release.Ed25519CallProg
