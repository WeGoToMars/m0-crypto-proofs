import M0Crypto.Release.ConstantTime.Entries
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.ConstantTime.FunctionalWrites

/-! Contract consequences needed by the analysis and return-state bounds. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Release

/-- The ChaCha contract separates code from the complete analysis window. -/
theorem chacha20_code_stack_disjoint (c : Frame.Ctx) (hv : Frame.Valid c) :
    Frame.Disj c.base Artifacts.Release.bytes.length
      (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) := by
  simpa [Artifacts.Release.bytes_length, chacha20Env, chacha20ArgWords,
    TraceSpec.chacha20StackBytes, Frame.Ctx.fp, ChaCha20Layout.chStackBytes_eq] using hv.codeF

/-- The AEAD contract separates code from the complete analysis window. -/
theorem aead_code_stack_disjoint (c : Aead.ACall) (hv : Aead.AValid c) :
    Frame.Disj c.base Artifacts.Release.bytes.length
      (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) := by
  simpa [Artifacts.Release.bytes_length, encryptEnv, aeadArgWords,
    TraceSpec.aeadStackBytes] using hv.codeS

theorem chacha20_code_no_wrap (c : Frame.Ctx) (hv : Frame.Valid c) :
    c.base.toNat + Artifacts.Release.bytes.length ≤ 2 ^ 32 := by
  simpa [Artifacts.Release.bytes_length] using hv.codeF.1

theorem aead_code_no_wrap (c : Aead.ACall) (hv : Aead.AValid c) :
    c.base.toNat + Artifacts.Release.bytes.length ≤ 2 ^ 32 := by
  simpa [Artifacts.Release.bytes_length] using hv.codeS.1

/-- A returned state with restored SP lies in any stack window at entry SP. -/
theorem restored_sp_in_stack_window {sp0 : M0Crypto.Armv6M.Word} {s : State}
    (hsp : s.regs 13 = sp0) (below : Nat) :
    TraceSpec.InStackWindow sp0 below (s.regs 13) := by
  exact ⟨0, Nat.zero_le _, by simpa using hsp⟩

theorem chacha20_result_stack_window (c : Frame.Ctx) (s : State)
    (h : ChaCha20Xor.Result c s) :
    TraceSpec.InStackWindow c.sp0 chacha20Env.win.below (s.regs 13) :=
  restored_sp_in_stack_window h.sp _

theorem aead_result_stack_window (c : Aead.ACall) (result : M0Crypto.Armv6M.Word)
    (s : State) (h : Aead.RetPost c result s) :
    TraceSpec.InStackWindow c.sp0 encryptEnv.win.below (s.regs 13) :=
  restored_sp_in_stack_window h.sp _

/-- The final recorded state agrees with the state returned by `runUntil`. -/
theorem runStates_final {stop : M0Crypto.Armv6M.Word} {fuel : Nat} {s : State}
    {states : List State} {events : List M0Crypto.Thumb.Event}
    (hrun : runStates stop fuel s = .ok (states, events)) :
    ∃ last, states.getLast? = some last ∧
      M0Crypto.Thumb.runUntil stop fuel s = .ok (last, events) := by
  induction fuel generalizing s states events with
  | zero =>
    simp only [runStates] at hrun
    split at hrun
    · rename_i hp
      cases hrun
      exact ⟨s, by simp, by simp [M0Crypto.Thumb.runUntil, hp]⟩
    · contradiction
  | succ fuel ih =>
    simp only [runStates] at hrun
    split at hrun
    · rename_i hp
      cases hrun
      exact ⟨s, by simp, by simp [M0Crypto.Thumb.runUntil, hp]⟩
    · rename_i hp
      cases hs : M0Crypto.Thumb.step s with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨last, hlast, hfinal⟩ := ih ht
          have hne : rest ≠ [] := (runStates_nonempty ht).1
          refine ⟨last, ?_, ?_⟩
          · cases rest with
            | nil => contradiction
            | cons x xs => simpa using hlast
          · simp [M0Crypto.Thumb.runUntil, hp, hs, hfinal]

/-- The final state of every successful recorded decryption has a restored
stack pointer, including when the execution stops immediately after return. -/
theorem decrypt_final_stack_window (c : Aead.ACall) (hv : Aead.AValid c)
    (hb : Aead.ABuf c) (s : State) (he : Aead.AEntry c Aead.decOff s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List M0Crypto.Thumb.Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∃ last, states.getLast? = some last ∧
      TraceSpec.InStackWindow c.sp0 decryptEnv.win.below (last.regs 13) := by
  obtain ⟨n, hc⟩ := Aead.decrypt_correct c hv hb s he hlr hret
  obtain ⟨t, tr, ht, hresult, _⟩ := hc n (Nat.le_refl n)
  obtain ⟨last, hlast, hrun'⟩ := runStates_final hrun
  have ht' := (runUntil_success_unique ht hrun').1
  subst last
  refine ⟨t, hlast, ?_⟩
  exact restored_sp_in_stack_window hresult.abi.sp _

/-- The final state of a successful ChaCha recording has its entry SP. -/
theorem chacha20_final_stack_window (c : Frame.Ctx) (hv : Frame.Valid c)
    (s : State) (he : ChaCha20Setup.Entry c s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List M0Crypto.Thumb.Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∃ last, states.getLast? = some last ∧
      TraceSpec.InStackWindow c.sp0 chacha20Env.win.below (last.regs 13) := by
  obtain ⟨n, hc⟩ := ChaCha20Xor.xor_correct c hv s he hlr hret
  obtain ⟨t, tr, ht, hresult, _⟩ := hc n (Nat.le_refl n)
  obtain ⟨last, hlast, hrun'⟩ := runStates_final hrun
  have ht' := (runUntil_success_unique ht hrun').1
  subst last
  exact ⟨t, hlast, restored_sp_in_stack_window hresult.sp _⟩

/-- The final state of a successful encryption recording has its entry SP. -/
theorem encrypt_final_stack_window (c : Aead.ACall) (hv : Aead.AValid c)
    (hb : Aead.ABuf c) (s : State) (he : Aead.AEntry c Aead.encOff s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List M0Crypto.Thumb.Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∃ last, states.getLast? = some last ∧
      TraceSpec.InStackWindow c.sp0 encryptEnv.win.below (last.regs 13) := by
  obtain ⟨n, hc⟩ := Aead.encrypt_correct c hv hb s he hlr hret
  obtain ⟨t, tr, ht, hresult, _⟩ := hc n (Nat.le_refl n)
  obtain ⟨last, hlast, hrun'⟩ := runStates_final hrun
  have ht' := (runUntil_success_unique ht hrun').1
  subst last
  exact ⟨t, hlast, restored_sp_in_stack_window hresult.sp _⟩

end M0Crypto.Release.ConstantTime
