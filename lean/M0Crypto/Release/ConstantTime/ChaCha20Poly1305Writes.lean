import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Buffers
import M0Crypto.Release.AeadDecrypt
set_option maxRecDepth 100000

/-!
Functional write facts of `m0c_chacha20_xor` and AEAD decryption.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- Every successful recorded decryption run inherits the functional proof's
byte-wise write bound, independent of its fuel allowance. -/
theorem decrypt_recorded_writes (c : ACall) (hv : AValid c) (hb : ABuf c)
    (s : State) (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    WritesTo (DAllowed c) events := by
  obtain ⟨n, hcorrect⟩ := decrypt_correct c s ⟨hv, hb, he, hlr, Region.not hret⟩
  obtain ⟨t, tr, ht, _, hw⟩ := hcorrect n (Nat.le_refl n)
  have hrun' := runStates_events (c.regs0 14 &&& ~~~1#32) fuel s
  simp only [hrun, Except.map] at hrun'
  change Except.ok events = (runUntil (c.regs0 14 &&& ~~~1#32) fuel s).map Prod.snd at hrun'
  cases hfinal : runUntil (c.regs0 14 &&& ~~~1#32) fuel s with
  | error err =>
    have hcontra := congrArg (Except.map Prod.snd) hfinal
    rw [← hrun'] at hcontra
    cases hcontra
  | ok pair =>
    obtain ⟨last, actual⟩ := pair
    simp only [hfinal, Except.map, Except.ok.injEq] at hrun'
    have heq := (runUntil_success_unique ht hfinal).2
    rw [hrun', ← heq]
    exact hw

/-- At a store known not to target the stack, the functional decryption write
bound puts the entire access in the output buffer and hence separates it from
the code and analysis stack. -/
theorem decrypt_store_bounds_of_write_bounds (c : ACall) (hb : ABuf c)
    (op : MemOp) (a : Word)
    (hw : ∀ k, k < op.width → DAllowed c (a + BitVec.ofNat 32 k))
    (hstack : ∀ k, k < op.width → ¬ SWr c.A (a + BitVec.ofNat 32 k)) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.size a op.width ∧
    Frame.Disj (c.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above) a op.width := by
  have hwpos := memOp_width_pos op
  have hout (k : Nat) (hk : k < op.width) : OutR c (a + BitVec.ofNat 32 k) := by
    rcases hw k hk with hs | ⟨_, ho⟩
    · exact False.elim (hstack k hk hs)
    · exact ho
  have hfirst := hout 0 (by omega)
  simp only [BitVec.add_zero] at hfirst
  simpa [decryptEnv, encryptEnv] using
    aead_output_endpoints c hb op a hfirst (hout (op.width - 1) (by omega))

/-- Site classification needed for untracked single-register stores: no byte
of such a store is in the functional stack-write region. -/
def NonStackStoreBytes (c : ACall) (st : AbsState) (s : State) : Instr → Prop
  | .memImm op _ n imm =>
    ((st.get n.val).addK (imm.toNat * op.width)).isSp = false → op.isLoad = false →
      ∀ k, k < op.width → ¬ SWr c.A
        (s.reg n + BitVec.ofNat 32 (imm.toNat * op.width) + BitVec.ofNat 32 k)
  | .memReg op _ n m =>
    ((st.get n.val).add (st.get m.val)).isSp = false → op.isLoad = false →
      ∀ k, k < op.width → ¬ SWr c.A (s.reg n + s.reg m + BitVec.ofNat 32 k)
  | _ => True

theorem output_not_swr (c : ACall) (hv : AValid c) (hb : ABuf c) {y : Word}
    (hy : OutR c y) : ¬ SWr c.A y := by
  have hd : Frame.Disj c.out c.len.toNat (c.sp0 - 320#32) 320 := by
    rcases hb.outS with ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, by omega⟩
  rw [Frame.eq_add_sub c.out y]
  exact hv.not_swr hd hy

/-- A write event lies in an output chunk or byte-tail block whose functional
loop bounds match the caller's output buffer. -/
def OutputSegmentEvent (c : ACall) (e : Event) : Prop :=
  ∃ xc : Frame.Ctx, Frame.Valid xc ∧ xc.out = c.out ∧ xc.len = c.len ∧
    ∃ (k : Nat) (t : State), t.regs 3 = xc.out + BitVec.ofNat 32 (64 * k) ∧
      ((∃ i, i < 16 ∧ 64 * k + 4 * i + 4 ≤ xc.len.toNat ∧
          e ∈ traceAll (ChaCha20Output.ach i) t) ∨
       (64 * k + (t.regs 0).toNat < xc.len.toNat ∧ e ∈ traceAll ChaCha20Output.bl t))

/-- In a successful recorded run, the certificate relation holds at every
visited non-return state if recorded buffer stores satisfy separation. -/
theorem recorded_self_certAt {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s u : State}
    {fuel : Nat} {states : List State} {events : List Event}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hrun : runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, events))
    (hbuffer : ∀ x ∈ states, ∀ b off st i is, b ∈ cert →
      BlockPoint env b off st (i :: is) → LowEq p bytes off st x x →
      BufferStoreOk env p bytes st x i)
    (hentry : CertAt env cert p bytes s s) (hmem : u ∈ states)
    (hstop : u.pc ≠ (p.lr0 &&& ~~~1#32)) : CertAt env cert p bytes u u := by
  have hreach := runStates_beforeStop hrun u hmem
  have hinv : RunRel env cert p bytes (p.lr0 &&& ~~~1#32) u u := by
    induction hreach with
    | initial => exact Or.inl hentry
    | @next x y ev hreach hnot hs ih =>
      have hxmem := hreach.mem_runStates hrun
      rcases ih hxmem hnot with hcert | ⟨hret, _⟩
      ·
        have hlocal : PositionObligations env cert p bytes x x := by
          intro b off st i is hm hp hrel
          exact ⟨hbuffer _ hxmem b off st i is hm hp hrel, pubLoadOk_self _ _ _ _, by intros; rfl⟩
        have hpaired := certAt_run_paired hc hi ha hslots hwidth hdisj hsize hbase
          hnowrap hlr hcert hlocal
        simp only [PairedStep, hs] at hpaired
        exact hpaired.2
      · exact False.elim (hnot hret)
  rcases hinv with hcert | ⟨hret, _⟩
  · exact hcert
  · exact False.elim (hstop hret)

end M0Crypto.Release.ConstantTime
