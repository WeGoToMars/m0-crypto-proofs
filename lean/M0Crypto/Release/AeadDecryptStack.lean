import M0Crypto.Release.ConstantTime.LowEqLeft
import M0Crypto.Release.AeadStoreCheck
import M0Crypto.Release.ChaCha20XorReads
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ChaCha20XorStack
import M0Crypto.Release.AeadDecryptSite
import M0Crypto.Release.ConstantTime.DecryptBufferStores

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Stack bounds of the AEAD functions

The policy run `decrypt_reach_p` bounds, at every visited state, the writes of the step by the
functional write set and, at output-store instructions with counter word `1`, by the output buffer.
Together with the static counter check this classifies every untracked store as an output store,
which is the certificate's store-separation premise; the certificate then bounds SP.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

theorem counter_eq (c : ACall) : c.sp0 + BitVec.ofInt 32 counterSlot = c.A + 4#32 := by
  have h : BitVec.ofInt 32 counterSlot = (0#32 - 144#32) + 4#32 := by rfl
  rw [h]
  unfold ACall.A
  simp only [BitVec.sub_eq_add_neg, BitVec.zero_add, BitVec.add_assoc]

/-- At a certificate position inside the code, the PC is not the return address. -/
theorem point_pc_ne_stop {env : Env} {cert : Cert} {entry : Nat} {init : AbsState} {c : ACall}
    {x y : State} {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hok : certOk env M0Crypto.Artifacts.Release.bytes entry init cert = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (hlow : LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes off st x y) :
    x.pc ≠ c.regs0 14 &&& ~~~1#32 := by
  have hf := (certPoint_instrAt hok hm hp).2
  have hpos := instr_size_pos i
  have hoff : off < M0Crypto.Artifacts.Release.size := by
    simpa [B_len] using (show off < M0Crypto.Artifacts.Release.bytes.length by omega)
  rw [hlow.pc]
  exact Ne.symm (hret off hoff)

/-- A policy step at a certified untracked store writes no stack byte. -/
theorem nonStack_of_policy (c : ACall) (hv : AValid c) (hb : ABuf c) {Pc Wr : Word → Prop}
    {x : State} {e : Event} {st : AbsState} {i : Instr} {off : Nat}
    (hpc : x.pc = c.base + BitVec.ofNat 32 off) (hev : e = ⟨x.pc, i, i.accesses x⟩)
    (hpol : PolW c Pc Wr x e)
    (hsite : outputStoreOffset off = true) (hcnt : read32 x.mem (c.A + 4#32) = 1#32) :
    NonStackStoreBytes c st x i := by
  have hsite' : OutputStorePC c.base e.pc := by
    rw [hev]; dsimp only; rw [hpc]; exact outputStoreOffset_pc _ _ hsite
  have hout := hpol.2 hsite' hcnt
  subst hev
  cases i with
  | memImm op t n imm =>
    intro _ hop k hk
    apply output_not_swr c hv hb
    apply hout
    exact ⟨⟨.write, x.reg n + BitVec.ofNat 32 (imm.toNat * op.width), op.width⟩,
      by simp [Instr.accesses, hop], rfl, k, hk, rfl⟩
  | memReg op t n m =>
    intro _ hop k hk
    apply output_not_swr c hv hb
    apply hout
    exact ⟨⟨.write, x.reg n + x.reg m, op.width⟩, by simp [Instr.accesses, hop], rfl, k, hk, rfl⟩
  | _ => trivial

theorem decrypt_pol_recorded (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, x.pc ≠ c.regs0 14 &&& ~~~1#32 →
      ∃ t e, step x = .ok (t, e) ∧ PolW c (DecAllPc c.base) (DAllowed c) x e := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have h : ReachS c.base (PolW c (DecAllPc c.base) (DAllowed c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ DecryptResult c t) :=
    (decrypt_reach_p (Pc := DecAllPc c.base) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.abi.pc, h⟩)
  refine ReachS.recorded ?_ hc h hrun
  intro x e h i hi hw
  rw [B_len] at hi
  rcases h.1.2 _ hw with hs | ⟨_, ho⟩
  · exact hv.code_not_swr hi hs
  · exact not_out hb.codeO hi ho


/-- The public part of a call fixes the link register and the base. -/
theorem pub_lr {c₁ c₂ : ACall} (h : c₁.pub = c₂.pub) : c₁.regs0 14 = c₂.regs0 14 := by
  simp only [ACall.pub, Prod.mk.injEq] at h
  exact h.2.2.1

theorem pub_base {c₁ c₂ : ACall} (h : c₁.pub = c₂.pub) : c₁.base = c₂.base := by
  simp only [ACall.pub, Prod.mk.injEq] at h
  exact h.1

/-- The artifact is disjoint from the decrypt stack window and does not wrap. -/
theorem decrypt_frame (c : ACall) (hv : AValid c) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.bytes.length
      (c.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above) ∧
    c.base.toNat + M0Crypto.Artifacts.Release.bytes.length ≤ 2 ^ 32 :=
  ⟨by simpa [decryptEnv, aeadArgWords, M0Crypto.Release.TraceSpec.aeadStackBytes, B_len] using hv.codeS,
   by simpa [B_len] using hv.codeS.1⟩

/-- Every checked store of a recorded decrypt run satisfies the certificate's separation
premise; it holds for the first state of any related pair (`LowEq.left`). -/
theorem decrypt_hbuffer (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, ∀ y b off st i is, b ∈ decryptCert →
      BlockPoint decryptEnv b off st (i :: is) →
      LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes off st x y →
      BufferStoreOk decryptEnv
        ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes st x i := by
  intro x hx y b off st i is hm hp hlow'
  have hlow := hlow'.left
  have hstop := point_pc_ne_stop decrypt_certOk hret hm hp hlow
  obtain ⟨t', e, hst, hpol⟩ := decrypt_pol_recorded c hv hb s he hlr hrun x hx hstop
  have hev := ChaCha20XorReads.certPoint_step_event i decrypt_certOk decrypt_certAligned
    (by show c.base.toNat % 2 = 0; have := hv.base4; omega) hm hp hlow hst
  apply decrypt_recorded_bufferStoreOk c hv hb s x he hlr hret hrun hm hp hlow hx
  by_cases hu : untrackedStore st i = true
  · rcases untracked_cases decrypt_counter hm hp hu with ⟨hsite, hcnt⟩ | hf
    · have hc1 := counter_of_stack (x := x) (y := x) hlow.stack (by simpa using hcnt)
      have hc2 : read32 x.mem (c.A + 4#32) = 1#32 := by
        rw [← counter_eq c]; exact hc1
      exact nonStack_of_policy c hv hb hlow.pc hev hpol hsite hc2
    · simp at hf
  · cases i with
    | memImm op t n imm => intro hsp hop; simp [untrackedStore, hop, hsp] at hu
    | memReg op t n m => intro hsp hop; simp [untrackedStore, hop, hsp] at hu
    | _ => trivial

/-- The certificate relation holds at every visited non-final state of a recorded run. -/
theorem decrypt_certAt_states (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ u ∈ states, u.pc ≠ c.regs0 14 &&& ~~~1#32 →
      CertAt decryptEnv decryptCert ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u u := by
  obtain ⟨hdisj, hnowrap⟩ := decrypt_frame c hv
  have hbuffer := fun x hx => decrypt_hbuffer c hv hb s he hlr hret hrun x hx x
  intro u hu hpc
  exact recorded_self_certAt decrypt_certOk decrypt_indicesFailure_eq_none
    decrypt_certAligned decrypt_slotsCheck (by decide) hdisj (by decide) hv.base4 hnowrap hlr
    hrun hbuffer (decrypt_entry_reachable hv he hv he rfl) hu hpc

/-- **Every state of AEAD decryption keeps SP in the stack window.** -/
theorem _root_.M0Crypto.Release.Aead.decrypt_stack : TraceSpec.AeadDecryptStack := by
  intro c s ⟨hv, hb, he, hlr, hret⟩
  replace hret := Region.ne hret
  obtain ⟨n, hcorrect⟩ := decrypt_correct c s ⟨hv, hb, he, hlr, Region.not hret⟩
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, ?_⟩
  intro u hu
  by_cases hpc : u.pc = c.regs0 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hw⟩ := decrypt_final_stack_window c hv hb s he hlr hret hrun
    have := Release.runStates_stop_last hrun u hu hpc
    rw [hlast] at this
    cases this
    simpa [decryptEnv, M0Crypto.Release.TraceSpec.aeadStackBytes] using hw
  · have hself := decrypt_certAt_states c hv hb s he hlr hret hrun u hu hpc
    obtain ⟨b, off, st, code, hm, hp, hnil, hlow⟩ := hself
    cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      obtain ⟨out, hx⟩ := certPoint_xfer decrypt_certOk hm hp
      simpa [decryptEnv, M0Crypto.Release.TraceSpec.aeadStackBytes] using (xfer_stack_window hlow hx).1

end M0Crypto.Release.ConstantTime
