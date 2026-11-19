import M0Crypto.Release.Ed25519VerifyEntry
import M0Crypto.Release.Ed25519CallProgEntryGood
import M0Crypto.Release.Ed25519VerifyUniq

/-!
# The claims of `m0c_ed25519_verify` from its run

A valid call returns with its `Result` (`verify_reach`), reads and writes in its footprints and
keeps SP in its window. Its trace is `Good` by `entry_goodP` and `body_good`, at the callees'
premises the run establishes, so its states keep the stack discipline. Each state before the
return is at an instruction of the build, so the call is interruptible. Two calls with equal
public values agree on every readable buffer, so their body traces are equal (`bodyTr_congr`)
and each condition holds of one trace (`bodyTr_uniq`).
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (State Mem)
open M0Crypto.Thumb (CodeAt)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (BelowEntry)
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build Call)
open M0Crypto.Artifacts.Ed25519Compact (ed_l9)

theorem verify_correct : Ed25519.Verify.Correct := fun b c s hp => by
  letI := b.codeBytes
  exact call_returns c.toCall (verify_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.1.ret.pc, h.1⟩) (fun _ hy => wr_cases hy) (verify_reach hp)

theorem verify_reads : Ed25519.Verify.Reads := fun b c s hp => by
  letI := b.codeBytes
  exact call_reads c.toCall (verify_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.1.ret.pc) (fun _ hy => rd_cases hy) (verify_reach hp)

theorem verify_stack : Ed25519.Verify.Stack := fun b c s hp => by
  letI := b.codeBytes
  exact call_stack c.toCall (verify_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.1.ret.pc, h.1.ret.sp⟩) (verify_reach hp)

/-- Every long enough run of a valid call keeps the stack discipline, and each of its states
before the return is at an instruction of the build. -/
theorem verify_run {b : Build} {c : Ed25519.Verify.Ctx} {s : State} (hp : Ed25519.Verify.Pre b c s) :
    ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 Ed25519.Verify.stackBytes states tr ∧
      ∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ c.ret → Interrupt.CodePos c.base b.bytes u := by
  letI := b.codeBytes
  have k := verify_codeOk hp.valid
  obtain ⟨n, t, tr, hQ, hΦ, -, -, h2, -⟩ := claims_of k.pc_ne k.wc (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.1.ret.pc) (verify_reach hp)
  have hS := verify_geo.1
  have hc : ∀ y, Has [@codeR b.bytes b.size b.codeBytes c.base] y → ¬ BelowEntry c.sp0 (36 + verifyGeo.N) y :=
    fun y ⟨r, hr, hh⟩ hb => by
      rw [List.mem_singleton.mp hr] at hh; rw [hS] at hb
      exact disj_not hp.valid.call.codeS (rgn_region hh (size_lt b)) hb
  have hg := entry_goodP (c := verifyCtx c) rfl verify_entryOk rfl
    (body_good (vAd b) (frm_entry (verify_geoOk hp.valid) rfl (hS ▸ hp.valid.call.spLo))
      (fun y hy hb => absurd hb (hc y hy)) (lines_code b) hQ.2) tr hΦ
  rw [hS] at hg
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, hs, hall⟩ := h2 fuel hf
  refine ⟨states, tr, hs, discipline_of hs (by rw [hp.entry.call.regs]; exact hp.entry.call.sp) hg,
    fun i u hu hne => ?_⟩
  rcases hall u (List.mem_of_getElem? hu) with h | rfl
  · exact h.2
  · exact absurd hQ.1.ret.pc hne

theorem verify_discipline : Ed25519.Verify.StackDiscipline := fun _ _ _ hp => by
  obtain ⟨m, hm⟩ := verify_run hp
  exact ⟨m, fun fuel hf => let ⟨st, tr, h1, h2, _⟩ := hm fuel hf; ⟨st, tr, h1, h2⟩⟩

theorem verify_interrupted : Ed25519.Verify.Interrupted := fun K b c s hp => by
  letI := b.codeBytes
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (verify_reads b c s hp) (verify_stack b c s hp)
    (verify_run hp)
  · rw [b.codeBytes.len] at hy
    exact ⟨.inr (.inr (.inr (.inl hy))), fun hb => disj_not hp.valid.call.codeS hy hb⟩
  · obtain ⟨n, hn⟩ := verify_correct b c s hp
    exact ⟨n, fun fuel hf => let ⟨t, tr, ht, hr, _⟩ := hn fuel hf; ⟨t, tr, ht, hr⟩⟩

/-! ## Constant time -/

/-- Two entry memories that agree on every readable buffer agree on its regions. -/
theorem xAgree_of {G : Geo} {c : Ctx} {m0 m0' : Mem}
    (h : ∀ i x, G.xs[i]? = some x → x.r = true →
      bytesAt m0 (c.ptr i) (x.len.v c) = bytesAt m0' (c.ptr i) (x.len.v c)) :
    XAgree G c m0 m0' := by
  rintro ⟨l, n⟩ hok hx hacc
  cases l with
  | fr _ => cases hx
  | rg _ => cases hx
  | ex i e =>
    cases hxi : G.xs[i]? with
    | none => simp only [SR.acc, hxi] at hacc; cases hacc
    | some x =>
      simp only [SR.acc, hxi, Bool.false_eq_true, ite_false] at hacc
      have hb := h i x hxi hacc
      simp only [Loc.addr]
      cases n with
      | k n =>
        cases hL : x.len with
        | k L' =>
          simp only [SR.ok, hxi, hL, decide_eq_true_eq] at hok
          simp only [hL, XLen.v] at hb ⊢
          rw [bytesAt_slice m0 _ hok, bytesAt_slice m0' _ hok, hb]
        | p j =>
          simp only [SR.ok, hxi, hL, beq_iff_eq] at hok
          subst hok; rfl
      | p j =>
        simp only [SR.ok, hxi, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨rfl, hj⟩ := hok
        rw [hj] at hb
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hb

section
variable {b : Build} {c : Ed25519.Verify.Ctx} {s : State}

/-- The entry bytes of each readable buffer: `sig`, the message, `pk` and the code's `L`. -/
theorem buf_enter (hp : Ed25519.Verify.Pre b c s) : ∀ i x, verifyGeo.xs[i]? = some x → x.r = true →
    bytesAt (enterMem s c.sp0) ((verifyCtx c).ptr i) (x.len.v (verifyCtx c)) =
      [c.sigB, c.msgB, c.pkB, (b.bytes.drop ed_l9).take 32].getD i [] := by
  have hm := hp.entry.call.mem; have hv := hp.valid
  intro i x hx _
  rcases i with _ | _ | _ | _ | i <;> simp only [verifyGeo, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hx <;> subst hx <;>
    simp only [verifyCtx, XLen.v, List.getD_cons_zero, List.getD_cons_succ]
  · rw [enter_bytes (off_saved hv.sigS), hm]; rfl
  · rcases hv.msgS with h0 | hd
    · simp [h0, bytesAt, Ed25519.Verify.Ctx.msgB, Call.bytes, Frame.Ctx.bytesAt]
    · rw [enter_bytes (off_saved hd), hm]; rfl
  · rw [enter_bytes (off_saved hv.pkS), hm]; rfl
  · exact M0Crypto.Release.Ed25519ScReduceProg.code_bytes (code_enter hp)
      (by rw [b.codeBytes.len]; exact (vcall_cs b).2.2.1)

end

theorem verify_ct : Ed25519.Verify.ConstantTime := by
  intro b c₁ c₂ s₁ s₂ h₁ h₂ hpub
  letI := b.codeBytes
  simp only [Ed25519.Verify.Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hsig, hmsg, hlen, hpk, hsB, hmB, hpB⟩ := hpub
  have hctx : verifyCtx c₁ = verifyCtx c₂ := by simp only [verifyCtx, hb, hsp, hsig, hmsg, hlen, hpk]
  have hret : c₁.ret = c₂.ret := by simp only [Call.ret, hlr]
  have hA : XAgree verifyGeo (verifyCtx c₂) (enterMem s₁ c₁.sp0) (enterMem s₂ c₂.sp0) :=
    xAgree_of fun i x hx hr => by
      have e₁ := buf_enter h₁ i x hx hr; have e₂ := buf_enter h₂ i x hx hr
      rw [hctx] at e₁; rw [e₁, e₂, hsB, hmB, hpB]
  have hT : verifyTr b c₁ (enterMem s₁ c₁.sp0) = verifyTr b c₂ (enterMem s₂ c₂.sp0) := by
    unfold verifyTr; rw [hctx, bodyTr_congr (vAd b) hA, hsp]
  have k₁ := verify_codeOk h₁.valid; have k₂ := verify_codeOk h₂.valid
  have r₁ := verify_reach h₁; have r₂ := verify_reach h₂
  have hc₁ : CodeAt s₁.mem c₁.base b.bytes := h₁.entry.call.mem ▸ h₁.valid.call.code
  rw [hT, hsp, hb] at r₁; rw [hsp, hb, hret] at k₁; rw [hb] at hc₁; rw [hret]
  exact traceEq_of (show Tr.Uniq (verifyTr b c₂ (enterMem s₂ c₂.sp0)) from entryTrP_uniq ((vAd b).bodyTr_uniq _ _))
    k₁.pc_ne k₁.wc k₂.pc_ne k₂.wc hc₁ (h₂.entry.call.mem ▸ h₂.valid.call.code)
    (fun _ h => h.1.ret.pc.trans hret) (fun _ h => h.1.ret.pc) r₁ r₂

end M0Crypto.Release.Ed25519VerifyProg
