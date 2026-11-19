import M0Crypto.Release.Ed25519PubkeyProg
import M0Crypto.Release.Ed25519CallProgEntryGood

/-!
# The run and the released claims of `m0c_ed25519_pubkey`

As sign's (`Ed25519SignRun`, `Ed25519SignEffect`), conditional on the callee adapters
`C : ∀ b, Callees b`: the program's value at `pk` is RFC 8032's public key of the seed
(`progPk_spec`), `entry_run` gives the call's `Result`, and `call_returns`, `call_reads`,
`call_stack`, `traceEq_of`, `entry_good` and the interrupt bridge give the six claims.
-/

namespace M0Crypto.Release.Ed25519PubkeyProg

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build Call)
open M0Crypto.Release.Ed25519Bytes (clampNat)
open M0Crypto.Spec.Ed25519 (encodeInt decodeInt encodePoint scalarMul)
open M0Crypto.Spec.Sha512 (sha512)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_pubkey)

/-! ## The value at `pk` -/

/-- What the program leaves at `pk`, from the seed. -/
def progPk (seed : List Byte) : List Byte :=
  encodePoint (scalarMul (decodeInt (clampSc (((sha512 ([] ++ seed)).drop 0).take 32))) Spec.Ed25519.B)

theorem pubkey_ev (c : Ctx) (m0 : Mem) :
    Prog.ev eaS ebS pubkeyGeo semE semB c m0 pubkeyProg pubkeySt (fun _ => .none) (.ex 0 0) =
      .b (progPk (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) 32)) := rfl

/-- **The program's public key is RFC 8032's** (section 5.1.5). -/
theorem progPk_spec (seed : List Byte) : progPk seed = Spec.Ed25519.publicKey seed := by
  have hl := sha512_length seed
  simp only [progPk, Spec.Ed25519.publicKey, List.nil_append, clampSc, List.drop_zero, decodeInt_encodeInt,
    ← Ed25519Bytes.secretScalar_eq _ (by omega : 32 ≤ (sha512 seed).length)]
  rw [Nat.mod_eq_of_lt (by rw [Ed25519Bytes.secretScalar_eq _ (by omega)]; exact Nat.lt_trans (clampNat_lt _) (by decide))]

/-! ## The final state -/

def pubkeyFin : St := (pubkeyProg.ty eaS ebS pubkeyGeo pubkeySt).getD pubkeySt

theorem pubkey_ty : (pubkeyProg.ty eaS ebS pubkeyGeo pubkeySt).isSome = true := by decide +kernel

theorem pubkey_fin : pubkeyProg.ty eaS ebS pubkeyGeo pubkeySt = some pubkeyFin ∧
    pubkeyFin.X = [⟨.ex 0 0, .k 32⟩] ∧ (Loc.ex 0 0, Kd.bytes 32) ∈ pubkeyFin.Γ := by
  decide +kernel

section
variable {b : Build} {c : Ed25519.Pubkey.Ctx}

theorem x_pk {r : SR} {y : Word} (hr : r ∈ pubkeyFin.X) (h : Has (r.rgns pubkeyGeo (pubkeyCtx c)) y) :
    Region c.pk 32 y := by
  rw [pubkey_fin.2.1] at hr
  obtain ⟨q, hq, hy⟩ := h
  simp only [List.mem_singleton] at hr; subst hr
  simp only [SR.rgns, XLen.v, Loc.addr, pubkeyCtx, List.getD_cons_zero, List.mem_ite_nil_left,
    List.mem_singleton] at hq
  obtain ⟨-, rfl⟩ := hq; exact half_in hy (by omega) (by decide)

end

/-! ## The run -/

/-- The trace condition of a call with body context `c` and entry SP `sp0`. -/
def pubkeyTr {b : Build} (C : Callees b) (c : Ctx) (sp0 : Word) : TrP :=
  entryTr eaS ebS pubkeyGeo (fun a => @Ad.T C.Rs b.bytes b.size b.codeBytes _ (C.ad a)) c sp0
    ed25519_pubkey pubkeyProg pubkeySt

/-- **A valid call of pubkey returns with its `Result`**, given the callee adapters. -/
theorem pubkey_reach (b : Build) (C : Callees b) {c : Ed25519.Pubkey.Ctx} {s : State}
    (hp : Ed25519.Pubkey.Pre b c s) :
    @ReachFT b.bytes b.size b.codeBytes c.base (PcIn c.base pubkeyGeo.cs) (Has (savedR c.sp0 :: pubkeyRc b c))
      (Has (savedR c.sp0 :: pubkeyWc c)) (InStackWindow c.sp0 Ed25519.Pubkey.stackBytes) s
      (Ed25519.Pubkey.Result c) (pubkeyTr C (pubkeyCtx c) c.sp0) := by
  obtain ⟨hv, he⟩ := hp
  have hS := pubkey_geo.1
  have hs := he.call.regs; have hm := he.call.mem
  rw [← hS]
  refine @entry_run C.Rs b.bytes b.size b.codeBytes _ _ eaS ebS C.ad (bdS C.Rs) (pubkeyCtx c) pubkeyGeo
    (pubkeyWc c) (pubkeyRc b c) (pubkey_geoOk hv) (pubkey_caller hv)
    (sub_one (by simp [pubkeyRc, codeR, pubkeyCtx]) hv.codeO.1) pubkeyProg pubkeySt pubkeyFin ed25519_pubkey s
    c.sp0 _ pubkey_entryOk pubkey_fin.1 rfl rfl (pubkey_bok b) (pubkey_pieces b).1 (pubkey_pieces b).2 rfl
    (by rw [hS]; exact hv.call.spLo) (by rw [hs]; exact he.call.sp)
    (by show s.regs 15 = _; rw [hs, he.call.pc, (pubkey_cs b).2]; rfl) (hm ▸ hv.call.code)
    (fun i hi => off_saved hv.call.codeS i (b.codeBytes.len ▸ hi)) rfl rfl ?_
    (fun y hy r hr hh => disj_not hv.pkS (x_pk hr hh) (saved_S hy)) (by rw [hs]; exact hv.call.thumb) ?_
  · intro p hp
    simp only [pubkeySt, pubkeyσ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals first
      | exact .inr rfl
      | exact .inl ⟨by decide, by simp [SV.val, pubkeyCtx, hs, he.r0, he.r1]⟩
  · intro mb u hI hpc h13 hcal h1 h2 h3 h12 hsv hz hout
    have hE : (fun a => @Ad.sem C.Rs b.bytes b.size b.codeBytes _ (C.ad a)) = semE := funext C.sem
    have hB : (fun b => (bdS C.Rs b).sem) = semB := funext fun b => by cases b <;> rfl
    rw [hE, hB] at hI
    have r0 := (hI.1 _ pubkey_fin.2.2).2
    dsimp only at r0; rw [pubkey_ev] at r0
    simp only [Rel, Loc.addr, pubkeyCtx, List.getD_cons_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] at r0
    have hseed : bytesAt (enterMem s c.sp0) c.seed 32 = c.seedB := by
      rw [enter_bytes fun j hj => off_saved hv.seedS j (by omega), hm]; rfl
    have hpk : bytesAt mb c.pk 32 = c.pkOut := by
      rw [r0, show [c.pk, c.seed].getD 1 0#32 = c.seed from rfl, hseed, progPk_spec]; rfl
    have hres := call_result c.toCall hs hpc h13 hcal h1 h2 h3 h12 hsv hz
    rw [hS] at hres
    refine ⟨hres.1, hres.2, memOut_of c.toCall (fun y hy => hout y (by rw [hS]; exact hy))
      (fun i hi => byte_of hpk hi) fun y hy hy' => ?_⟩
    rw [hI.2.1 y (fun h => hy (win_S h)) (fun r hr hh => hy' (x_pk hr hh)),
      enterMem_other s c.sp0 (fun h => hy (saved_S h)), hm]

/-! ## The released claims -/

section
variable (C : ∀ b, Callees b)
include C

theorem pubkey_correct : Ed25519.Pubkey.Correct := fun b c s hp => by
  letI := b.codeBytes
  exact call_returns c.toCall (pubkey_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.ret.pc, h⟩) (fun _ hy => wr_cases hy) (pubkey_reach b (C b) hp)

theorem pubkey_reads : Ed25519.Pubkey.Reads := fun b c s hp => by
  letI := b.codeBytes
  exact call_reads c.toCall (pubkey_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.ret.pc) (fun _ hy => rd_cases hy) (pubkey_reach b (C b) hp)

theorem pubkey_stack : Ed25519.Pubkey.Stack := fun b c s hp => by
  letI := b.codeBytes
  exact call_stack c.toCall (pubkey_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.ret.pc, h.ret.sp⟩) (pubkey_reach b (C b) hp)

theorem pubkey_ct : Ed25519.Pubkey.ConstantTime := by
  intro b c₁ c₂ s₁ s₂ h₁ h₂ hpub
  letI := b.codeBytes
  simp only [Ed25519.Pubkey.Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hpk, hseed⟩ := hpub
  have hctx : pubkeyCtx c₁ = pubkeyCtx c₂ := by simp only [pubkeyCtx, hb, hsp, hpk, hseed]
  have hret : c₁.ret = c₂.ret := by simp only [Call.ret, hlr]
  have k₁ := pubkey_codeOk h₁.valid; have k₂ := pubkey_codeOk h₂.valid
  have r₁ := pubkey_reach b (C b) h₁; have r₂ := pubkey_reach b (C b) h₂
  have hc₁ : CodeAt s₁.mem c₁.base b.bytes := h₁.entry.call.mem ▸ h₁.valid.call.code
  rw [hctx, hsp, hb] at r₁; rw [hsp, hb, hret] at k₁; rw [hb] at hc₁; rw [hret]
  exact traceEq_of entryTr_uniq k₁.pc_ne k₁.wc k₂.pc_ne k₂.wc hc₁ (h₂.entry.call.mem ▸ h₂.valid.call.code)
    (fun _ h => h.ret.pc.trans hret) (fun _ h => h.ret.pc) r₁ r₂

/-- Every long enough run of a valid call keeps the stack discipline, and each of its states
before the return is at an instruction of the build. -/
theorem pubkey_run {b : Build} {c : Ed25519.Pubkey.Ctx} {s : State} (hp : Ed25519.Pubkey.Pre b c s) :
    ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 Ed25519.Pubkey.stackBytes states tr ∧
      ∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ c.ret → Interrupt.CodePos c.base b.bytes u := by
  letI := b.codeBytes
  have k := pubkey_codeOk hp.valid
  obtain ⟨n, t, tr, hQ, hΦ, -, -, h2, -⟩ := claims_of k.pc_ne k.wc (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.ret.pc) (pubkey_reach b (C b) hp)
  have hg := entry_good (pubkey_geoOk hp.valid) rfl (pubkey_geo.1 ▸ hp.valid.call.spLo) (C b).ef
    (fun y ⟨r, hr, hh⟩ hb => by
      rw [List.mem_singleton.mp hr] at hh; rw [pubkey_geo.1] at hb
      exact disj_not hp.valid.call.codeS (rgn_region hh (size_lt b)) hb)
    pubkeyProg pubkey_entryOk pubkey_fin.1 rfl rfl (by decide +kernel) (pubkey_bok b) rfl tr hΦ
  rw [pubkey_geo.1] at hg
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, hs, hall⟩ := h2 fuel hf
  refine ⟨states, tr, hs, discipline_of hs (by rw [hp.entry.call.regs]; exact hp.entry.call.sp) hg,
    fun i u hu hne => ?_⟩
  rcases hall u (List.mem_of_getElem? hu) with h | rfl
  · exact h.2
  · exact absurd hQ.ret.pc hne

theorem pubkey_discipline : Ed25519.Pubkey.StackDiscipline := fun _ _ _ hp => by
  obtain ⟨m, hm⟩ := pubkey_run C hp
  exact ⟨m, fun fuel hf => let ⟨st, tr, h1, h2, _⟩ := hm fuel hf; ⟨st, tr, h1, h2⟩⟩

theorem pubkey_interrupted : Ed25519.Pubkey.Interrupted := fun K b c s hp => by
  letI := b.codeBytes
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (pubkey_reads C b c s hp) (pubkey_stack C b c s hp)
    (pubkey_run C hp)
  · rw [b.codeBytes.len] at hy
    exact ⟨.inr (.inl hy), fun hb => disj_not hp.valid.call.codeS hy hb⟩
  · obtain ⟨n, hn⟩ := pubkey_correct C b c s hp
    exact ⟨n, fun fuel hf => let ⟨t, tr, ht, hr, _⟩ := hn fuel hf; ⟨t, tr, ht, hr⟩⟩

end

end M0Crypto.Release.Ed25519PubkeyProg
