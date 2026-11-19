import M0Crypto.Release.Ed25519SignBlocks
import M0Crypto.Release.Ed25519CallProgCall
import M0Crypto.Release.Ed25519CallProgReport
import M0Crypto.Release.Ed25519CallProgEffect

/-!
# `m0c_ed25519_sign` from its program

The callees' semantics (`semE`) and their adapters as one named hypothesis per build
(`Callees`): SHA-512 init, update and final over a context relation, `sc_reduce`, `ge_mul_base`
and `ge_compress` over a point relation, and `sc_muladd`. The program's values at `sig` are
`progSig` of the entry bytes (`sign_ev`, by evaluation), which is RFC 8032's signature
(`progSig_spec`). `sign_reach` runs the entry from a valid call to `Result`; the released claim
forms follow from it.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519 (Build Call)
open M0Crypto.Release.Ed25519Bytes (clampNat)
open M0Crypto.Spec.Ed25519 (Byte encodeInt decodeInt encodePoint scalarMul L)
open M0Crypto.Spec.Sha512 (sha512)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_sign)

/-! ## The callees -/

/-- The callees' semantics on their views. -/
def semE : EA → List V → List V
  | .init, _ => [.c []]
  | .update _ _, [.c M, .b d] => [.c (M ++ d)]
  | .final _, [.c M] => [.b (sha512 M)]
  | .reduce, [.b h] => [.b (encodeInt (decodeInt h % L))]
  | .mulBase, [.b k] => [.p (scalarMul (decodeInt k) Spec.Ed25519.B)]
  | .compress, [.p P] => [.b (encodePoint P)]
  | .muladd, [.b k, .b s, .b r] => [.b (encodeInt ((decodeInt k * decodeInt s + decodeInt r) % L))]
  | _, _ => [.none]

/-- **The callee adapters of build `b`**: one relation pair, and each callee's adapter with its
semantics and the byte effect of its trace. -/
structure Callees (b : Build) where
  Rs : Rels
  ad : ∀ a, @Ad Rs b.bytes b.size b.codeBytes (eaS a)
  sem : ∀ a, @Ad.sem Rs b.bytes b.size b.codeBytes _ (ad a) = semE a
  ef : ∀ a base p, @CalleeS.Eff (eaS a) p b.bytes b.size b.codeBytes base
    (@Ad.T Rs b.bytes b.size b.codeBytes _ (ad a) base p)

/-! ## The values at `sig` -/

/-- What the program leaves at `sig`, from the seed, the caller's public key and the message. -/
def progSig (seed pk msg : List Byte) : List Byte × List Byte :=
  let hs := sha512 ([] ++ seed)
  let rr := encodeInt (decodeInt (sha512 ([] ++ (((hs.drop 32).take 32).drop 0).take 32 ++ msg)) % L)
  let R := encodePoint (scalarMul (decodeInt rr) Spec.Ed25519.B)
  let kk := encodeInt (decodeInt (sha512 ([] ++ R ++ pk ++ msg)) % L)
  (R, encodeInt ((decodeInt kk * decodeInt (clampSc ((hs.drop 0).take 32)) + decodeInt rr) % L))

/-- What the program leaves at `sig` from the entry memory `m0`. -/
abbrev signP (c : Ctx) (m0 : Mem) : List Byte × List Byte :=
  progSig (bytesAt m0 (c.ptr 2 + BitVec.ofNat 32 0) 32) (bytesAt m0 (c.ptr 2 + BitVec.ofNat 32 32) 32)
    (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) (c.prm 0).toNat)

theorem sign_ev (c : Ctx) (m0 : Mem) :
    Prog.ev eaS ebS signGeo semE semB c m0 signProg signSt (fun _ => .none) (.ex 0 0) = .b (signP c m0).1 ∧
    Prog.ev eaS ebS signGeo semE semB c m0 signProg signSt (fun _ => .none) (.ex 0 32) = .b (signP c m0).2 :=
  ⟨rfl, rfl⟩

theorem mod_L_lt (x : Nat) : x % L < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)

theorem mod_L (r k s : Nat) : (r % L + k % L * s) % L = (r + k * s) % L := by
  rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- **The program's signature is RFC 8032's** (section 5.1.6, with the caller's public key). -/
theorem progSig_spec (seed pk msg : List Byte) :
    (progSig seed pk msg).1 ++ (progSig seed pk msg).2 = Spec.Ed25519.signWith seed pk msg := by
  have hl := sha512_length seed
  have hc : Spec.Ed25519.secretScalar (sha512 seed) < 2 ^ 256 := by
    rw [Ed25519Bytes.secretScalar_eq _ (by omega)]; unfold clampNat
    have := Nat.mod_lt (decodeInt ((sha512 seed).take 32)) (Nat.two_pow_pos 254); omega
  simp only [progSig, Spec.Ed25519.signWith, List.nil_append, clampSc, List.drop_zero,
    List.take_of_length_le (by simp [hl] : ((sha512 seed).drop 32).length ≤ 32), decodeInt_encodeInt,
    Nat.mod_eq_of_lt (mod_L_lt _), ← Ed25519Bytes.secretScalar_eq _ (by omega : 32 ≤ (sha512 seed).length),
    Nat.mod_eq_of_lt hc]
  rw [Nat.add_comm, mod_L]

/-! ## The entry -/

/-- The body's context: `sp` below the saved words, the buffers `sig`, `m`, `sk`, and `n`. -/
def signCtx (c : Ed25519.Sign.Ctx) : Ctx :=
  ⟨c.base, c.sp0 - 36#32, fun i => [c.sig, c.msg, c.sk].getD i 0, fun _ => c.len⟩

def signWc (c : Ed25519.Sign.Ctx) : List Rgn := [signGeo.win (signCtx c), ⟨c.sig, 64⟩]

def signRc (b : Build) (c : Ed25519.Sign.Ctx) : List Rgn :=
  [⟨c.base, b.size⟩, signGeo.win (signCtx c), ⟨c.sk, 64⟩, ⟨c.msg, c.len.toNat⟩]

/-- The final static state. -/
def signFin : St := (signProg.ty eaS ebS signGeo signSt).getD signSt

theorem sign_fin : signProg.ty eaS ebS signGeo signSt = some signFin ∧
    signFin.X = [⟨.ex 0 0, .k 32⟩, ⟨.ex 0 32, .k 32⟩] ∧
    (Loc.ex 0 0, Kd.bytes 32) ∈ signFin.Γ ∧ (Loc.ex 0 32, Kd.bytes 32) ∈ signFin.Γ := by
  decide +kernel

theorem sign_entryOk : entryOk eaS ebS signGeo signProg ed25519_sign = true := by decide +kernel

theorem sign_geo : 36 + signGeo.N = Ed25519.Sign.stackBytes ∧ signGeo.top ≤ signGeo.N ∧ signGeo.top % 4 = 0 :=
  by decide +kernel

theorem sign_cs (b : Build) : rangesSub signGeo.cs [(0, b.size)] = true ∧ b.signAt = ed25519_sign := by
  cases b <;> decide +kernel

/-! ## The call's regions -/

section
variable (b : Build) (c : Ed25519.Sign.Ctx)

theorem size_lt : b.size < 2 ^ 32 := by cases b <;> decide

theorem win_eq : signGeo.win (signCtx c) = ⟨c.fp, signGeo.N⟩ := by
  simp only [Geo.win, signCtx, Ed25519.Sign.Ctx.fp, Call.fp]; rw [ad_sub36, sign_geo.1]

variable {b c}

theorem saved_S {y : Word} (h : Region (c.sp0 - 36#32) 36 y) : Region c.fp Ed25519.Sign.stackBytes y := by
  have := saved_in_all (N := signGeo.N) h; rwa [sign_geo.1] at this

theorem win_S {y : Word} (h : (signGeo.win (signCtx c)).Has y) : Region c.fp Ed25519.Sign.stackBytes y := by
  rw [win_eq] at h
  have hS := sign_geo.1; have : Ed25519.Sign.stackBytes < 2 ^ 32 := by decide
  have := rgn_region h (by omega)
  simp only [Region] at this ⊢; omega

theorem x_sig {r : SR} {y : Word} (hr : r ∈ signFin.X) (h : Has (r.rgns signGeo (signCtx c)) y) :
    Region c.sig 64 y := by
  rw [sign_fin.2.1] at hr
  obtain ⟨q, hq, hy⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
  · simp only [SR.rgns, XLen.v, Loc.addr, signCtx, List.getD_cons_zero, List.mem_ite_nil_left,
      List.mem_singleton] at hq
    obtain ⟨-, rfl⟩ := hq; exact half_in hy (by omega) (by decide)

theorem wr_cases {y : Word} (h : Has (savedR c.sp0 :: signWc c) y) : Ed25519.Sign.WrOk c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [signWc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact .inl (saved_S (rgn_region hy (by decide)))
  · exact .inl (win_S hy)
  · exact .inr (rgn_region hy (by decide))

theorem rd_cases {y : Word} (h : Has (savedR c.sp0 :: signRc b c) y) : Ed25519.Sign.ReadRegion b c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [signRc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr (.inr (saved_S (rgn_region hy (by decide)))))
  · exact .inr (.inr (.inl (rgn_region hy (size_lt b))))
  · exact .inr (.inr (.inr (win_S hy)))
  · exact .inl (rgn_region hy (by decide))
  · exact .inr (.inl (rgn_region hy c.len.isLt))

/-- The saved words lie apart from a buffer apart from the stack window. -/
theorem off_saved {a : Word} {n : Nat} (hd : Frame.Disj a n c.fp Ed25519.Sign.stackBytes) :
    ∀ j < n, ¬ Region (c.sp0 - 36#32) 36 (a + BitVec.ofNat 32 j) := fun _ hj hy =>
  disj_not hd (region_off hd.1 hj) (saved_S hy)

/-- The message length is below its parameter bound. -/
theorem sign_pm (hv : Ed25519.Sign.Valid b c) :
    ∀ i x, signGeo.pm[i]? = some x → ((signCtx c).prm i).toNat ≤ x := fun i x hx => by
  rcases i with _ | i <;> simp only [signGeo, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.some.injEq, reduceCtorEq] at hx
  subst hx; have := hv.lenLt; simp only [signCtx]; omega

theorem sign_geoOk (hv : Ed25519.Sign.Valid b c) : GeoOk (signCtx c) signGeo (signWc c) (signRc b c) := by
  have hS := sign_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hw : (signCtx c).sp0 - BitVec.ofNat 32 signGeo.N = c.fp := congrArg Rgn.a (win_eq c)
  have hwb : (signGeo.win (signCtx c)).a.toNat + (signGeo.win (signCtx c)).n ≤ 2 ^ 32 := by
    rw [win_eq]; dsimp only
    have : Ed25519.Sign.stackBytes < 2 ^ 32 := by decide
    simp only [Ed25519.Sign.Ctx.fp, Call.fp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsp : ((signCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [signCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hxs : signGeo.xs = [⟨.k 64, true, false, false⟩, ⟨.p 0, false, true, false⟩,
      ⟨.k 64, false, true, false⟩] := rfl
  refine ⟨by omega, by omega, sign_geo.2.1, sign_geo.2.2, sub_one (by simp [signWc]) hwb,
    sub_one (by simp [signRc]) hwb, fun i x hx => ?_, sign_pm hv, fun _ _ h => by simp [signGeo] at h,
    fun _ _ h => by simp [signGeo] at h⟩
  rw [hxs] at hx
  rcases i with _ | _ | _ | i <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hx <;> subst hx
  · refine ⟨.inr ?_, fun _ => sub_one (by simp [signWc, XLen.v, signCtx]) hv.sigS.1,
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [hw]; exact Disj.shrink hv.sigS (by omega)
  · refine ⟨?_, fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide)⟩
    · rcases hv.msgS with h | h
      · exact .inl (by simp [XLen.v, signCtx, h])
      · exact .inr (by rw [hw]; exact Disj.shrink h (by omega))
    · unfold XInfo.rgns; split
      · intro r hr; cases hr
      · rename_i h0
        have hd := hv.msgS.resolve_left fun e => h0 (by simp [XLen.v, signCtx, e])
        exact sub_one (by simp [signRc, XLen.v, signCtx]) hd.1
  · refine ⟨.inr ?_, fun h => absurd h (by decide),
      fun _ => sub_one (by simp [signRc, XLen.v, signCtx]) hv.skS.1, fun h => absurd h (by decide)⟩
    rw [hw]; exact Disj.shrink hv.skS (by omega)

theorem sign_caller (hv : Ed25519.Sign.Valid b c) :
    @Caller b.bytes b.size b.codeBytes (signCtx c).base (signCtx c).sp0 signGeo.N (signWc c) := by
  have hS := sign_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hsp : ((signCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [signCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  letI := b.codeBytes
  refine ⟨hv.call.base4, by omega, by omega, fun r hr q hq => ?_, hv.codeO.1⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [signWc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · rw [win_eq]; exact Disj.shrink hv.call.codeS (by dsimp only; omega)
  · exact hv.codeO

theorem sign_codeOk (hv : Ed25519.Sign.Valid b c) :
    CodeOk b.size c.base c.ret (PcIn c.base signGeo.cs) (Has (savedR c.sp0 :: signWc c)) := by
  letI := b.codeBytes
  exact ⟨fun _ hy => pcIn_region (size_lt b) (sign_cs b).1 hy,
    fun _ hy h => (wr_cases hy).elim (disj_not hv.call.codeS h) (disj_not hv.codeO h), hv.call.retOut⟩

end

/-! ## The run -/

/-- The trace condition of a call with body context `c` and entry SP `sp0`. -/
def signTr {b : Build} (C : Callees b) (c : Ctx) (sp0 : Word) : TrP :=
  entryTr eaS ebS signGeo (fun a =>
    @Ad.T C.Rs b.bytes b.size b.codeBytes _ (C.ad a)) c sp0
    ed25519_sign signProg signSt

/-- **A valid call of sign returns with its `Result`**, given the callee adapters. -/
theorem sign_reach (b : Build) (C : Callees b) {c : Ed25519.Sign.Ctx} {s : State} (hp : Ed25519.Sign.Pre b c s) :
    @ReachFT b.bytes b.size b.codeBytes c.base (PcIn c.base signGeo.cs) (Has (savedR c.sp0 :: signRc b c))
      (Has (savedR c.sp0 :: signWc c)) (InStackWindow c.sp0 Ed25519.Sign.stackBytes) s (Ed25519.Sign.Result c) (signTr C (signCtx c) c.sp0) := by
  obtain ⟨hv, he⟩ := hp
  have hS := sign_geo.1
  have hs := he.call.regs; have hm := he.call.mem
  rw [← hS]
  refine @entry_run C.Rs b.bytes b.size b.codeBytes _ _ eaS ebS C.ad (bdS C.Rs) (signCtx c) signGeo (signWc c)
    (signRc b c) (sign_geoOk hv) (sign_caller hv) (sub_one (by simp [signRc, codeR, signCtx]) hv.codeO.1) signProg
    signSt signFin ed25519_sign s c.sp0 _ sign_entryOk sign_fin.1 rfl rfl (sign_bok b) (sign_pieces b).1
    (sign_pieces b).2 rfl (by rw [hS]; exact hv.call.spLo) (by rw [hs]; exact he.call.sp)
    (by show s.regs 15 = _; rw [hs, he.call.pc, (sign_cs b).2]; rfl) (hm ▸ hv.call.code)
    (fun i hi => off_saved hv.call.codeS i (b.codeBytes.len ▸ hi)) rfl rfl ?_
    (fun y hy r hr hh => disj_not hv.sigS (x_sig hr hh) (saved_S hy)) (by rw [hs]; exact hv.call.thumb) ?_
  · intro p hp
    simp only [signSt, signσ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inr rfl
      | exact .inl ⟨by decide, by simp [SV.val, signCtx, hs, he.r0, he.r1, he.r2, he.r3]⟩
  · intro mb u hI hpc h13 hcal h1 h2 h3 h12 hsv hz hout
    have hE : (fun a => @Ad.sem C.Rs b.bytes b.size b.codeBytes _ (C.ad a)) = semE := funext C.sem
    have hB : (fun b => (bdS C.Rs b).sem) = semB := funext fun b => by cases b <;> rfl
    rw [hE, hB] at hI
    have ev := sign_ev (signCtx c) (enterMem s c.sp0)
    have r0 := (hI.1 _ sign_fin.2.2.1).2; have r1 := (hI.1 _ sign_fin.2.2.2).2
    dsimp only at r0 r1; rw [ev.1] at r0; rw [ev.2] at r1
    simp only [Rel, Loc.addr, signCtx, List.getD_cons_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] at r0 r1
    have hb : ∀ {a : Word} {n : Nat}, Frame.Disj a n c.fp Ed25519.Sign.stackBytes → ∀ {m}, m ≤ n →
        bytesAt (enterMem s c.sp0) a m = c.bytes a m := fun hd _ hmn => by
      rw [enter_bytes fun j hj => off_saved hd j (by omega), hm]; rfl
    have hpk : bytesAt (enterMem s c.sp0) (c.sk + 32#32) 32 = c.pkB := by
      rw [enter_bytes fun j hj => by rw [Thumb.ofNat_add_assoc]; exact off_saved hv.skS _ (by omega), hm]; rfl
    have hmsg : bytesAt (enterMem s c.sp0) c.msg c.len.toNat = c.msgB := by
      rcases hv.msgS with h0 | hd
      · simp [h0, bytesAt, Ed25519.Sign.Ctx.msgB, Call.bytes, Frame.Ctx.bytesAt]
      · exact hb hd (Nat.le_refl _)
    have hsig : bytesAt mb c.sig 64 = c.sigOut := by
      rw [show 64 = 32 + 32 from rfl, bytesAt_split, r0, r1, progSig_spec]
      simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero]
      rw [hb hv.skS (by decide), hpk, hmsg]; rfl
    have hres := call_result c.toCall hs hpc h13 hcal h1 h2 h3 h12 hsv hz
    rw [hS] at hres
    refine ⟨hres.1, hres.2, memOut_of c.toCall (fun y hy => hout y (by rw [hS]; exact hy))
      (fun i hi => byte_of hsig hi) fun y hy hy' => ?_⟩
    rw [hI.2.1 y (fun h => hy (win_S h)) (fun r hr hh => hy' (x_sig hr hh)),
      enterMem_other s c.sp0 (fun h => hy (saved_S h)), hm]

/-! ## The released claims -/

section
variable (C : ∀ b, Callees b)
include C

theorem sign_correct : Ed25519.Sign.Correct := fun b c s hp => by
  letI := b.codeBytes
  exact call_returns c.toCall (sign_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.ret.pc, h⟩) (fun _ hy => wr_cases hy) (sign_reach b (C b) hp)

theorem sign_reads : Ed25519.Sign.Reads := fun b c s hp => by
  letI := b.codeBytes
  exact call_reads c.toCall (sign_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => h.ret.pc) (fun _ hy => rd_cases hy) (sign_reach b (C b) hp)

theorem sign_stack : Ed25519.Sign.Stack := fun b c s hp => by
  letI := b.codeBytes
  exact call_stack c.toCall (sign_codeOk hp.valid) (hp.entry.call.mem ▸ hp.valid.call.code)
    (fun _ h => ⟨h.ret.pc, h.ret.sp⟩) (sign_reach b (C b) hp)

theorem sign_ct : Ed25519.Sign.ConstantTime := by
  intro b c₁ c₂ s₁ s₂ h₁ h₂ hpub
  letI := b.codeBytes
  simp only [Ed25519.Sign.Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hsig, hmsg, hlen, hsk⟩ := hpub
  have hctx : signCtx c₁ = signCtx c₂ := by simp only [signCtx, hb, hsp, hsig, hmsg, hlen, hsk]
  have hret : c₁.ret = c₂.ret := by simp only [Call.ret, hlr]
  have k₁ := sign_codeOk h₁.valid; have k₂ := sign_codeOk h₂.valid
  have r₁ := sign_reach b (C b) h₁; have r₂ := sign_reach b (C b) h₂
  have hc₁ : CodeAt s₁.mem c₁.base b.bytes := h₁.entry.call.mem ▸ h₁.valid.call.code
  rw [hctx, hsp, hb] at r₁; rw [hsp, hb, hret] at k₁; rw [hb] at hc₁; rw [hret]
  exact traceEq_of entryTr_uniq k₁.pc_ne k₁.wc k₂.pc_ne k₂.wc hc₁ (h₂.entry.call.mem ▸ h₂.valid.call.code)
    (fun _ h => h.ret.pc.trans hret) (fun _ h => h.ret.pc) r₁ r₂

theorem sign_correctRfc : Ed25519.Sign.CorrectRfc := fun b c s hp hpk => by
  obtain ⟨n, hn⟩ := sign_correct C b c s hp
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, h1, h2, h3⟩ := hn fuel hf
  refine ⟨t, tr, h1, ⟨h2, ?_⟩, h3⟩
  rw [memOut_bytes h2.mem hp.valid.sigS (by rw [Ed25519.Sign.Ctx.sigOut, ← progSig_spec]; simp [progSig,
    encodeInt_length, encodePoint_length]), Ed25519.Sign.Ctx.sigOut, hpk]; rfl

end

end M0Crypto.Release.Ed25519CallProg
