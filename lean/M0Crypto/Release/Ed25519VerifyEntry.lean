import M0Crypto.Release.Ed25519VerifyRun
import M0Crypto.Release.Ed25519CallProgCall
import M0Crypto.Release.Ed25519CallProgEntryP
import M0Crypto.Release.Ed25519VerifyTie
import M0Crypto.Release.Ed25519VerifyCongr

/-!
# `m0c_ed25519_verify`'s call

The body's context of a call (`verifyCtx`: `sig`, `m`, `pk` and the code's `L` at `ed_l9`), its
footprints, and the geometry's facts (`verify_geoOk`, `verify_caller`, `verify_codeOk`).
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build Call)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_verify ed_l9)
open M0Crypto.Release.RoutinePieces
open M0Crypto.Spec.Ed25519 (decodeInt L)

/-- The body's context: `sp` below the saved words, the buffers `sig`, `m`, `pk` and the code's
`L`, and `n`. -/
def verifyCtx (c : Ed25519.Verify.Ctx) : Ctx :=
  ⟨c.base, c.sp0 - 36#32, fun i => [c.sig, c.msg, c.pk, c.base + BitVec.ofNat 32 ed_l9].getD i 0, fun _ => c.len⟩

def verifyWc (c : Ed25519.Verify.Ctx) : List Rgn := [verifyGeo.win (verifyCtx c)]

def verifyRc (b : Build) (c : Ed25519.Verify.Ctx) : List Rgn :=
  [⟨c.base, b.size⟩, verifyGeo.win (verifyCtx c), ⟨c.sig, 64⟩, ⟨c.msg, c.len.toNat⟩, ⟨c.pk, 32⟩]

theorem verify_geo : 36 + verifyGeo.N = Ed25519.Verify.stackBytes ∧ verifyGeo.top ≤ verifyGeo.N ∧
    verifyGeo.top % 4 = 0 := by decide +kernel

theorem vcall_cs (b : Build) : rangesSub verifyGeo.cs [(0, b.size)] = true ∧ b.verifyAt = ed25519_verify ∧
    ed_l9 + 32 ≤ b.size ∧ ed_l9 % 4 = 0 := by
  cases b <;> decide +kernel

/-! ## The call's regions -/

section
variable {b : Build} {c : Ed25519.Verify.Ctx}

theorem win_eq (c : Ed25519.Verify.Ctx) : verifyGeo.win (verifyCtx c) = ⟨c.fp, verifyGeo.N⟩ := by
  simp only [Geo.win, verifyCtx, Ed25519.Verify.Ctx.fp, Call.fp]; rw [ad_sub36, verify_geo.1]

theorem saved_S {y : Word} (h : Region (c.sp0 - 36#32) 36 y) : Region c.fp Ed25519.Verify.stackBytes y := by
  have := saved_in_all (N := verifyGeo.N) h; rwa [verify_geo.1] at this

theorem win_S {y : Word} (h : (verifyGeo.win (verifyCtx c)).Has y) : Region c.fp Ed25519.Verify.stackBytes y := by
  rw [win_eq] at h
  have hS := verify_geo.1; have : Ed25519.Verify.stackBytes < 2 ^ 32 := by decide
  have := rgn_region h (by omega)
  simp only [Region] at this ⊢; omega

theorem wr_cases {y : Word} (h : Has (savedR c.sp0 :: verifyWc c) y) : Ed25519.Verify.WrOk c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [verifyWc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact saved_S (rgn_region hy (by decide))
  · exact win_S hy

theorem rd_cases {y : Word} (h : Has (savedR c.sp0 :: verifyRc b c) y) : Ed25519.Verify.ReadRegion b c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [verifyRc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr (.inr (.inr (saved_S (rgn_region hy (by decide))))))
  · exact .inr (.inr (.inr (.inl (rgn_region hy (size_lt b)))))
  · exact .inr (.inr (.inr (.inr (win_S hy))))
  · exact .inl (rgn_region hy (by decide))
  · exact .inr (.inl (rgn_region hy c.len.isLt))
  · exact .inr (.inr (.inl (rgn_region hy (by decide))))

/-- The saved words lie apart from a buffer apart from the stack window. -/
theorem off_saved {a : Word} {n : Nat} (hd : Frame.Disj a n c.fp Ed25519.Verify.stackBytes) :
    ∀ j < n, ¬ Region (c.sp0 - 36#32) 36 (a + BitVec.ofNat 32 j) := fun _ hj hy =>
  disj_not hd (region_off hd.1 hj) (saved_S hy)

theorem l9_nat (hv : Ed25519.Verify.Valid b c) : (c.base + BitVec.ofNat 32 ed_l9).toNat = c.base.toNat + ed_l9 := by
  have h1 := hv.call.codeS.1; have h2 := (vcall_cs b).2.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ed_l9) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The message length is below its parameter bound. -/
theorem verify_pm (hv : Ed25519.Verify.Valid b c) :
    ∀ i x, verifyGeo.pm[i]? = some x → ((verifyCtx c).prm i).toNat ≤ x := fun i x hx => by
  rcases i with _ | i <;> simp only [verifyGeo, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.some.injEq, reduceCtorEq] at hx
  subst hx; have := hv.lenLt; simp only [verifyCtx]; omega

theorem verify_geoOk (hv : Ed25519.Verify.Valid b c) : GeoOk (verifyCtx c) verifyGeo (verifyWc c) (verifyRc b c) := by
  have hS := verify_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hw : (verifyCtx c).sp0 - BitVec.ofNat 32 verifyGeo.N = c.fp := congrArg Rgn.a (win_eq c)
  have hwb : (verifyGeo.win (verifyCtx c)).a.toNat + (verifyGeo.win (verifyCtx c)).n ≤ 2 ^ 32 := by
    rw [win_eq]; dsimp only
    have : Ed25519.Verify.stackBytes < 2 ^ 32 := by decide
    simp only [Ed25519.Verify.Ctx.fp, Call.fp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hxs : verifyGeo.xs = [⟨.k 64, false, true, false⟩, ⟨.p 0, false, true, false⟩,
      ⟨.k 32, false, true, false⟩, ⟨.k 32, false, true, true⟩] := rfl
  have hl9 := l9_nat hv; have hcd := hv.call.codeS
  obtain ⟨-, -, h9, h94⟩ := vcall_cs b
  have hsp : ((verifyCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [verifyCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨by omega, by omega, verify_geo.2.1, verify_geo.2.2, sub_one (by simp [verifyWc]) hwb,
    sub_one (by simp [verifyRc]) hwb, fun i x hx => ?_, verify_pm hv, fun i s h => ?_, fun i s h x hx => ?_⟩
  · rw [hxs] at hx
    rcases i with _ | _ | _ | _ | i <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hx <;> subst hx
    · refine ⟨.inr ?_, fun h => absurd h (by decide),
        fun _ => sub_one (by simp [verifyRc, XLen.v, verifyCtx]) hv.sigS.1, fun h => absurd h (by decide)⟩
      rw [hw]; exact Disj.shrink hv.sigS (by omega)
    · refine ⟨?_, fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide)⟩
      · rcases hv.msgS with h | h
        · exact .inl (by simp [XLen.v, verifyCtx, h])
        · exact .inr (by rw [hw]; exact Disj.shrink h (by omega))
      · unfold XInfo.rgns; split
        · intro r hr; cases hr
        · rename_i h0
          have hd := hv.msgS.resolve_left fun e => h0 (by simp [XLen.v, verifyCtx, e])
          exact sub_one (by simp [verifyRc, XLen.v, verifyCtx]) hd.1
    · refine ⟨.inr ?_, fun h => absurd h (by decide),
        fun _ => sub_one (by simp [verifyRc, XLen.v, verifyCtx]) hv.pkS.1, fun h => absurd h (by decide)⟩
      rw [hw]; exact Disj.shrink hv.pkS (by omega)
    · refine ⟨.inr ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_⟩
      · rw [hw]
        obtain ⟨d1, d2, d3⟩ := Disj.shrink hcd (show verifyGeo.N ≤ Ed25519.Verify.stackBytes by omega)
        simp only [XLen.v, verifyCtx, List.getD_cons_succ, List.getD_cons_zero]
        simp only [Ed25519.Verify.Ctx.fp] at d3 ⊢; refine ⟨by omega, d2, ?_⟩; omega
      · intro r hr
        simp only [XInfo.rgns, XLen.v, verifyCtx, List.getD_cons_succ, List.getD_cons_zero,
          show (32 = 0) = False from by decide, ite_false, List.mem_singleton] at hr
        subst hr
        exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega, hcd.1⟩
      · simp only [verifyCtx, List.getD_cons_succ, List.getD_cons_zero]
        have := hv.call.base4; omega
  · simp only [verifyGeo, List.lookup] at h
    split at h
    · rename_i he; simp only [Option.some.injEq] at h; subst h
      simp only [beq_iff_eq] at he; subst he; rfl
    · simp at h
  · simp only [verifyGeo, List.lookup] at h
    split at h
    · rename_i he; simp only [beq_iff_eq] at he; subst he
      rw [hxs] at hx
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
      intro r hr q hq
      simp only [XInfo.rgns, XLen.v, verifyCtx, List.getD_cons_succ, List.getD_cons_zero,
        show (32 = 0) = False from by decide, ite_false, List.mem_singleton] at hr
      simp only [verifyWc, List.mem_singleton] at hq
      subst hr hq
      obtain ⟨d1, d2, d3⟩ := Disj.shrink hcd (show verifyGeo.N ≤ Ed25519.Verify.stackBytes by omega)
      rw [win_eq]; dsimp only
      simp only [Ed25519.Verify.Ctx.fp] at d3 ⊢; refine ⟨by omega, d2, ?_⟩; omega
    · simp at h

theorem verify_caller (hv : Ed25519.Verify.Valid b c) :
    @Caller b.bytes b.size b.codeBytes (verifyCtx c).base (verifyCtx c).sp0 verifyGeo.N (verifyWc c) := by
  have hS := verify_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hsp : ((verifyCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [verifyCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  letI := b.codeBytes
  refine ⟨hv.call.base4, by omega, by omega, fun r hr q hq => ?_, hv.call.codeS.1⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [verifyWc, List.mem_singleton] at hq; subst hq
  rw [win_eq]; exact Disj.shrink hv.call.codeS (by dsimp only; omega)

theorem verify_codeOk (hv : Ed25519.Verify.Valid b c) :
    CodeOk b.size c.base c.ret (PcIn c.base verifyGeo.cs) (Has (savedR c.sp0 :: verifyWc c)) := by
  letI := b.codeBytes
  exact ⟨fun _ hy => pcIn_region (size_lt b) (vcall_cs b).1 hy,
    fun _ hy h => disj_not hv.call.codeS h (wr_cases hy), hv.call.retOut⟩

/-- The saved words lie outside the body's window. -/
theorem saved_not_vwin (hv : Ed25519.Verify.Valid b c) {y : Word} (hy : Region (c.sp0 - 36#32) 36 y) :
    ¬ (verifyGeo.win (verifyCtx c)).Has y := fun hw => by
  have hS := verify_geo.1
  have h := saved_not_win (N := verifyGeo.N) (by rw [hS]; exact hv.call.spLo) hy
  have hw' : (verifyGeo.win (verifyCtx c)).Has y := hw
  simp only [Geo.win, verifyCtx] at hw'
  rw [ad_sub36] at hw'
  exact h (rgn_region hw' (by decide))

end

/-! ## The run -/

theorem verify_pieces (b : Build) :
    seqAt b.bytes ed25519_verify (abiEnter verifyGeo.top) = true ∧
    piecesAt b.bytes (bodyAt verifyGeo ed25519_verify + verifyBodyBytes) (abiLeaveP verifyGeo.top) = true := by
  cases b <;> exact ⟨by rw [seqAt_eq_scan]; decide +kernel, by rw [piecesAt_eq_scan]; decide +kernel⟩

theorem verify_at : bodyAt verifyGeo ed25519_verify = oP0 ∧ bodyAt verifyGeo ed25519_verify + verifyBodyBytes = oLeave := by
  decide +kernel

/-- The trace condition of a call from entry memory `m0`. -/
noncomputable def verifyTr (b : Build) (c : Ed25519.Verify.Ctx) (m0 : Mem) : TrP :=
  letI := b.codeBytes
  entryTrP verifyGeo (verifyCtx c) c.sp0 ed25519_verify verifyBodyBytes ((vAd b).bodyTr (verifyCtx c) m0)

section
variable {b : Build} {c : Ed25519.Verify.Ctx} {s : State}

/-- The build is at `base` in the entry memory. -/
theorem code_enter (hp : Ed25519.Verify.Pre b c s) : CodeAt (enterMem s c.sp0) c.base b.bytes := fun i hi => by
  rw [enterMem_other _ _ (off_saved hp.valid.call.codeS i (b.codeBytes.len ▸ hi))]
  exact (hp.entry.call.mem ▸ hp.valid.call.code) i hi

/-- The body reads `L` from the code. -/
theorem lv_enter (hp : Ed25519.Verify.Pre b c s) : decodeInt (lv (verifyCtx c) (enterMem s c.sp0)) = L := by
  simp only [lv, verifyCtx, List.getD_cons_succ, List.getD_cons_zero, BitVec.add_zero]
  rw [M0Crypto.Release.Ed25519ScReduceProg.code_bytes (code_enter hp)
    (by rw [b.codeBytes.len]; exact (vcall_cs b).2.2.1)]
  exact Ed25519VerifyBlocks.l9_val b

/-- The body's input bytes are the call's. -/
theorem bytes_enter (hp : Ed25519.Verify.Pre b c s) :
    rv (verifyCtx c) (enterMem s c.sp0) ++ sv (verifyCtx c) (enterMem s c.sp0) = c.sigB ∧
    mv (verifyCtx c) (enterMem s c.sp0) = c.msgB ∧ pv (verifyCtx c) (enterMem s c.sp0) = c.pkB := by
  have hm := hp.entry.call.mem; have hv := hp.valid
  refine ⟨?_, ?_, ?_⟩
  · simp only [rv, sv, verifyCtx, List.getD_cons_zero, BitVec.add_zero]
    rw [← bytesAt_split (enterMem s c.sp0) c.sig 32 32, enter_bytes (off_saved hv.sigS), hm]; rfl
  · simp only [mv, verifyCtx, List.getD_cons_succ, List.getD_cons_zero, BitVec.add_zero]
    rcases hv.msgS with h0 | hd
    · simp [h0, bytesAt, Ed25519.Verify.Ctx.msgB, Call.bytes, Frame.Ctx.bytesAt]
    · rw [enter_bytes (off_saved hd), hm]; rfl
  · simp only [pv, verifyCtx, List.getD_cons_succ, List.getD_cons_zero, BitVec.add_zero]
    rw [enter_bytes (off_saved hv.pkS), hm]; rfl

/-- **A valid call of verify returns with its `Result`**, and the callees' premises hold. -/
theorem verify_reach (hp : Ed25519.Verify.Pre b c s) :
    @ReachFT b.bytes b.size b.codeBytes c.base (PcIn c.base verifyGeo.cs) (Has (savedR c.sp0 :: verifyRc b c))
      (Has (savedR c.sp0 :: verifyWc c)) (InStackWindow c.sp0 Ed25519.Verify.stackBytes) s
      (fun u => Ed25519.Verify.Result c u ∧
        @VAd.pubOk vRels b.bytes b.size b.codeBytes (vAd b) (verifyCtx c) (enterMem s c.sp0))
      (verifyTr b c (enterMem s c.sp0)) := by
  letI := b.codeBytes
  obtain ⟨hv, he⟩ := hp
  have hS := verify_geo.1
  have hs := he.call.regs; have hm := he.call.mem
  have hL := lv_enter ⟨hv, he⟩
  obtain ⟨hsig, hmsg, hpk⟩ := bytes_enter ⟨hv, he⟩
  rw [← hS]
  refine entry_runP vRels (st0 := stE) (oE := ed25519_verify) (bsz := verifyBodyBytes)
    (R := fun u => (∀ y, ¬ (verifyGeo.win (verifyCtx c)).Has y → u.mem y = enterMem s c.sp0 y) ∧
      (u.regs 0 = if (vAd b).ok (verifyCtx c) (enterMem s c.sp0) then 0#32 else 0xffffffff#32) ∧
      (vAd b).pubOk (verifyCtx c) (enterMem s c.sp0))
    (verify_caller hv) verify_entryOk (verify_pieces b).1 rfl (by rw [hS]; exact hv.call.spLo)
    (by rw [hs]; exact he.call.sp) (by show s.regs 15 = _; rw [hs, he.call.pc, (vcall_cs b).2.1]; rfl)
    (hm ▸ hv.call.code) (fun i hi => off_saved hv.call.codeS i (b.codeBytes.len ▸ hi)) rfl rfl ?_
    (by rw [hs]; exact hv.call.thumb) ?_ ?_
  · intro p hp
    simp only [stE, verifyσ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inr rfl
      | exact .inl ⟨by decide, by simp [SV.val, verifyCtx, hs, he.r0, he.r1, he.r2, he.r3]⟩
  · intro t hat
    rw [verify_at.1] at hat
    have hpre := body_pre (b := b) hL
    refine ReachT.mono (body_run (vAd b) (verify_geoOk hv) (verify_caller hv)
      (sub_one (by simp [verifyRc, codeR, verifyCtx]) hv.call.codeS.1) (lines_code b) (sites_code b) (lt_code b)
      (xsites_code b) (tail_code b) trivial (fun _ => trivial) (fun _ => hpre.1) (fun _ _ => trivial)
      (fun _ _ => trivial) hpre.2 (fun _ _ => trivial) hat)
      (fun _ _ h => h) (fun u hu => ?_) (fun _ h => h)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hu
    exact ⟨by rw [h1, verify_at.2], h2, (verify_pieces b).2,
      fun y hy => h3 y (saved_not_vwin hv hy), h3, h4, h5⟩
  · intro u1 u hR hpc h13 hr0 hcal _ _ _ hum
    refine ⟨⟨⟨by rw [hpc, hs]; rfl, h13, by rw [hs] at hcal; exact hcal⟩, ?_, fun y hy => ?_⟩, hR.2.2⟩
    · rw [hr0, hR.2.1, ok_eq (b := b) hL, hsig, hmsg, hpk]; rfl
    · rw [hum, hR.1 y (fun hw => hy (win_S hw)), enterMem_other s c.sp0 (fun h => hy (saved_S h)), hm]

end

end M0Crypto.Release.Ed25519VerifyProg
