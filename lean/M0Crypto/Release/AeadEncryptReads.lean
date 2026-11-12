import M0Crypto.Release.AeadReadsPhases
import M0Crypto.Release.AeadLengthsReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Checked encryption under the read policy

`encrypt_reach_r`: the run of `encrypt_reach_w`, with the step condition "a load at a read site
reads only bytes of `Rd`".
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (PCBetween)
open M0Crypto.Spec.Aead (pad16 macData chacha20)

theorem encrypt_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) s (EncryptResult c) := by
  have hn : ∀ pc, NoSite c.base pc → ¬ SiteRd c.base pc := fun _ h => h
  have hblk := rd_blk c hsub
  obtain ⟨spro, blx, scopy, bli, scrypt, blc, laad, maat, lout, mcat, slen, bll, sf, blf,
    sca, scl, bcl, sepi, pop⟩ := enc_at
  obtain ⟨tx, ti', tc, tl, tf⟩ := enc_calls
  apply ReachS.bind
  apply (aead_setup_r (Rd := Rd) c hv encOff (blImm (encOff + proXorOff) xorOff) (blImm (encOff + initCallOff) initOff)
    spro blx tx scopy bli ti' (by decide) (by decide) s he (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide)) (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide))
    (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) hsub).mono (fun _ _ h => h)
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  apply ReachS.bind
  apply (crypt_reach_r (Rd := Rd) c hv hb encCryptAt (blImm (encCryptAt + cryptXorOff) xorOff) scrypt blc tc (by decide) (by decide)
    u hu.pc hu.sp hu.high hu.nonce hu.out
    (fun j hj => not_siteRd (by have := (by decide : encCryptAt + seqSize crypt < 2 ^ 32); omega)
      (no_readSite (by decide +kernel : firstReadSite encCryptAt (seqSize crypt) = none) j hj))
    (pt_ns (by decide +kernel) (by decide))
    (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) hsub).mono (fun _ _ h => h)
  intro v hv'
  have bv := bu.crypt hv hb hv'
  have pv : PInv c.A u.mem [] v.mem := pi.congr (fun j hj => by
    simpa only [ofNat_add_assoc] using hv'.atA hv hb (8+j) (by omega) (.inr (by omega)))
  have aadV : Ctx.bytesAt v.mem c.aad c.alen.toNat = c.aadB := by
    apply bytesAt_congr
    intro j hj
    rw [hv'.keep (c.aad+BitVec.ofNat 32 j) (fun o ho e => (hv.not_swr hb.aadS hj) (e ▸ swr_lo c.A o ho))
      (fun o ho e => (hv.not_swr hb.aadS hj) (e ▸ swr_A c.A (4+o) (by omega))) (not_out hb.aadO hj),
      bu.frame _ (hv.not_swr hb.aadS hj)]
  apply ReachS.bind
  apply (mac_phase_r (Rd := Rd) c hv (AWr c) encLoadAadAt loadAad 0x24 0x25 rfl laad _ _ maat (by decide) (by decide)
    v hv'.pc c.aad c.alen hb.aadS bv.high.aad bv.high.alen bv u.mem [] pv
    (fun y h => .inl (macWr_swr _ y h))
    (region_ns (by decide +kernel) (by decide)) (macFree_of_first (by decide +kernel))
    (fun o ho => hsub _ (.aad ho rfl)) hblk).mono (fun _ _ h => h)
  intro w hw
  have pw : PInv c.A u.mem (c.aadB ++ pad16 c.aadB) w.mem := by
    have h := hw.inv; rw [aadV, List.nil_append] at h; exact h
  have ctW : Ctx.bytesAt w.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB := by
    rw [← hv'.out]
    exact bytesAt_congr (fun j hj => hw.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply (mac_phase_r (Rd := Rd) c hv (AWr c) encLoadOutAt loadOut 0x1a 0x1d rfl lout _ _ mcat (by decide) (by decide)
    w hw.pc c.out c.len hb.outStack hw.body.high.out hw.body.high.len hw.body
    u.mem _ pw (fun y h => .inl (macWr_swr _ y h))
    (region_ns (by decide +kernel) (by decide)) (macFree_of_first (by decide +kernel))
    (fun o ho => hsub _ (.out ho rfl)) hblk).mono (fun _ _ h => h)
  intro x hx
  let ct := chacha20 c.keyB 1 c.nonceB c.ptB
  have px : PInv c.A u.mem ((c.aadB ++ pad16 c.aadB) ++ (ct ++ pad16 ct)) x.mem := by
    have h := hx.inv; rw [ctW] at h; exact h
  have ctX : Ctx.bytesAt x.mem c.out c.len.toNat = ct := by
    change Ctx.bytesAt x.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB
    rw [← ctW]
    exact bytesAt_congr (fun j hj => hx.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply (lengths_reach_r (Rd := Rd) c hv encLengthsAt _ slen bll tl (by decide) (by decide)
    x hx.pc hx.body.sp hx.body.high hx.body.code u.mem _ px
    (region_ns (by decide +kernel) (by decide)) hblk).mono (fun _ _ h => h)
  intro y hy
  have by' := hx.body.lengths hv hy (fun y h => .inl (macWr_swr _ y h))
  have plen : PInv c.A u.mem (macData c.aadB ct) y.mem := by
    have h := hy.inv
    have hl : ct.length = c.len.toNat := by rw [ChaCha20Spec.chacha20_length, ACall.ptB, bytesAt_length]
    simpa only [macData, ACall.aadB, bytesAt_length, lengthBlock, hl, List.append_assoc] using h
  have ctY : Ctx.bytesAt y.mem c.out c.len.toNat = ct := by
    rw [← ctX]
    exact bytesAt_congr (fun j hj => hy.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply ((finish_phase_w c hv hb false encFinEAt sf _ blf tf (by decide) (by decide)
    y hy.pc by'.sp by'.high by'.code ic u hu.init hu.ictx hu.pkey _ plen
    (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide)) (finPc_ns c.base)).toRd hn).mono (fun _ _ h => h)
  intro z hz
  have zh : Hi c z.mem := by'.high.congr (fun o a b => hz.frame _ (finish_not_A c hv hb false o b (.inr a)))
  have zr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → z.regs r = c.regs0 r :=
    fun r a b => (hz.hi r (by omega) b).trans (by'.hi r a b)
  have ctZ : Ctx.bytesAt z.mem c.out c.len.toNat = ct := by
    rw [← ctY]
    apply bytesAt_congr
    intro j hj
    apply hz.frame
    rintro (⟨q, hq, eq⟩ | ⟨q, hq, eq⟩)
    · exact hv.not_swr hb.outStack hj (by
        refine Region.mk (o := 156+q) (by omega) ?_
        rw [eq, BitVec.ofNat_add, ← BitVec.add_assoc]; congr 1; bv_omega)
    · exact ne_of_disj hb.tagO.2.1 hb.tagO.1 (Or.symm hb.tagO.2.2) hj hq eq
  have zframe : ∀ a, ¬ AWr c a → z.mem a = c.m0 a := fun a ha =>
    (hz.frame a (fun h => ha (finishWr_awr c a h))).trans (by'.frame a ha)
  apply ReachS.bind
  apply ((clear_reach_w c.base c.A encClrAAt sca scl bcl hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega) (by decide) (by decide) z hz.pc hz.sp
    (region_ns (by decide +kernel) (by decide)) (region_ns (by decide +kernel) (by decide))
    (pt_ns (by decide +kernel) (by decide))).toRd hn).mono (fun _ _ h => h)
  intro q hq
  have qh : Hi c q.mem := zh.congr (fun o a b => hq.frame _ (by
    rintro ⟨j, hj, eq⟩
    exact off_ne c.A (a := o) (b := 8+j) (by omega) (by omega) (by omega) eq))
  have qs : q.regs 13 = c.A := by rw [hq.hi 13 (by decide) (by decide), hz.sp]
  have qr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → q.regs r = c.regs0 r :=
    fun r a b => (hq.hi r (by omega) (by omega)).trans (zr r a b)
  apply ((epilogue_reach_w c hv (AWr c) false encEpiAt sepi pop (by decide) (by decide) q hq.pc qs qh qr hlr
    (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide))).toRd hn).mono
    (fun _ _ h => h)
  rintro t ⟨ht, tm⟩
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · change Ctx.bytesAt t.mem c.out c.len.toNat = ct
    rw [tm, ← ctZ]
    exact bytesAt_congr (fun j hj => hq.frame _ (fun h => hv.not_swr hb.outStack hj (clearWr_swr _ _ h)))
  · change Ctx.bytesAt t.mem c.tag 16 = M0Crypto.Spec.Aead.poly1305
      (M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB) (macData c.aadB ct)
    rw [tm, ← hz.tagBytes]
    exact bytesAt_congr (fun j hj => hq.frame _ (fun h => hv.not_swr hb.tagStack hj (clearWr_swr _ _ h)))
  · intro a ha
    rw [tm, hq.frame a (fun h => ha (.inl (clearWr_swr _ _ h))), zframe a ha]
  · intro o ho; rw [tm]; exact hq.zero o ho

end M0Crypto.Release.Aead
