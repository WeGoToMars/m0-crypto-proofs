import M0Crypto.Release.AeadCompareReads
import M0Crypto.Release.AeadLengthsReads
import M0Crypto.Release.AeadReadsPhases

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Checked decryption under the read policy

`decrypt_reach_r`: the run of `decrypt_reach_w`, with the step condition "a load at a read site
reads only bytes of `Rd`".
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (PCBetween)
open M0Crypto.Spec.Aead (pad16 macData chacha20 decrypt poly1305 polyKey)

theorem decrypt_return_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decClrAAt) (h : DecryptReady c s) (hlr : (c.regs0 14).getLsbD 0=true) :
    ReachS c.base (RdP c.base Rd) s (DecryptResult c) := by
  apply ((clear_return_w c hv true decClrAAt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s hp h.sp h.high h.hi hlr
    (region_ns (by decide +kernel) (by decide)) (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide)) (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide))).toRd (fun _ h => h)).mono (fun _ _ h => h)
  rintro t ⟨ht, hz, hf⟩
  have eout : Ctx.bytesAt t.mem c.out c.len.toNat=Ctx.bytesAt s.mem c.out c.len.toNat :=
    bytesAt_congr (fun j hj => hf _ (fun hw => hv.not_swr hb.outStack hj (clearWr_swr _ _ hw)))
  have ho := eout.trans h.out
  have ha : RetPost c (if c.expected=c.tagB then 0#32 else 0xfffffffe#32) t := by simpa only [ite_true, h.r4] using ht
  refine ⟨ha, ?_, ?_, ?_, hz⟩
  · intro pt hs
    have hok : c.expected=c.tagB := by
      by_cases hn : c.expected=c.tagB
      · exact hn
      · simp only [decrypt_eq, if_neg hn] at hs
        cases hs
    refine ⟨by rw [ha.r0, if_pos hok], ?_⟩
    simpa only [hs] using ho
  · intro hs
    have hbad : c.expected≠c.tagB := by
      intro heq
      simp only [decrypt_eq, if_pos heq] at hs
      cases hs
    exact ⟨by rw [ha.r0, if_neg hbad], by simpa only [hs] using ho⟩
  · intro y hy
    rw [hf y (fun hw => hy (.inl (clearWr_swr _ _ hw))), h.frame y hy]

theorem decrypt_tail_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decVerdictAt) (h : Body c (SWr c.A) s)
    (hz : s.regs 3=0#32 ↔ c.expected=c.tagB) (hlr : (c.regs0 14).getLsbD 0=true)
    (hsub : ∀ y, TraceSpec.AeadDecryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) s (DecryptResult c) := by
  obtain ⟨ez, em, er⟩ := verdict_effect s
  apply ReachS.blockW (Pn := NoSite c.base) (Wr := DAllowed c) (noP c.base Rd) (is := verdict) (region_ns (by decide +kernel) (by decide)) (by have := hv.base4; omega) hp (by decide) (by decide) (by decide)
    (by simp [alignedAll, verdict, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _)
  generalize hu : execAll verdict s=u at ez em er
  have up : u.pc=c.base+BitVec.ofNat 32 decRejectBrAt := by rw [←hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have ub : Body c (SWr c.A) u := h.same em (er 13 (by decide) (by decide))
    (fun r a b => er r (by omega) (by omega))
  apply ReachS.bcondW (Pn := NoSite c.base) (Wr := DAllowed c) (noP c.base Rd) (pt_ns (by decide +kernel) (by decide)) (by have := hv.base4; omega) decRejectAt 1 (brImm8 decRejectBrAt decRejectAt) up (by decide) (by decide +kernel)
    (by decide) (by decide +kernel)
  · intro hn
    have hbad : c.expected≠c.tagB := by
      have hn' : s.regs 3≠0#32 := by simpa [condPassed, ez] using hn
      exact fun e => hn' (hz.mpr e)
    generalize hv' : u.setReg 15 (c.base+BitVec.ofNat 32 decRejectAt)=v
    have vb : Body c (SWr c.A) v := ub.same (by rw [←hv']; rfl)
      (by rw [←hv', setReg_ne _ _ _ _ (by decide)])
      (fun r a b => by rw [←hv', setReg_ne _ _ _ _ (by rintro rfl; omega)])
    apply ReachS.bind
    apply ((status_reach_w c hv (DAllowed c) true decRejectAt (by decide) (by decide) v
      (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq]) (region_ns (by decide +kernel) (by decide))).toRd (fun _ h => h)).mono (fun _ _ h => h)
    rintro w ⟨wp, w4, wm, wr⟩
    have wb : Body c (SWr c.A) w := vb.same wm (wr 13 (by decide) (by decide))
      (fun r a b => wr r (by omega) (by omega))
    apply decrypt_return_r c hv hb w wp _ hlr
    refine ⟨wb.sp, wb.high, wb.hi, ?_, ?_, ?_⟩
    · simpa [if_neg hbad] using w4
    · simp only [decrypt_eq, if_neg hbad]
      exact bytesAt_congr (fun j hj => wb.frame _ (hv.not_swr hb.outStack hj))
    · intro y hy; exact wb.frame y (fun hw => hy (.inl hw))
  · intro heq
    have hok : c.expected=c.tagB := by
      apply hz.mp
      simpa [condPassed, ez] using heq
    have hfall : decRejectBrAt + 2 = decCryptAt := by decide
    generalize hv' : u.setReg 15 (c.base+BitVec.ofNat 32 (decRejectBrAt + 2))=v
    have vb : Body c (SWr c.A) v := ub.same (by rw [←hv']; rfl)
      (by rw [←hv', setReg_ne _ _ _ _ (by decide)])
      (fun r a b => by rw [←hv', setReg_ne _ _ _ _ (by rintro rfl; omega)])
    have reach := crypt_reach_r (Rd := Rd) c hv hb decCryptAt (blImm (decCryptAt + cryptXorOff) xorOff) (by decide) (by decide) dec_calls.2.2.2.2
      (by decide) (by decide) v (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq, hfall]) vb.sp vb.high vb.nonce vb.frame
      (fun j hj => not_siteRd (by have := (by decide : decCryptAt + seqSize crypt < 2 ^ 32); omega)
        (no_readSite (by decide +kernel : firstReadSite decCryptAt (seqSize crypt) = none) j hj))
      (pt_ns (by decide +kernel) (by decide))
      (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) (fun y h => hsub y (.enc h))
    apply ReachS.bind
    apply reach.mono (fun _ _ h => h)
    intro w hw
    have wb := vb.crypt hv hb hw
    have wf : ∀ y, ¬DWr c y → w.mem y=c.m0 y := by
      intro y hy
      rw [hw.keep y (fun o ho e => hy (.inl (e ▸ swr_lo c.A o ho)))
        (fun o ho e => hy (.inl (e ▸ swr_A c.A (4+o) (by omega)))) (fun h => hy (.inr h))]
      exact vb.frame y (fun h => hy (.inl h))
    apply ReachS.bind
    apply ((status_reach_w c hv (DAllowed c) false decAcceptAt (by decide) (by decide) w hw.pc (region_ns (by decide +kernel) (by decide))).toRd (fun _ h => h)).mono
      (fun _ _ h => h)
    rintro x ⟨xp, x4, xm, xr⟩
    apply ReachS.bW (Pn := NoSite c.base) (Wr := DAllowed c) (noP c.base Rd) (pt_ns (by decide +kernel) (by decide)) (by have := hv.base4; omega) decClrAAt (brImm11 decSkipAt decClrAAt) xp (by decide) (by decide) (by decide) (by decide)
    generalize hy : x.setReg 15 (c.base+BitVec.ofNat 32 decClrAAt)=y
    apply decrypt_return_r c hv hb y (by rw [←hy, M0Crypto.Armv6M.State.pc, setReg_eq]) _ hlr
    have ym : y.mem=w.mem := by rw [←hy, setReg_mem, xm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [←hy, setReg_ne _ _ _ _ (by decide), xr 13 (by decide) (by decide), wb.sp]
    · rw [ym]; exact wb.high
    · intro r a b
      rw [←hy, setReg_ne _ _ _ _ (by rintro rfl; omega), xr r (by omega) (by omega), wb.hi r a b]
    · rw [←hy, setReg_ne _ _ _ _ (by decide), x4, if_pos hok]; rfl
    · simp only [decrypt_eq, if_pos hok]
      rw [ym]; exact hw.out
    · intro a ha; rw [ym]; exact wf a ha

theorem decrypt_compare_entry_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hsub : ∀ y, TraceSpec.AeadDecryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) s (fun y =>
      y.pc = c.base + BitVec.ofNat 32 decCmpAAt ∧ Body c (SWr c.A) y ∧
      Ctx.bytesAt y.mem c.tag 16 = c.tagB ∧
      Ctx.bytesAt y.mem (c.A + 72#32) 16 = c.expected) := by
  have hsubE : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y := fun y h => hsub y (.enc h)
  have hblk := rd_blk c hsubE
  obtain ⟨tx, ti', tl, tf, tc⟩ := dec_calls
  obtain ⟨_, _, _, _, _, mad, _, mct, _⟩ := dec_at
  apply ReachS.bind
  apply (aead_setup_r (Rd := Rd) c hv decOff (blImm (decOff + proXorOff) xorOff) (blImm (decOff + initCallOff) initOff)
    (by decide) (by decide) tx
    (by decide) (by decide) ti' (by decide) (by decide) s he (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide)) (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide))
    (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) hsubE).mono (fun _ _ h => h)
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  have aadU : Ctx.bytesAt u.mem c.aad c.alen.toNat=c.aadB :=
    bytesAt_congr (fun j hj => bu.frame _ (hv.not_swr hb.aadS hj))
  apply ReachS.bind
  apply (mac_phase_r (Rd := Rd) c hv (SWr c.A) decLoadAadAt loadAad 0x24 0x25 rfl (by decide)
    (blImm (decLoadAadAt + seqSize loadAad + macBlOff) blocksOff)
    (blImm (decLoadAadAt + seqSize loadAad + macBl2Off) blocksOff)
    mad (by decide) (by decide) u hu.pc c.aad c.alen hb.aadS bu.high.aad bu.high.alen bu u.mem [] pi
    (macWr_swr c.A) (region_ns (by decide +kernel) (by decide)) (macFree_of_first (by decide +kernel))
    (fun o ho => hsubE _ (.aad ho rfl)) hblk).mono (fun _ _ h => h)
  intro v hv'
  have pv : PInv c.A u.mem (c.aadB++pad16 c.aadB) v.mem := by
    have h := hv'.inv; rw [aadU, List.nil_append] at h; exact h
  have inV : Ctx.bytesAt v.mem c.inp c.len.toNat=c.ptB :=
    bytesAt_congr (fun j hj => hv'.body.frame _ (hv.not_swr hb.inS hj))
  apply ReachS.bind
  apply (mac_phase_r (Rd := Rd) c hv (SWr c.A) decLoadInAt loadIn 0x1c 0x1d rfl (by decide)
    (blImm (decLoadInAt + seqSize loadIn + macBlOff) blocksOff)
    (blImm (decLoadInAt + seqSize loadIn + macBl2Off) blocksOff)
    mct (by decide) (by decide) v hv'.pc c.inp c.len hb.inS hv'.body.high.inp hv'.body.high.len hv'.body
    u.mem _ pv (macWr_swr c.A) (region_ns (by decide +kernel) (by decide)) (macFree_of_first (by decide +kernel))
    (fun o ho => hsubE _ (.inp ho rfl)) hblk).mono (fun _ _ h => h)
  intro w hw
  have pw : PInv c.A u.mem ((c.aadB++pad16 c.aadB)++(c.ptB++pad16 c.ptB)) w.mem := by
    have h := hw.inv; rw [inV] at h; exact h
  apply ReachS.bind
  apply (lengths_reach_r (Rd := Rd) c hv decLengthsAt (blImm (decLengthsAt + seqSize lengths) blocksOff) (by decide) (by decide) tl (by decide) (by decide)
    w hw.pc hw.body.sp hw.body.high hw.body.code u.mem _ pw (region_ns (by decide +kernel) (by decide)) hblk).mono (fun _ _ h => h)
  intro x hx
  have bx := hw.body.lengths hv hx (macWr_swr c.A)
  have px : PInv c.A u.mem (macData c.aadB c.ptB) x.mem := by
    have h := hx.inv
    simpa only [macData, ACall.aadB, ACall.ptB, bytesAt_length, lengthBlock, List.append_assoc] using h
  apply ReachS.bind
  apply ((finish_phase_w c hv hb true decFinDAt (by decide) (blImm (decFinDAt + seqSize (finArgs true)) finishOff) (by decide) tf (by decide) (by decide)
    x hx.pc bx.sp bx.high bx.code ic u hu.init hu.ictx hu.pkey _ px (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide)) (finPc_ns c.base)).toRd (fun _ h => h)).mono (fun _ _ h => h)
  intro y hy
  have yf : ∀ a, ¬SWr c.A a → y.mem a=c.m0 a := fun a ha =>
    (hy.frame a (fun h => ha (finishWr_swr _ a h))).trans (bx.frame a ha)
  have yb : Body c (SWr c.A) y := ⟨hy.sp,
    bx.high.congr (fun o a b => hy.frame _ (finish_not_A c hv hb true o b (.inr a))),
    (by rw [←bx.nonce]; exact read32_congr (fun k hk => hy.frame _ (finish_not_A c hv hb true k (by omega) (.inl (by omega))))),
    (fun r a b => (hy.hi r (by omega) b).trans (bx.hi r a b)), yf, hv.codeAt_of yf⟩
  have tagY : Ctx.bytesAt y.mem c.tag 16=c.tagB :=
    bytesAt_congr (fun j hj => yf _ (hv.not_swr hb.tagStack hj))
  apply ReachS.done
  refine ⟨hy.pc, yb, tagY, ?_⟩
  exact hy.tagBytes

theorem decrypt_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0=true)
    (hsub : ∀ y, TraceSpec.AeadDecryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) s (DecryptResult c) := by
  apply ReachS.bind
  apply (decrypt_compare_entry_r (Rd := Rd) c hv hb s he hsub).mono (fun _ _ h => h)
  rintro y ⟨ypc, yb, tagY, tag⟩
  apply ReachS.bind
  apply (compare_reach_r (Rd := Rd) c hv y ypc yb.sp yb.high (region_ns (by decide +kernel) (by decide)) (pt_ns (by decide +kernel) (by decide))
    (fun j hj => hsub _ (.tag hj rfl)) (rd_blk c (fun y h => hsub y (.enc h)))).mono
    (fun _ _ h => h)
  rintro z ⟨zp, zm, zr, zeq⟩
  have zb := yb.same zm (zr 13 (by decide) (by decide)) (fun r a b => zr r (by omega) (by omega))
  apply decrypt_tail_r c hv hb z zp zb _ hlr hsub
  rw [zeq, tagY, tag]
  exact eq_comm

end M0Crypto.Release.Aead
