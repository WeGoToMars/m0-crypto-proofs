import M0Crypto.Release.AeadStoreSites

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Checked decryption under the output-store policy

`decrypt_reach_p`: the run of `decrypt_reach_w` with the step condition strengthened by `CPol`.
Only the two ChaCha calls run output-store instructions; every other routine is site-free.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (OutputStorePC outputStoreOffset PCBetween)
open M0Crypto.Spec.Aead (pad16 macData chacha20 decrypt poly1305 polyKey)

/-- Program counters of the decrypt function and the Poly1305 routines it calls (not ChaCha). -/
def DecNon (base : Word) (pc : Word) : Prop :=
  PCBetween base decOff decEnd pc ∨ Poly1305Blocks.BlkPc base pc ∨ Poly1305Init.InitPc base pc ∨ Poly1305Finish.FinPc base pc

theorem decNon_dec {base : Word} {pc : Word} (h : DecNon base pc) : DecAllPc base pc := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

theorem decOwn_free : ∀ o, decOff ≤ o → o < decEnd → outputStoreOffset o = false := by
  have : ∀ o < decEnd, decOff ≤ o → outputStoreOffset o = false := by decide +kernel
  exact fun o h1 h2 => this o h2 h1

theorem decCrypt_free (base : Word) : ∀ j < seqSize crypt, ¬ OutputStorePC base (base + BitVec.ofNat 32 (decCryptAt + j)) := by
  have : ∀ j < seqSize crypt, outputStoreOffset (decCryptAt + j) = false := by decide +kernel
  exact fun j hj => not_outputStorePC (by have := (by decide : decCryptAt + seqSize crypt < 2 ^ 32); omega) (this j hj)

theorem decNon_free (base : Word) : ∀ pc, DecNon base pc → ¬ OutputStorePC base pc := by
  rintro pc (h | h | h | h)
  · exact noSite_between (by decide) decOwn_free pc h
  · exact noSite_between (by decide) (by
      have : ∀ o < Poly1305Blocks.popAt + 2, Poly1305Blocks.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
      exact fun o h1 h2 => this o h2 h1) pc h
  · exact noSite_between (by decide) (by
      have : ∀ o < Poly1305Init.popAt + 2, Poly1305Init.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
      exact fun o h1 h2 => this o h2 h1) pc h
  · exact noSite_between (by decide) (by
      have : ∀ o < Poly1305Finish.popAt + 2, Poly1305Finish.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
      exact fun o h1 h2 => this o h2 h1) pc h

theorem decrypt_tail_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decVerdictAt) (h : Body c (SWr c.A) s)
    (hz : s.regs 3=0#32 ↔ c.expected=c.tagB) (hlr : (c.regs0 14).getLsbD 0=true)
    (hPc : ∀ pc, DecAllPc c.base pc → Pc pc) :
    ReachS c.base (PolW c Pc (DAllowed c)) s (DecryptResult c) := by
  have hE : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd pc → M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd pc := fun pc h => h
  have hEc : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd pc → Pc pc := fun pc h => hPc pc (.inl h)
  have hfreeO := noSite_between (base := c.base) (lo := decOff) (hi := decEnd) (by decide) decOwn_free
  have hPo : ∀ x ev, RegionWrites (M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd) (DAllowed c) x ev → PolW c Pc (DAllowed c) x ev :=
    polW_of_free hfreeO (fun pc h => hEc pc h) (fun _ h => h)
  have hCha : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inl h))
  obtain ⟨ez, em, er⟩ := verdict_effect s
  apply ReachS.blockW hPo (is := verdict) (regionOf hE (by decide +kernel) (by decide +kernel)) (by have := hv.base4; omega) hp (by decide) (by decide) (by decide)
    (by simp [alignedAll, verdict, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _)
  generalize hu : execAll verdict s=u at ez em er
  have up : u.pc=c.base+BitVec.ofNat 32 decRejectBrAt := by rw [←hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have ub : Body c (SWr c.A) u := h.same em (er 13 (by decide) (by decide))
    (fun r a b => er r (by omega) (by omega))
  apply ReachS.bcondW hPo (pcOf hE (by decide +kernel) (by decide +kernel)) (by have := hv.base4; omega) decRejectAt 1 (brImm8 decRejectBrAt decRejectAt) up (by decide) (by decide +kernel)
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
    apply (ReachW.toPol (status_reach_w c hv (DAllowed c) true decRejectAt (by decide) (by decide) v
      (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq]) (regionOf hE (by decide +kernel) (by decide +kernel))) hfreeO hEc (fun _ h => h)).mono (fun _ _ h => h)
    rintro w ⟨wp, w4, wm, wr⟩
    have wb : Body c (SWr c.A) w := vb.same wm (wr 13 (by decide) (by decide))
      (fun r a b => wr r (by omega) (by omega))
    refine ReachW.toPol (decrypt_return_w c hv hb w wp ?_ hlr hE) hfreeO hEc (fun _ h => h)
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
    have reach := crypt_reach_p c hv hb decCryptAt (blImm (decCryptAt + cryptXorOff) xorOff) (by decide) (by decide) dec_calls.2.2.2.2
      (by decide) (by decide) v (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq, hfall]) vb.sp vb.high vb.nonce vb.frame
      (regionOf hEc (by decide +kernel) (by decide +kernel)) (pcOf hEc (by decide +kernel) (by decide +kernel))
      (decCrypt_free c.base) (not_outputStorePC (by decide) (by decide +kernel))
      (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) hCha
    apply ReachS.bind
    apply reach.mono (fun _ _ h => PolW.monoW (fun y h => h.elim Or.inl (fun ho => Or.inr ⟨hok, ho⟩)) h)
    intro w hw
    have wb := vb.crypt hv hb hw
    have wf : ∀ y, ¬DWr c y → w.mem y=c.m0 y := by
      intro y hy
      rw [hw.keep y (fun o ho e => hy (.inl (e ▸ swr_lo c.A o ho)))
        (fun o ho e => hy (.inl (e ▸ swr_A c.A (4+o) (by omega)))) (fun h => hy (.inr h))]
      exact vb.frame y (fun h => hy (.inl h))
    apply ReachS.bind
    apply (ReachW.toPol (status_reach_w c hv (DAllowed c) false decAcceptAt (by decide) (by decide) w hw.pc (regionOf hE (by decide +kernel) (by decide +kernel))) hfreeO hEc (fun _ h => h)).mono
      (fun _ _ h => h)
    rintro x ⟨xp, x4, xm, xr⟩
    apply ReachS.bW hPo (pcOf hE (by decide +kernel) (by decide +kernel)) (by have := hv.base4; omega) decClrAAt (brImm11 decSkipAt decClrAAt) xp (by decide) (by decide) (by decide) (by decide)
    generalize hy : x.setReg 15 (c.base+BitVec.ofNat 32 decClrAAt)=y
    refine ReachW.toPol (decrypt_return_w c hv hb y (by rw [←hy, M0Crypto.Armv6M.State.pc, setReg_eq]) ?_ hlr hE) hfreeO hEc (fun _ h => h)
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

/-- The decrypt setup and MAC phases establish the inputs to tag comparison. -/

theorem decrypt_compare_entry_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hPc : ∀ pc, DecAllPc c.base pc → Pc pc) :
    ReachS c.base (PolW c Pc (DAllowed c)) s (fun y =>
      y.pc = c.base + BitVec.ofNat 32 decCmpAAt ∧ Body c (SWr c.A) y ∧
      Ctx.bytesAt y.mem c.tag 16 = c.tagB ∧
      Ctx.bytesAt y.mem (c.A + 72#32) 16 = c.expected) := by
  have hfreeN := decNon_free c.base
  have hPnN : ∀ pc, DecNon c.base pc → Pc pc := fun pc h => hPc pc (decNon_dec h)
  have hE : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd pc → DecNon c.base pc := fun pc h => .inl h
  have hCha : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inl h))
  have hBlk : ∀ pc, Poly1305Blocks.BlkPc c.base pc → DecNon c.base pc := fun pc h => .inr (.inl h)
  have hIni : ∀ pc, Poly1305Init.InitPc c.base pc → DecNon c.base pc := fun pc h => .inr (.inr (.inl h))
  have hFin : ∀ pc, Poly1305Finish.FinPc c.base pc → DecNon c.base pc := fun pc h => .inr (.inr (.inr h))
  obtain ⟨tx, ti', tl, tf, tc⟩ := dec_calls
  obtain ⟨_, _, _, _, _, mad, _, mct, _⟩ := dec_at
  apply ReachS.bind
  apply (aead_setup_p (Pc := Pc) (Pn := DecNon c.base) c hv decOff (blImm (decOff + proXorOff) xorOff) (blImm (decOff + initCallOff) initOff)
    (by decide) (by decide) tx
    (by decide) (by decide) ti' (by decide) (by decide) s he hfreeN hPnN
    (regionOf hE (by decide +kernel) (by decide +kernel)) (hPnN _ (pcOf hE (by decide +kernel) (by decide +kernel)))
    (not_outputStorePC (by decide) (by decide +kernel))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel)) hCha hIni).mono
    (fun _ _ h => PolW.monoW (fun _ h => .inl h) h)
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  have aadU : Ctx.bytesAt u.mem c.aad c.alen.toNat=c.aadB :=
    bytesAt_congr (fun j hj => bu.frame _ (hv.not_swr hb.aadS hj))
  apply ReachS.bind
  apply (ReachW.toPol (mac_phase_w c hv (SWr c.A) decLoadAadAt loadAad 0x24 0x25 rfl (by decide)
    (blImm (decLoadAadAt + seqSize loadAad + macBlOff) blocksOff)
    (blImm (decLoadAadAt + seqSize loadAad + macBl2Off) blocksOff)
    mad (by decide) (by decide) u hu.pc c.aad c.alen hb.aadS bu.high.aad bu.high.alen bu u.mem [] pi
    (macWr_swr c.A) (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel)) hBlk) hfreeN hPnN (fun _ h => .inl h)).mono (fun _ _ h => h)
  intro v hv'
  have pv : PInv c.A u.mem (c.aadB++pad16 c.aadB) v.mem := by
    have h := hv'.inv; rw [aadU, List.nil_append] at h; exact h
  have inV : Ctx.bytesAt v.mem c.inp c.len.toNat=c.ptB :=
    bytesAt_congr (fun j hj => hv'.body.frame _ (hv.not_swr hb.inS hj))
  apply ReachS.bind
  apply (ReachW.toPol (mac_phase_w c hv (SWr c.A) decLoadInAt loadIn 0x1c 0x1d rfl (by decide)
    (blImm (decLoadInAt + seqSize loadIn + macBlOff) blocksOff)
    (blImm (decLoadInAt + seqSize loadIn + macBl2Off) blocksOff)
    mct (by decide) (by decide) v hv'.pc c.inp c.len hb.inS hv'.body.high.inp hv'.body.high.len hv'.body
    u.mem _ pv (macWr_swr c.A) (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel)) hBlk) hfreeN hPnN (fun _ h => .inl h)).mono (fun _ _ h => h)
  intro w hw
  have pw : PInv c.A u.mem ((c.aadB++pad16 c.aadB)++(c.ptB++pad16 c.ptB)) w.mem := by
    have h := hw.inv; rw [inV] at h; exact h
  apply ReachS.bind
  apply (ReachW.toPol (lengths_reach_w c hv decLengthsAt (blImm (decLengthsAt + seqSize lengths) blocksOff) (by decide) (by decide) tl (by decide) (by decide)
    w hw.pc hw.body.sp hw.body.high hw.body.code u.mem _ pw (regionOf hE (by decide +kernel) (by decide +kernel)) hBlk) hfreeN hPnN (fun y h => .inl (macWr_swr _ y h))).mono (fun _ _ h => h)
  intro x hx
  have bx := hw.body.lengths hv hx (macWr_swr c.A)
  have px : PInv c.A u.mem (macData c.aadB c.ptB) x.mem := by
    have h := hx.inv
    simpa only [macData, ACall.aadB, ACall.ptB, bytesAt_length, lengthBlock, List.append_assoc] using h
  apply ReachS.bind
  apply (ReachW.toPol (finish_phase_w c hv hb true decFinDAt (by decide) (blImm (decFinDAt + seqSize (finArgs true)) finishOff) (by decide) tf (by decide) (by decide)
    x hx.pc bx.sp bx.high bx.code ic u hu.init hu.ictx hu.pkey _ px (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel)) hFin) hfreeN hPnN (fun y h => .inl (finishWr_swr _ y h))).mono (fun _ _ h => h)
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

/-- Full checked-decryption run of the frozen machine code. -/

theorem decrypt_reach_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0=true)
    (hPc : ∀ pc, DecAllPc c.base pc → Pc pc) :
    ReachS c.base (PolW c Pc (DAllowed c)) s (DecryptResult c) := by
  have hfreeN := decNon_free c.base
  have hPnN : ∀ pc, DecNon c.base pc → Pc pc := fun pc h => hPc pc (decNon_dec h)
  have hE : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween c.base decOff decEnd pc → DecNon c.base pc := fun pc h => .inl h
  apply ReachS.bind
  apply (decrypt_compare_entry_p c hv hb s he hPc).mono (fun _ _ h => h)
  rintro y ⟨ypc, yb, tagY, tag⟩
  apply ReachS.bind
  apply (ReachW.toPol (compare_reach_w c hv y ypc yb.sp yb.high (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))) hfreeN hPnN (fun _ h => False.elim h)).mono
    (fun _ _ h => h)
  rintro z ⟨zp, zm, zr, zeq⟩
  have zb := yb.same zm (zr 13 (by decide) (by decide)) (fun r a b => zr r (by omega) (by omega))
  apply decrypt_tail_p c hv hb z zp zb _ hlr hPc
  rw [zeq, tagY, tag]
  exact eq_comm

end M0Crypto.Release.Aead
