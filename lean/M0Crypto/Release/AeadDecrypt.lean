import M0Crypto.Release.AeadCompare
import M0Crypto.Release.AeadCompose
import M0Crypto.Release.AeadCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.AEAD (pad16 macData chacha20 decrypt poly1305 polyKey)

def ACall.tagB (c : ACall) := Ctx.bytesAt c.m0 c.tag 16
def ACall.expected (c : ACall) := poly1305 (polyKey c.keyB c.nonceB) (macData c.aadB c.ptB)
def DWr (c : ACall) (y : Word) : Prop := SWr c.A y ∨ OutR c y

/-- Output stores are permitted only after successful authentication. -/
def DAllowed (c : ACall) (y : Word) : Prop := SWr c.A y ∨ (c.expected=c.tagB ∧ OutR c y)

theorem decrypt_eq (c : ACall) : decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB =
    if c.expected=c.tagB then some (chacha20 c.keyB 1 c.nonceB c.ptB) else none := rfl


/-- Checked decryption, unchanged output on authentication failure, erasure and ABI. -/
structure DecryptResult (c : ACall) (t : State) : Prop where
  abi : RetPost c (if c.expected=c.tagB then 0#32 else 0xfffffffe#32) t
  ok : ∀ pt, decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB=some pt →
    t.regs 0=0#32 ∧ Ctx.bytesAt t.mem c.out c.len.toNat=pt
  reject : decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB=none →
    t.regs 0=0xfffffffe#32 ∧ Ctx.bytesAt t.mem c.out c.len.toNat=Ctx.bytesAt c.m0 c.out c.len.toNat
  frame : ∀ y, ¬ DWr c y → t.mem y=c.m0 y
  zero : ∀ o<96, t.mem (c.A+BitVec.ofNat 32 (8+o))=0#8

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5

theorem verdict_effect (s : State) : (execAll verdict s).z=(s.regs 3==0#32) ∧
    (execAll verdict s).mem=s.mem ∧
    (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → (execAll verdict s).regs r=s.regs r) := by
  refine ⟨?_, rfl, fun r a b => execAll_regs_other _ _ _ b (by
    have h0 : r.val ≠ 0 := by omega
    have h5 : r.val ≠ 5 := by omega
    simp [verdict, Instr.dsts, Fin.ext_iff, h0, h5]; omega)⟩
  simp [verdict, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
    ChaChaLoop.sub_flags]
  rw [show (4294967295#32 : Word)= ~~~0#32 from rfl, ChaChaLoop.sub_flags, BitVec.sub_zero]

def statusCode (bad : Bool) : List Instr := if bad then reject else accept

theorem status_effect (bad : Bool) (s : State) :
    (execAll (statusCode bad) s).regs 4=(if bad then 0xfffffffe#32 else 0#32) ∧
    (execAll (statusCode bad) s).mem=s.mem ∧
    (∀ r : Reg, r.val≠4 → r.val≠15 → (execAll (statusCode bad) s).regs r=s.regs r) := by
  refine ⟨?_, ?_, fun r a b => execAll_regs_other _ _ _ b (by cases bad <;> simp [statusCode, reject, accept, Instr.dsts, Fin.ext_iff, a] <;> omega)⟩
  all_goals cases bad <;> simp [statusCode, reject, accept, execAll, Instr.next, Instr.exec, addFlags,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.addWithCarry]

theorem status_reach (c : ACall) (hv : AValid c) (Wr : Word → Prop) (bad : Bool) (off : Nat)
    (hat : seqAt B off (statusCode bad)=true) (ho : off%2=0) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 off) :
    Reach c.base Wr s (fun t => t.pc=c.base+BitVec.ofNat 32 (off+(if bad then 4 else 2)) ∧
      t.regs 4=(if bad then 0xfffffffe#32 else 0#32) ∧ t.mem=s.mem ∧
      ∀ r : Reg, r.val≠4 → r.val≠15 → t.regs r=s.regs r) := by
  obtain ⟨e4, em, er⟩ := status_effect bad s
  apply Reach.block (by have := hv.base4; omega) (statusCode bad) off hp ho hat
    (by cases bad <;> rfl) (by cases bad <;> simp [statusCode, reject, accept, alignedAll, Instr.accesses])
    (ChaChaBlock.noWrites _ _ (by cases bad <;> rfl) _)
  apply Reach.done
  refine ⟨?_, e4, em, er⟩
  rw [execAll_pc _ _ (by cases bad <;> rfl), hp, ofNat_add_assoc]
  cases bad <;> rfl

structure DecryptReady (c : ACall) (s : State) : Prop where
  sp : s.regs 13=c.A
  high : Hi c s.mem
  hi : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → s.regs r=c.regs0 r
  r4 : s.regs 4=(if c.expected=c.tagB then 0#32 else 0xfffffffe#32)
  out : Ctx.bytesAt s.mem c.out c.len.toNat =
    match decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB with
    | some pt => pt
    | none => Ctx.bytesAt c.m0 c.out c.len.toNat
  frame : ∀ y, ¬DWr c y → s.mem y=c.m0 y

/-- Both verdict paths join at the same erasure and return sequence. -/
theorem decrypt_return (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decClrAAt) (h : DecryptReady c s) (hlr : (c.regs0 14).getLsbD 0=true) :
    Reach c.base (DAllowed c) s (DecryptResult c) := by
  obtain ⟨spro, blx, scopy, bli, laad, mad, lin, mct, slen, bll, sf, blf, scma, scml, bcml, sv, bcr, scr, blc, sa, bsk, sr, sca, scl, bcl, sepi, pop⟩ := dec_at
  apply ((clear_return c hv true decClrAAt sca scl bcl sepi pop
    (by decide) (by decide) s hp h.sp h.high h.hi hlr).monoW (fun _ h => .inl h)).mono
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

theorem Body.same {c : ACall} {Wr : Word → Prop} {s t : State} (h : Body c Wr s)
    (hm : t.mem=s.mem) (hs : t.regs 13=s.regs 13)
    (hr : ∀ r : Reg, 8 ≤ r.val → r.val<12 → t.regs r=s.regs r) : Body c Wr t :=
  ⟨hs.trans h.sp, by rw [hm]; exact h.high, by rw [hm]; exact h.nonce,
    fun r a b => (hr r a b).trans (h.hi r a b), (fun y hy => by rw [hm]; exact h.frame y hy), by rw [hm]; exact h.code⟩

/-- An accepted verdict reaches the decryption call setup with the
authentication-phase invariant intact. -/
theorem decrypt_verdict_reaches_crypt (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 decVerdictAt) (h : Body c (SWr c.A) s)
    (hz : s.regs 3 = 0#32 ↔ c.expected = c.tagB) (hok : c.expected = c.tagB) :
    Reach c.base (DAllowed c) s (fun v =>
      v.pc = c.base + BitVec.ofNat 32 decCryptAt ∧ Body c (SWr c.A) v) := by
  obtain ⟨spro, blx, scopy, bli, laad, mad, lin, mct, slen, bll, sf, blf, scma, scml, bcml, sv, bcr, scr, blc, sa, bsk, sr, sca, scl, bcl, sepi, pop⟩ := dec_at
  obtain ⟨ez, em, er⟩ := verdict_effect s
  apply Reach.block (by have := hv.base4; omega) verdict decVerdictAt hp (by decide) sv (by decide)
    (by simp [alignedAll, verdict, Instr.accesses]) (ChaChaBlock.noWrites _ _ (by decide) _)
  generalize hu : execAll verdict s = u at ez em er
  have up : u.pc = c.base + BitVec.ofNat 32 decRejectBrAt := by
    rw [← hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have ub : Body c (SWr c.A) u := h.same em (er 13 (by decide) (by decide))
    (fun r a b => er r (by omega) (by omega))
  apply Reach.bcond (by have := hv.base4; omega) decRejectBrAt decRejectAt 1
    (brImm8 decRejectBrAt decRejectAt) up (by decide) bcr
    (by decide) (by decide +kernel)
  · intro hn
    have hn' : s.regs 3 ≠ 0#32 := by simpa [condPassed, ez] using hn
    exact False.elim (hn' (hz.mpr hok))
  · intro _
    apply Reach.done
    constructor
    · rw [M0Crypto.Armv6M.State.pc, setReg_eq]
      congr 1
    · exact ub.same rfl (setReg_ne _ _ _ _ (by decide))
        (fun r a b => setReg_ne _ _ _ _ (by rintro rfl; omega))

/-- Verdict, accepted-only decryption, both status paths, erasure and return. -/
theorem decrypt_tail (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decVerdictAt) (h : Body c (SWr c.A) s)
    (hz : s.regs 3=0#32 ↔ c.expected=c.tagB) (hlr : (c.regs0 14).getLsbD 0=true) :
    Reach c.base (DAllowed c) s (DecryptResult c) := by
  obtain ⟨spro, blx, scopy, bli, laad, mad, lin, mct, slen, bll, sf, blf, scma, scml, bcml, sv, bcr, scr, blc, sa, bsk, sr, sca, scl, bcl, sepi, pop⟩ := dec_at
  obtain ⟨ez, em, er⟩ := verdict_effect s
  apply Reach.block (by have := hv.base4; omega) verdict decVerdictAt hp (by decide) sv (by decide)
    (by simp [alignedAll, verdict, Instr.accesses]) (ChaChaBlock.noWrites _ _ (by decide) _)
  generalize hu : execAll verdict s=u at ez em er
  have up : u.pc=c.base+BitVec.ofNat 32 decRejectBrAt := by rw [←hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have ub : Body c (SWr c.A) u := h.same em (er 13 (by decide) (by decide))
    (fun r a b => er r (by omega) (by omega))
  apply Reach.bcond (by have := hv.base4; omega) decRejectBrAt decRejectAt 1 (brImm8 decRejectBrAt decRejectAt) up (by decide) bcr
    (by decide) (by decide +kernel)
  · intro hn
    have hbad : c.expected≠c.tagB := by
      have hn' : s.regs 3≠0#32 := by simpa [condPassed, ez] using hn
      exact fun e => hn' (hz.mpr e)
    generalize hv' : u.setReg 15 (c.base+BitVec.ofNat 32 decRejectAt)=v
    have vb : Body c (SWr c.A) v := ub.same (by rw [←hv']; rfl)
      (by rw [←hv', setReg_ne _ _ _ _ (by decide)])
      (fun r a b => by rw [←hv', setReg_ne _ _ _ _ (by rintro rfl; omega)])
    apply Reach.bind
    apply (status_reach c hv (DAllowed c) true decRejectAt sr (by decide) v
      (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq])).mono
    rintro w ⟨wp, w4, wm, wr⟩
    have wb : Body c (SWr c.A) w := vb.same wm (wr 13 (by decide) (by decide))
      (fun r a b => wr r (by omega) (by omega))
    apply decrypt_return c hv hb w wp _ hlr
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
    have reach := crypt_reach_narrow c hv hb decCryptAt (blImm (decCryptAt + cryptXorOff) xorOff) scr blc dec_calls.2.2.2.2
      (by decide) (by decide) v (by rw [←hv', M0Crypto.Armv6M.State.pc, setReg_eq, hfall]) vb.sp vb.high vb.nonce vb.frame
    apply Reach.bind
    apply (reach.monoW (fun y h => h.elim Or.inl (fun ho => Or.inr ⟨hok, ho⟩))).mono
    intro w hw
    have wb := vb.crypt hv hb hw
    have wf : ∀ y, ¬DWr c y → w.mem y=c.m0 y := by
      intro y hy
      rw [hw.keep y (fun o ho e => hy (.inl (e ▸ swr_lo c.A o ho)))
        (fun o ho e => hy (.inl (e ▸ swr_A c.A (4+o) (by omega)))) (fun h => hy (.inr h))]
      exact vb.frame y (fun h => hy (.inl h))
    apply Reach.bind
    apply (status_reach c hv (DAllowed c) false decAcceptAt sa (by decide) w hw.pc).mono
    rintro x ⟨xp, x4, xm, xr⟩
    apply Reach.b (by have := hv.base4; omega) decSkipAt decClrAAt (brImm11 decSkipAt decClrAAt) xp (by decide) bsk (by decide) (by decide)
    generalize hy : x.setReg 15 (c.base+BitVec.ofNat 32 decClrAAt)=y
    apply decrypt_return c hv hb y (by rw [←hy, M0Crypto.Armv6M.State.pc, setReg_eq]) _ hlr
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
theorem decrypt_compare_entry (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) :
    Reach c.base (DAllowed c) s (fun y =>
      y.pc = c.base + BitVec.ofNat 32 decCmpAAt ∧ Body c (SWr c.A) y ∧
      Ctx.bytesAt y.mem c.tag 16 = c.tagB ∧
      Ctx.bytesAt y.mem (c.A + 72#32) 16 = c.expected) := by
  obtain ⟨tx, ti', tl, tf, tc⟩ := dec_calls
  obtain ⟨spro, blx, scopy, bli, laad, mad, lin, mct, slen, bll, sf, blf, _⟩ := dec_at
  apply Reach.bind
  apply ((aead_setup c hv decOff (blImm (decOff + proXorOff) xorOff) (blImm (decOff + initCallOff) initOff)
    spro blx tx
    scopy bli ti' (by decide) (by decide) s he).monoW (fun _ h => .inl h)).mono
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  have aadU : Ctx.bytesAt u.mem c.aad c.alen.toNat=c.aadB :=
    bytesAt_congr (fun j hj => bu.frame _ (hv.not_swr hb.aadS hj))
  apply Reach.bind
  apply ((mac_phase c hv (SWr c.A) decLoadAadAt loadAad 0x24 0x25 rfl laad
    (blImm (decLoadAadAt + seqSize loadAad + macBlOff) blocksOff)
    (blImm (decLoadAadAt + seqSize loadAad + macBl2Off) blocksOff)
    mad (by decide) (by decide) u hu.pc c.aad c.alen hb.aadS bu.high.aad bu.high.alen bu u.mem [] pi
    (macWr_swr c.A)).monoW (fun _ h => .inl h)).mono
  intro v hv'
  have pv : PInv c.A u.mem (c.aadB++pad16 c.aadB) v.mem := by
    have h := hv'.inv; rw [aadU, List.nil_append] at h; exact h
  have inV : Ctx.bytesAt v.mem c.inp c.len.toNat=c.ptB :=
    bytesAt_congr (fun j hj => hv'.body.frame _ (hv.not_swr hb.inS hj))
  apply Reach.bind
  apply ((mac_phase c hv (SWr c.A) decLoadInAt loadIn 0x1c 0x1d rfl lin
    (blImm (decLoadInAt + seqSize loadIn + macBlOff) blocksOff)
    (blImm (decLoadInAt + seqSize loadIn + macBl2Off) blocksOff)
    mct (by decide) (by decide) v hv'.pc c.inp c.len hb.inS hv'.body.high.inp hv'.body.high.len hv'.body
    u.mem _ pv (macWr_swr c.A)).monoW (fun _ h => .inl h)).mono
  intro w hw
  have pw : PInv c.A u.mem ((c.aadB++pad16 c.aadB)++(c.ptB++pad16 c.ptB)) w.mem := by
    have h := hw.inv; rw [inV] at h; exact h
  apply Reach.bind
  apply ((lengths_reach c hv decLengthsAt (blImm (decLengthsAt + seqSize lengths) blocksOff) slen bll tl (by decide) (by decide)
    w hw.pc hw.body.sp hw.body.high hw.body.code u.mem _ pw).monoW
    (fun y h => .inl (macWr_swr _ y h))).mono
  intro x hx
  have bx := hw.body.lengths hv hx (macWr_swr c.A)
  have px : PInv c.A u.mem (macData c.aadB c.ptB) x.mem := by
    have h := hx.inv
    simpa only [macData, ACall.aadB, ACall.ptB, bytesAt_length, lengthBlock, List.append_assoc] using h
  apply Reach.bind
  apply ((finish_phase c hv hb true decFinDAt sf (blImm (decFinDAt + seqSize (finArgs true)) finishOff) blf tf (by decide) (by decide)
    x hx.pc bx.sp bx.high bx.code ic u hu.init hu.ictx hu.pkey _ px).monoW
    (fun y h => .inl (finishWr_swr _ y h))).mono
  intro y hy
  have yf : ∀ a, ¬SWr c.A a → y.mem a=c.m0 a := fun a ha =>
    (hy.frame a (fun h => ha (finishWr_swr _ a h))).trans (bx.frame a ha)
  have yb : Body c (SWr c.A) y := ⟨hy.sp,
    bx.high.congr (fun o a b => hy.frame _ (finish_not_A c hv hb true o b (.inr a))),
    (by rw [←bx.nonce]; exact read32_congr (fun k hk => hy.frame _ (finish_not_A c hv hb true k (by omega) (.inl (by omega))))),
    (fun r a b => (hy.hi r (by omega) b).trans (bx.hi r a b)), yf, hv.codeAt_of yf⟩
  have tagY : Ctx.bytesAt y.mem c.tag 16=c.tagB :=
    bytesAt_congr (fun j hj => yf _ (hv.not_swr hb.tagStack hj))
  apply Reach.done
  refine ⟨hy.pc, yb, tagY, ?_⟩
  exact hy.tagBytes

/-- Full checked-decryption run of the frozen machine code. -/
theorem decrypt_reach (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0=true) :
    Reach c.base (DAllowed c) s (DecryptResult c) := by
  apply Reach.bind
  apply (decrypt_compare_entry c hv hb s he).mono
  rintro y ⟨ypc, yb, tagY, tag⟩
  apply Reach.bind
  apply ((compare_reach c hv y ypc yb.sp yb.high).monoW (fun _ h => False.elim h)).mono
  rintro z ⟨zp, zm, zr, zeq⟩
  have zb := yb.same zm (zr 13 (by decide) (by decide)) (fun r a b => zr r (by omega) (by omega))
  apply decrypt_tail c hv hb z zp zb _ hlr
  rw [zeq, tagY, tag]
  exact eq_comm

/-- Checked-decryption theorem in the single-memory ARMv6-M model. -/
theorem decrypt_correct (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0=true)
    (hret : ∀ i<Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base+BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s=.ok (t,tr) ∧
      DecryptResult c t ∧ WritesTo (DAllowed c) tr := by
  apply Reach.runUntil (by rw [he.mem]; exact hv.code)
    (fun y hy i hi eq => by
      rw [B_len] at hi
      subst y
      rcases hy with h | ⟨_, h⟩
      · exact hv.code_not_swr hi h
      · exact not_out hb.codeO hi h)
    (fun i hi => hret i (by rwa [B_len] at hi))
  exact (decrypt_reach c hv hb s he hlr).mono fun t ht => ⟨ht.abi.pc, ht⟩

/-- Rejected calls write only the AEAD stack, including exact in-place calls. -/
theorem rejected_writes (c : ACall) (tr : List Event)
    (h : decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB=none)
    (hw : WritesTo (DAllowed c) tr) : WritesTo (SWr c.A) tr := by
  refine WritesTo.mono (Wr' := SWr c.A) hw ?_
  rintro y (hs | ⟨ha, _⟩)
  · exact hs
  · rw [decrypt_eq, if_pos ha] at h
    cases h

end M0Crypto.Release.Aead
