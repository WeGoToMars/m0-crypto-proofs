import M0Crypto.Release.AeadStoreSites

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Checked encryption under the output-store and tag-emit policy

`encrypt_reach_p`: the run of `encrypt_reach_w` with the step condition strengthened by `CPol`
(output-store instructions of the encrypting ChaCha call write the output) and by the tag-emit
policy (the sixteen stores of the finish emit block write only the tag).
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (OutputStorePC outputStoreOffset PCBetween)
open M0Crypto.Spec.Aead (pad16 macData encrypt chacha20)

/-- Output-store policy plus the tag-emit policy, with tag destination `tg`. -/
def PolE (c : ACall) (tg : Word) (Pc Wr : Word → Prop) (x : State) (e : Event) : Prop :=
  PolW c Pc Wr x e ∧
    (Poly1305Finish.EmitPc c.base e.pc → ∀ y, Writes e.accesses y → InFrame tg 4 y)

theorem PolE.monoW {c : ACall} {tg : Word} {Pc Wr Wr' : Word → Prop} (hw : ∀ y, Wr y → Wr' y)
    {x : State} {e : Event} (h : PolE c tg Pc Wr x e) : PolE c tg Pc Wr' x e :=
  ⟨PolW.monoW hw h.1, h.2⟩

theorem polE_of_free {c : ACall} {tg : Word} {Pn Pc Wr Wr' : Word → Prop}
    (hs : ∀ pc, Pn pc → ¬ OutputStorePC c.base pc) (hne : ∀ pc, Pn pc → ¬ Poly1305Finish.EmitPc c.base pc)
    (hPc : ∀ pc, Pn pc → Pc pc) (hw : ∀ y, Wr y → Wr' y) (x : State) (e : Event)
    (h : RegionWrites Pn Wr x e) : PolE c tg Pc Wr' x e :=
  ⟨polW_of_free hs hPc hw x e h, fun hem => absurd hem (hne _ h.1)⟩

/-- Program counters outside the finish emit block. -/
def NE (base : Word) (pc : Word) : Prop := EncAllPc base pc ∧ ¬ Poly1305Finish.EmitPc base pc

theorem polE_of_polW {c : ACall} {tg : Word} {Pc Wr : Word → Prop} (hPc : ∀ pc, NE c.base pc → Pc pc)
    {x : State} {e : Event} (h : PolW c (NE c.base) Wr x e) : PolE c tg Pc Wr x e :=
  ⟨⟨⟨hPc _ h.1.1, h.1.2⟩, h.2⟩, fun hem => absurd hem h.1.1.2⟩

/-- Program counters of the encrypt function and the Poly1305 routines other than finish. -/
def EncNon (base : Word) (pc : Word) : Prop :=
  PCBetween base encOff encEnd pc ∨ Poly1305Blocks.BlkPc base pc ∨ Poly1305Init.InitPc base pc

theorem encNon_all {base pc} (h : EncNon base pc) : EncAllPc base pc := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

theorem emit_lt : Poly1305Finish.clearAt ≤ 2 ^ 32 := by decide

theorem not_emit_of {base : Word} {o : Nat} (ho : o < 2 ^ 32)
    (h : o < Poly1305Finish.emitAt ∨ Poly1305Finish.clearAt ≤ o) : ¬ Poly1305Finish.EmitPc base (base + BitVec.ofNat 32 o) :=
  Poly1305Finish.not_pcBetween' ho emit_lt h

theorem encNon_not_emit (base : Word) : ∀ pc, EncNon base pc → ¬ Poly1305Finish.EmitPc base pc := by
  rintro pc (⟨o, h1, h2, rfl⟩ | ⟨o, h1, h2, rfl⟩ | ⟨o, h1, h2, rfl⟩)
  · exact not_emit_of (by have : encEnd < 2 ^ 32 := by decide
                          omega) (by
      have : Poly1305Finish.clearAt ≤ encOff ∨ encEnd ≤ Poly1305Finish.emitAt := by decide
      omega)
  · exact not_emit_of (by have : Poly1305Blocks.popAt + 2 < 2 ^ 32 := by decide
                          omega) (by
      have : Poly1305Finish.clearAt ≤ Poly1305Blocks.entryAt ∨ Poly1305Blocks.popAt + 2 ≤ Poly1305Finish.emitAt := by decide
      omega)
  · exact not_emit_of (by have : Poly1305Init.popAt + 2 < 2 ^ 32 := by decide
                          omega) (by
      have : Poly1305Finish.clearAt ≤ Poly1305Init.entryAt ∨ Poly1305Init.popAt + 2 ≤ Poly1305Finish.emitAt := by decide
      omega)

theorem cha_not_emit (base : Word) : ∀ pc, ChaCha20Policy.ChaPc base pc → ¬ Poly1305Finish.EmitPc base pc := by
  rintro pc ⟨o, h1, h2, rfl⟩
  exact not_emit_of (by have : ChaCha20Policy.chaEnd < 2 ^ 32 := by decide
                        omega) (by
    have : ChaCha20Policy.chaEnd ≤ Poly1305Finish.emitAt := by decide
    omega)

theorem encOwn_free : ∀ o, encOff ≤ o → o < encEnd → outputStoreOffset o = false := by
  have : ∀ o < encEnd, encOff ≤ o → outputStoreOffset o = false := by decide +kernel
  exact fun o h1 h2 => this o h2 h1

theorem encNon_free (base : Word) : ∀ pc, EncNon base pc → ¬ OutputStorePC base pc := by
  rintro pc (h | h | h)
  · exact noSite_between (by decide) encOwn_free pc h
  · exact noSite_between (by decide) (by
      have : ∀ o < Poly1305Blocks.popAt + 2, Poly1305Blocks.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
      exact fun o h1 h2 => this o h2 h1) pc h
  · exact noSite_between (by decide) (by
      have : ∀ o < Poly1305Init.popAt + 2, Poly1305Init.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
      exact fun o h1 h2 => this o h2 h1) pc h

theorem finPc_free (base : Word) : ∀ pc, Poly1305Finish.FinPc base pc → ¬ OutputStorePC base pc :=
  noSite_between (by decide) (by
    have : ∀ o < Poly1305Finish.popAt + 2, Poly1305Finish.entryAt ≤ o → outputStoreOffset o = false := by decide +kernel
    exact fun o h1 h2 => this o h2 h1)

/-- The finish call under the policy. -/
theorem finish_call_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (tag : Word) (off : Nat) (i : BitVec 25)
    (hbl : instrAt B off = some (.bl i)) (ht : blTarget off i = BitVec.ofNat 32 finishOff)
    (ho : off % 2 = 0) (hox : off + blSize ≤ Artifacts.Release.size)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off) (h13 : s.regs 13 = c.A)
    (h0 : s.regs 0 = c.A + 8#32) (h1 : s.regs 1 = tag) (hc : CodeAt s.mem c.base B)
    (hcodeT : Disj c.base Artifacts.Release.size tag 16) (htagS : Disj tag 16 (c.A - 20#32) 20)
    (ic : Poly1305Init.ICtx) (ti : State) (hi : Poly1305Init.IResult ic ti) (hctx : ic.ctx = c.A + 8#32)
    (hk : Ctx.bytesAt ic.m0 ic.key 32 = M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB)
    (msg : List M0Crypto.Spec.ChaCha20.Byte) (hp : PInv c.A ti.mem msg s.mem)
    (hrg : Pc (c.base + BitVec.ofNat 32 off))
    (hns : ¬ OutputStorePC c.base (c.base + BitVec.ofNat 32 off))
    (hne : ¬ Poly1305Finish.EmitPc c.base (c.base + BitVec.ofNat 32 off))
    (hfin : ∀ pc, Poly1305Finish.FinPc c.base pc → Pc pc) :
    ReachS c.base (PolE c tag Pc (FinishWr c.A tag)) s (FinishPost c tag off msg s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ReachS.blW (Pn := fun pc => pc = c.base + BitVec.ofNat 32 off)
    (fun x ev h => polE_of_free (Pc := Pc) (Wr' := FinishWr c.A tag) (fun pc h => by subst h; exact hns)
      (fun pc h => by subst h; exact hne) (fun pc h => by subst h; exact hrg) (fun _ h => h) x ev h)
    rfl hb2 finishOff i hpc ho hbl (by have := blSize_eq; omega) ht
  rw [show off + 4 = off + blSize by rw [blSize_eq]]
  generalize hx : (s.setReg 14 ((c.base + BitVec.ofNat 32 (off + blSize)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 finishOff) = x
  have xr : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → x.regs r = s.regs r := fun r a b => by
    rw [← hx, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have xm : x.mem = s.mem := by rw [← hx]; rfl
  have x14 : x.regs 14 = (c.base + BitVec.ofNat 32 (off + blSize)) ||| 1#32 := by
    rw [← hx, setReg_ne _ _ _ _ (by decide), setReg_eq]
  let fc : Poly1305Finish.FCtx := { base := c.base, sp0 := c.A, ctx := c.A + 8#32, tag := tag, m0 := x.mem, regs0 := x.regs }
  have fv : Poly1305Finish.FValid fc := {
    base4 := hv.base4
    sp8 := by show c.A.toNat % 8 = 0; rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    spLo := by change 20 ≤ c.A.toNat; have := hv.A_lo; omega
    ctx4 := by show (c.A + 8#32).toNat % 4 = 0; rw [hv.A_off 8 (by decide), hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    codeS := hv.win hv.codeS 156 20 _ (by show (c.A - 20#32).toNat = _; rw [hv.sub_toNat 20 (by decide)]; have := hv.A_lo; omega) (by decide)
    codeT := hcodeT
    ctxS := by
      change Disj (c.A + 8#32) 64 (c.A - 20#32) 20
      have := hv.A_lo; have := hv.A_hi
      rw [Disj, hv.A_off 8 (by decide), hv.sub_toNat 20 (by decide)]
      exact ⟨by omega, by omega, .inr (by omega)⟩
    tagS := htagS
    code := by change CodeAt x.mem c.base B; rw [xm]; exact hc }
  have fe : Poly1305Finish.FEntry fc x := ⟨rfl, rfl, by change x.regs 15 = c.base + BitVec.ofNat 32 finishOff; rw [← hx, setReg_eq],
    by change x.regs 13 = c.A; rw [xr 13 (by decide) (by decide), h13], by change x.regs 0 = c.A + 8#32; rw [xr 0 (by decide) (by decide), h0],
    by change x.regs 1 = tag; rw [xr 1 (by decide) (by decide), h1]⟩
  have hlr : (fc.regs0 14).getLsbD 0 = true := by show (x.regs 14).getLsbD 0 = true; rw [x14]; exact lr_odd _
  refine ReachS.mono (Poly1305Finish.finish_reach_p fc fv x fe hlr)
    (fun y ev h => ⟨⟨⟨hfin _ h.1.1, h.1.2⟩, fun hsite => absurd hsite (finPc_free c.base _ h.1.1)⟩, h.2⟩) ?_
  intro t ht'
  refine ⟨?_, ht'.sp, ?_, ?_, ?_⟩
  · rw [ht'.ret]; show x.regs 14 &&& ~~~1#32 = _
    rw [x14, lr_mask _ (even_off c.base hv.base4 _ (by have := blSize_eq; omega))]
  · intro r a b
    rw [ht'.callee r a b]; show x.regs r = _
    rw [xr r (by omega) (by omega)]
  · intro y hy
    rw [Poly1305Finish.result_frame fc x t fe ht' y hy]; exact congrFun xm y
  · have hh : fc.acc < 2 * M0Crypto.Spec.Aead.p := by
      rw [Poly1305Context.finish_acc]; change Poly1305Blocks.accAt x.mem (c.A + 8#32) < _
      rw [xm]; exact Poly1305Context.finish_bound _ hp.bound
    have tagval := Poly1305Finish.result_tag fc fv x t fe ht' hh
    rw [Poly1305Context.finish_acc, Poly1305Context.finish_pad] at tagval
    change Ctx.bytesAt t.mem tag 16 = M0Crypto.Spec.Aead.leBytes 16
      (Poly1305Blocks.accAt x.mem (c.A + 8#32) % _ + Poly1305Context.padAt x.mem (c.A + 8#32)) at tagval
    rw [xm] at tagval
    rw [tagval, ← hctx, Poly1305Context.poly1305_chain ic ti hi s.mem msg hp.len
      (by rw [hctx]; exact hp.pad) (by rw [hctx]; exact hp.acc), hk]

/-- Finish arguments plus the call, under the policy; the region is the encrypt function. -/
theorem finish_phase_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (dec : Bool) (off : Nat)
    (hseq : seqAt B off (finArgs dec) = true) (i : BitVec 25)
    (hbl : instrAt B (off + seqSize (finArgs dec)) = some (.bl i))
    (ht : blTarget (off + seqSize (finArgs dec)) i = BitVec.ofNat 32 finishOff)
    (ho : off % 2 = 0) (hx : off + seqSize (finArgs dec) + blSize ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 off) (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (hc : CodeAt s.mem c.base B)
    (ic : Poly1305Init.ICtx) (ti : State) (hi : Poly1305Init.IResult ic ti) (hctx : ic.ctx = c.A+8#32)
    (hk : Ctx.bytesAt ic.m0 ic.key 32 = M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB)
    (msg : List M0Crypto.Spec.ChaCha20.Byte) (hpi : PInv c.A ti.mem msg s.mem)
    (hrf : InRegion (PCBetween c.base encOff encEnd) c.base off (seqSize (finArgs dec)))
    (hrg : PCBetween c.base encOff encEnd (c.base + BitVec.ofNat 32 (off + seqSize (finArgs dec))))
    (hOwn : ∀ pc, PCBetween c.base encOff encEnd pc → Pc pc)
    (hfin : ∀ pc, Poly1305Finish.FinPc c.base pc → Pc pc) :
    ReachS c.base (PolE c (if dec then c.A+72#32 else c.tag) Pc (FinishWr c.A (if dec then c.A+72#32 else c.tag))) s
      (FinishPost c (if dec then c.A+72#32 else c.tag) (off + seqSize (finArgs dec)) msg s) := by
  have hfreeO : ∀ pc, PCBetween c.base encOff encEnd pc → ¬ OutputStorePC c.base pc :=
    noSite_between (by decide) encOwn_free
  have hneO : ∀ pc, PCBetween c.base encOff encEnd pc → ¬ Poly1305Finish.EmitPc c.base pc :=
    fun pc h => encNon_not_emit c.base pc (Or.inl h)
  have hPo : ∀ x ev, RegionWrites (PCBetween c.base encOff encEnd) (FinishWr c.A (if dec then c.A+72#32 else c.tag)) x ev →
      PolE c (if dec then c.A+72#32 else c.tag) Pc (FinishWr c.A (if dec then c.A+72#32 else c.tag)) x ev :=
    polE_of_free hfreeO hneO hOwn (fun _ h => h)
  obtain ⟨e0, e1, em, er⟩ := finArgs_effect dec s
  have hfa : seqSize (finArgs dec) = 4 := by cases dec <;> decide
  rw [hs] at e0 e1
  rw [hh.tag] at e1
  apply ReachS.blockW hPo hrf (by have := hv.base4; omega) hp ho hseq
    (by cases dec <;> rfl)
    (alignedAll_sp _ _ (sp_al (by cases dec <;> rfl))
      (by rw [hs, hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega))
    (WritesTo.of_noWritesMem _ _ (by cases dec <;> rfl) _)
  generalize hu : execAll (finArgs dec) s = u at e0 e1 em er
  have up : u.pc = c.base + BitVec.ofNat 32 (off + seqSize (finArgs dec)) := by
    rw [← hu, execAll_pc _ _ (by cases dec <;> rfl), hp, ofNat_add_assoc]
  have tagS : Disj (if dec then c.A+72#32 else c.tag) 16 (c.A-20#32) 20 := by
    cases dec
    · exact hv.win hb.tagS 156 20 _ (by rw [hv.sub_toNat 20 (by decide)]; have := hv.A_lo; omega) (by decide)
    · change Disj (c.A+72#32) 16 (c.A-20#32) 20
      have := hv.A_lo; have := hv.A_hi
      rw [Disj, hv.A_off 72 (by decide), hv.sub_toNat 20 (by decide)]
      exact ⟨by omega, by omega, .inr (by omega)⟩
  have codeT : Disj c.base Artifacts.Release.size (if dec then c.A+72#32 else c.tag) 16 := by
    cases dec
    · exact hb.codeT
    · change Disj c.base Artifacts.Release.size (c.A+72#32) 16
      exact hv.win hv.codeS 248 16 _ (by rw [hv.A_off 72 (by decide)]; have := hv.A_lo; omega) (by decide)
  apply (finish_call_p (Pc := Pc) c hv _ (off + seqSize (finArgs dec)) i hbl ht (by have := hfa; omega) (by omega) u up
    (by rw [er 13 (by decide) (by decide), hs]) e0 e1 (by rw [em]; exact hc)
    codeT tagS ic ti hi hctx hk msg (by rw [em]; exact hpi) (hOwn _ hrg) (hfreeO _ hrg) (hneO _ hrg) hfin).mono
    (fun _ _ h => h) (fun t ht' => ?_)
  exact ⟨ht'.pc, ht'.sp, fun r a b => (ht'.hi r a b).trans (er r (by omega) (by omega)),
    fun y hy => (ht'.frame y hy).trans (congrFun em y), ht'.tagBytes⟩

/-- Full encryption run of the frozen machine code under the output-store and tag-emit policies. -/
theorem encrypt_reach_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hPc : ∀ pc, EncAllPc c.base pc → Pc pc) :
    ReachS c.base (PolE c c.tag Pc (AWr c)) s (EncryptResult c) := by
  have hfreeN := encNon_free c.base
  have hnoE := encNon_not_emit c.base
  have hNE : ∀ pc, NE c.base pc → Pc pc := fun pc h => hPc pc h.1
  have lift : ∀ (x : State) (e : Event), PolW c (NE c.base) (AWr c) x e → PolE c c.tag Pc (AWr c) x e :=
    fun _ _ h => polE_of_polW hNE h
  have hPnN : ∀ pc, EncNon c.base pc → NE c.base pc := fun pc h => ⟨encNon_all h, hnoE pc h⟩
  have hE : ∀ pc, PCBetween c.base encOff encEnd pc → EncNon c.base pc := fun pc h => .inl h
  have hEO : ∀ pc, PCBetween c.base encOff encEnd pc → Pc pc := fun pc h => hPc pc (.inl h)
  have hEN : ∀ pc, PCBetween c.base encOff encEnd pc → NE c.base pc := fun pc h => hPnN pc (hE pc h)
  have hCha : ∀ pc, ChaCha20Policy.ChaPc c.base pc → NE c.base pc :=
    fun pc h => ⟨.inr (.inl h), cha_not_emit c.base pc h⟩
  have hBlk : ∀ pc, Poly1305Blocks.BlkPc c.base pc → EncNon c.base pc := fun pc h => .inr (.inl h)
  have hIni : ∀ pc, Poly1305Init.InitPc c.base pc → EncNon c.base pc := fun pc h => .inr (.inr h)
  have hFin : ∀ pc, Poly1305Finish.FinPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inr (.inr (.inr h))))
  obtain ⟨spro, blx, scopy, bli, scrypt, blc, laad, maat, lout, mcat, slen, bll, sf, blf,
    sca, scl, bcl, sepi, pop⟩ := enc_at
  obtain ⟨tx, ti', tc, tl, tf⟩ := enc_calls
  apply ReachS.bind
  apply (aead_setup_p (Pc := NE c.base) (Pn := EncNon c.base) c hv encOff (blImm (encOff + proXorOff) xorOff)
    (blImm (encOff + initCallOff) initOff) spro blx tx scopy bli ti' (by decide) (by decide) s he hfreeN hPnN
    (regionOf hE (by decide +kernel) (by decide +kernel)) (hPnN _ (pcOf hE (by decide +kernel) (by decide +kernel)))
    (not_outputStorePC (by decide) (by decide +kernel))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))
    hCha hIni).mono (fun _ _ h => lift _ _ (PolW.monoW (fun _ h => .inl h) h))
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  apply ReachS.bind
  apply (crypt_reach_p (Pc := NE c.base) c hv hb encCryptAt (blImm (encCryptAt + cryptXorOff) xorOff) scrypt blc tc
    (by decide) (by decide) u hu.pc hu.sp hu.high hu.nonce hu.out
    (regionOf hEN (by decide +kernel) (by decide +kernel)) (pcOf hEN (by decide +kernel) (by decide +kernel))
    (fun j hj => by
      have : ∀ j < seqSize crypt, outputStoreOffset (encCryptAt + j) = false := by decide +kernel
      exact not_outputStorePC (by have := (by decide : encCryptAt + seqSize crypt < 2 ^ 32); omega) (this j hj))
    (not_outputStorePC (by decide) (by decide +kernel))
    (not_pcBetween (by decide) (by decide) (Or.inr (by decide))) hCha).mono (fun _ _ h => lift _ _ (PolW.monoW (fun y h => h.elim Or.inl (fun o => Or.inr (Or.inl o))) h))
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
  apply (ReachW.toPol (Pc := NE c.base) (Wr' := AWr c) (mac_phase_w c hv (AWr c) encLoadAadAt loadAad 0x24 0x25 rfl laad _ _ maat (by decide) (by decide)
    v hv'.pc c.aad c.alen hb.aadS bv.high.aad bv.high.alen bv u.mem [] pv
    (fun y h => .inl (macWr_swr _ y h))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    hBlk) hfreeN hPnN (fun _ h => h)).mono (fun _ _ h => lift _ _ h)
  intro w hw
  have pw : PInv c.A u.mem (c.aadB ++ pad16 c.aadB) w.mem := by
    have h := hw.inv; rw [aadV, List.nil_append] at h; exact h
  have ctW : Ctx.bytesAt w.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB := by
    rw [← hv'.out]
    exact bytesAt_congr (fun j hj => hw.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply (ReachW.toPol (Pc := NE c.base) (Wr' := AWr c) (mac_phase_w c hv (AWr c) encLoadOutAt loadOut 0x1a 0x1d rfl lout _ _ mcat (by decide) (by decide)
    w hw.pc c.out c.len hb.outStack hw.body.high.out hw.body.high.len hw.body
    u.mem _ pw (fun y h => .inl (macWr_swr _ y h))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    hBlk) hfreeN hPnN (fun _ h => h)).mono (fun _ _ h => lift _ _ h)
  intro x hx
  let ct := chacha20 c.keyB 1 c.nonceB c.ptB
  have px : PInv c.A u.mem ((c.aadB ++ pad16 c.aadB) ++ (ct ++ pad16 ct)) x.mem := by
    have h := hx.inv; rw [ctW] at h; exact h
  have ctX : Ctx.bytesAt x.mem c.out c.len.toNat = ct := by
    change Ctx.bytesAt x.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB
    rw [← ctW]
    exact bytesAt_congr (fun j hj => hx.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply (ReachW.toPol (Pc := NE c.base) (Wr' := AWr c) ((lengths_reach_w c hv encLengthsAt _ slen bll tl (by decide) (by decide)
    x hx.pc hx.body.sp hx.body.high hx.body.code u.mem _ px
    (regionOf hE (by decide +kernel) (by decide +kernel)) hBlk).monoW
    (fun y h => .inl (macWr_swr _ y h))) hfreeN hPnN (fun _ h => h)).mono (fun _ _ h => lift _ _ h)
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
  apply (finish_phase_p (Pc := Pc) c hv hb false encFinEAt sf _ blf tf (by decide) (by decide)
    y hy.pc by'.sp by'.high by'.code ic u hu.init hu.ictx hu.pkey _ plen
    (regionOf (fun _ h => h) (by decide +kernel) (by decide +kernel)) (by exact ⟨_, by decide +kernel, by decide +kernel, rfl⟩)
    hEO hFin).mono (fun _ _ h => PolE.monoW (finishWr_awr c) h)
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
        refine ⟨156+q, by omega, ?_⟩
        rw [eq, BitVec.ofNat_add, ← BitVec.add_assoc]; congr 1; bv_omega)
    · exact ne_of_disj hb.tagO.2.1 hb.tagO.1 (Or.symm hb.tagO.2.2) hj hq eq
  have zframe : ∀ a, ¬ AWr c a → z.mem a = c.m0 a := fun a ha =>
    (hz.frame a (fun h => ha (finishWr_awr c a h))).trans (by'.frame a ha)
  apply ReachS.bind
  apply (ReachW.toPol (Pc := NE c.base) (Wr' := AWr c) ((clear_reach_w c.base c.A encClrAAt sca scl bcl hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega) (by decide) (by decide) z hz.pc hz.sp
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    (pcOf hE (by decide +kernel) (by decide +kernel))).monoW
    (fun a h => .inl (clearWr_swr _ a h))) hfreeN hPnN (fun _ h => h)).mono (fun _ _ h => lift _ _ h)
  intro q hq
  have qh : Hi c q.mem := zh.congr (fun o a b => hq.frame _ (by
    rintro ⟨j, hj, eq⟩
    exact off_ne c.A (a := o) (b := 8+j) (by omega) (by omega) (by omega) eq))
  have qs : q.regs 13 = c.A := by rw [hq.hi 13 (by decide) (by decide), hz.sp]
  have qr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → q.regs r = c.regs0 r :=
    fun r a b => (hq.hi r (by omega) (by omega)).trans (zr r a b)
  apply (ReachW.toPol (Pc := NE c.base) (Wr' := AWr c) (epilogue_reach_w c hv (AWr c) false encEpiAt sepi pop (by decide) (by decide) q hq.pc qs qh qr hlr
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))) hfreeN hPnN (fun _ h => h)).mono
    (fun _ _ h => lift _ _ h)
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
