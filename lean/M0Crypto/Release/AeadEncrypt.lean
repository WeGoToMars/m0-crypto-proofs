import M0Crypto.Release.AeadWindow
import M0Crypto.Release.AeadCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (pad16 macData encrypt chacha20)

theorem out_not_mac {c : ACall} (hv : AValid c) (hb : ABuf c) {j : Nat} (hj : j < c.len.toNat) :
    ¬ MacWr c.A (c.out + BitVec.ofNat 32 j) :=
  fun h => hv.not_swr hb.outStack hj (macWr_swr _ _ h)

/-- Program counters of the encrypt function and of every routine it calls. -/
def EncAllPc (base : Word) (pc : Word) : Prop :=
  M0Crypto.Release.ConstantTime.PCBetween base encOff encEnd pc ∨ ChaCha20Policy.ChaPc base pc ∨
    Poly1305Blocks.BlkPc base pc ∨ Poly1305Init.InitPc base pc ∨ Poly1305Finish.FinPc base pc

/-- Full encryption run of the frozen machine code, in composable form, with r12 and the stack
window at return. -/
theorem encrypt_win_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hPc : ∀ pc, EncAllPc c.base pc → Pc pc) :
    ReachW c.base Pc (AWr c) s (fun t => EncryptResult c t ∧ t.regs 12 = 0#32 ∧
      Ctx.bytesAt t.mem (c.sp0 - 320#32) 320 =
        encWindow c.regs0 c.nonce (Ctx.bytesAt c.m0 (c.sp0 - 320#32) 320)) := by
  have hE : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween c.base encOff encEnd pc → Pc pc := fun pc h => hPc pc (.inl h)
  have hCha : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inl h))
  have hBlk : ∀ pc, Poly1305Blocks.BlkPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inr (.inl h)))
  have hIni : ∀ pc, Poly1305Init.InitPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inr (.inr (.inl h))))
  have hFin : ∀ pc, Poly1305Finish.FinPc c.base pc → Pc pc := fun pc h => hPc pc (.inr (.inr (.inr (.inr h))))
  obtain ⟨spro, blx, scopy, bli, scrypt, blc, laad, maat, lout, mcat, slen, bll, sf, blf,
    sca, scl, bcl, sepi, pop⟩ := enc_at
  obtain ⟨tx, ti', tc, tl, tf⟩ := enc_calls
  apply ReachS.bind
  apply ((aead_setup_w c hv encOff (blImm (encOff + proXorOff) xorOff) (blImm (encOff + initCallOff) initOff)
    spro blx tx scopy bli ti' (by decide) (by decide) s he
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))
    hCha hIni).monoW
    (fun _ h => .inl h)).mono (fun _ _ h => h)
  rintro u ⟨ic, hu⟩
  have bu := hu.body hv
  have pi := PInv.init c.A ic u hu.init hu.ictx
  apply ReachS.bind
  apply (crypt_reach_w c hv hb encCryptAt (blImm (encCryptAt + cryptXorOff) xorOff) scrypt blc tc (by decide) (by decide)
    u hu.pc hu.sp hu.high hu.nonce hu.out
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))
    hCha).mono (fun _ _ h => h)
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
  apply (mac_phase_win_w c hv (AWr c) encLoadAadAt loadAad 0x24 0x25 rfl laad _ _ maat (by decide) (by decide)
    v hv'.pc c.aad c.alen hb.aadS bv.high.aad bv.high.alen bv u.mem [] pv
    (fun y h => .inl (macWr_swr _ y h))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    hBlk).mono (fun _ _ h => h)
  rintro w ⟨hw, -, hw7⟩
  have pw : PInv c.A u.mem (c.aadB ++ pad16 c.aadB) w.mem := by
    have h := hw.inv; rw [aadV, List.nil_append] at h; exact h
  have ctW : Ctx.bytesAt w.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB := by
    rw [← hv'.out]
    exact bytesAt_congr (fun j hj => hw.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply (mac_phase_win_w c hv (AWr c) encLoadOutAt loadOut 0x1a 0x1d rfl lout _ _ mcat (by decide) (by decide)
    w hw.pc c.out c.len hb.outStack hw.body.high.out hw.body.high.len hw.body
    u.mem _ pw (fun y h => .inl (macWr_swr _ y h))
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    hBlk).mono (fun _ _ h => h)
  rintro x ⟨hx, hxR, hx7⟩
  let ct := chacha20 c.keyB 1 c.nonceB c.ptB
  have px : PInv c.A u.mem ((c.aadB ++ pad16 c.aadB) ++ (ct ++ pad16 ct)) x.mem := by
    have h := hx.inv; rw [ctW] at h; exact h
  have ctX : Ctx.bytesAt x.mem c.out c.len.toNat = ct := by
    change Ctx.bytesAt x.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB
    rw [← ctW]
    exact bytesAt_congr (fun j hj => hx.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply ((lengths_win_w c hv encLengthsAt _ slen bll tl (by decide) (by decide)
    x hx.pc hx.body.sp hx.body.high hx.body.code u.mem _ px
    (regionOf hE (by decide +kernel) (by decide +kernel)) hBlk).monoW
    (fun y h => .inl (macWr_swr _ y h))).mono (fun _ _ h => h)
  rintro y ⟨hy, hyL, hyS⟩
  have by' := hx.body.lengths hv hy (fun y h => .inl (macWr_swr _ y h))
  have plen : PInv c.A u.mem (macData c.aadB ct) y.mem := by
    have h := hy.inv
    have hl : ct.length = c.len.toNat := by rw [ChaCha20Spec.chacha20_length, ACall.ptB, bytesAt_length]
    simpa only [macData, ACall.aadB, bytesAt_length, lengthBlock, hl, List.append_assoc] using h
  have ctY : Ctx.bytesAt y.mem c.out c.len.toNat = ct := by
    rw [← ctX]
    exact bytesAt_congr (fun j hj => hy.frame _ (out_not_mac hv hb hj))
  apply ReachS.bind
  apply ((finish_phase_win_w c hv hb false encFinEAt sf _ blf tf (by decide) (by decide)
    y hy.pc by'.sp by'.high by'.code ic u hu.init hu.ictx hu.pkey _ plen
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))
    hFin).monoW
    (finishWr_awr c)).mono (fun _ _ h => h)
  rintro z ⟨hz, hzS, hz12⟩
  have zh : Hi c z.mem := by'.high.congr (fun o a b => hz.frame _ (finish_not_A c hv hb false o b (.inr a)))
  have zr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → z.regs r = c.regs0 r :=
    fun r a b => (hz.hi r (by omega) b).trans (by'.hi r a b)
  have ctZ : Ctx.bytesAt z.mem c.out c.len.toNat = ct := by
    rw [← ctY]
    apply bytesAt_congr
    intro j hj
    apply hz.frame
    rintro (⟨q, hq, eq⟩ | ⟨q, hq, eq⟩)
    · exact hv.not_swr hb.outStack hj (finishWr_swr c.A _ (.inl ⟨q, hq, eq⟩))
    · exact ne_of_disj hb.tagO.2.1 hb.tagO.1 (Or.symm hb.tagO.2.2) hj hq eq
  have zframe : ∀ a, ¬ AWr c a → z.mem a = c.m0 a := fun a ha =>
    (hz.frame a (fun h => ha (finishWr_awr c a h))).trans (by'.frame a ha)
  apply ReachS.bind
  apply ((clear_reach_w c.base c.A encClrAAt sca scl bcl hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega) (by decide) (by decide) z hz.pc hz.sp
    (regionOf hE (by decide +kernel) (by decide +kernel)) (regionOf hE (by decide +kernel) (by decide +kernel))
    (pcOf hE (by decide +kernel) (by decide +kernel))).monoW
    (fun a h => .inl (clearWr_swr _ a h))).mono (fun _ _ h => h)
  intro q hq
  have qh : Hi c q.mem := zh.congr (fun o a b => hq.frame _ (by
    rintro ⟨j, hj, eq⟩
    exact off_ne c.A (a := o) (b := 8+j) (by omega) (by omega) (by omega) eq))
  have qs : q.regs 13 = c.A := by rw [hq.hi 13 (by decide) (by decide), hz.sp]
  have qr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → q.regs r = c.regs0 r :=
    fun r a b => (hq.hi r (by omega) (by omega)).trans (zr r a b)
  apply (epilogue_win_w c hv (AWr c) false encEpiAt sepi pop (by decide) (by decide) q hq.pc qs qh qr hlr
    (regionOf hE (by decide +kernel) (by decide +kernel)) (pcOf hE (by decide +kernel) (by decide +kernel))).mono
    (fun _ _ h => h)
  rintro t ⟨ht, tm, t12⟩
  refine ⟨⟨ht, ?_, ?_, ?_, ?_⟩, by rw [t12, hq.hi 12 (by decide) (by decide), hz12], ?_⟩
  rotate_left 4
  · -- the stack window: words below `A` from the callee calls, the rest from the clear and `Hi`
    have nf : ∀ o, o < 156 → ¬ FinishWr c.A (if false = true then c.A + 72#32 else c.tag)
        (c.A - 176#32 + BitVec.ofNat 32 o) := fun o ho => finishWr_X hv hb false o (.inl ho)
    have zLow : ∀ o < 140, z.mem (c.A - 176#32 + BitVec.ofNat 32 o) = 0#8 := by
      intro o ho
      rw [hz.frame _ (nf o (by omega))]
      by_cases h112 : o < 112
      · rw [hy.frame _ (macWr_X hv o (.inl h112)), hx.frame _ (macWr_X hv o (.inl h112)),
          hw.frame _ (macWr_X hv o (.inl h112))]
        exact hv'.low o ho (hu.low o ho)
      · obtain ⟨k, rfl⟩ : ∃ k, o = 112 + k := ⟨o - 112, by omega⟩
        rw [X_64]; exact hyL k (by omega)
    have xr7 : x.regs 7 = c.regs0 7 := by
      rw [hx7, hw7, hv'.hi 7 (by decide) (by decide), hu.r7]
    have zSv : ∀ i < 9, read32 z.mem (c.A - 176#32 + BitVec.ofNat 32 (140 + 4 * i)) =
        (encLow9 c.regs0).getD i 0#32 := by
      intro i hi
      by_cases h4 : i < 4
      · rw [read32_congr (m := y.mem) (fun k hk => by rw [ofNat_add_assoc]; exact hz.frame _ (nf _ (by omega))),
          X_slot64, hyS i h4]
        have r := hx.body.hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
          simp only [Frame.saved, encLow9] <;> rw [r _ (by decide) (by decide)] <;> rfl
      · obtain ⟨j, rfl⟩ : ∃ j, i = 4 + j := ⟨i - 4, by omega⟩
        rw [X_slot20, hzS j (by omega)]
        have r := hy.hi
        obtain ⟨x4, x5, x6⟩ := hxR
        have pc0 : c.regs0 15 - BitVec.ofNat 32 encOff = c.base := by
          rw [he.pc, BitVec.add_sub_cancel]
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
        · simp only [encLow9, List.getD_cons_succ, List.getD_cons_zero]
          rw [r 4 (by decide) (by decide), x4, he.r0, he.r3]
        · simp only [encLow9, List.getD_cons_succ, List.getD_cons_zero]
          rw [r 5 (by decide) (by decide), x5, he.r3]
        · simp only [encLow9, List.getD_cons_succ, List.getD_cons_zero]
          rw [r 6 (by decide) (by decide), x6, he.r3]
        · simp only [encLow9, List.getD_cons_succ, List.getD_cons_zero]
          rw [r 7 (by decide) (by decide), xr7]
        · simp only [encLow9, List.getD_cons_succ, List.getD_cons_zero]
          rw [pc0]
    have zA : ∀ k < 8, z.mem (c.A + BitVec.ofNat 32 k) = v.mem (c.A + BitVec.ofNat 32 k) := by
      intro k hk
      rw [hz.frame _ (finish_not_A c hv hb false k (by omega) (.inl hk)),
        hy.frame _ (mac_not_A c.A k (by omega) (.inl hk)), hx.frame _ (mac_not_A c.A k (by omega) (.inl hk)),
        hw.frame _ (mac_not_A c.A k (by omega) (.inl hk))]
    have zn : read32 z.mem c.A = c.nonce := by
      rw [← hx.body.nonce]
      refine read32_congr (fun k hk => ?_)
      have e : c.A = c.A + BitVec.ofNat 32 0 := (BitVec.add_zero _).symm
      rw [e, ofNat_add_assoc, hz.frame _ (finish_not_A c hv hb false _ (by omega) (.inl (by omega))),
        hy.frame _ (mac_not_A c.A _ (by omega) (.inl (by omega)))]
    have zc : read32 z.mem (c.A + 4#32) = 1#32 := by
      rw [← hv'.ctr]
      refine read32_congr (fun k hk => ?_)
      rw [show c.A + 4#32 = c.A + BitVec.ofNat 32 4 from rfl, ofNat_add_assoc, zA _ (by omega)]
    rw [tm]
    exact window_eq hv he 1#32 (encLow9 c.regs0) hq.frame hq.zero zLow zSv zn zc zh
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

/-- Full encryption run of the frozen machine code, in composable form. -/
theorem encrypt_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hPc : ∀ pc, EncAllPc c.base pc → Pc pc) :
    ReachW c.base Pc (AWr c) s (EncryptResult c) :=
  (encrypt_win_w c hv hb s he hlr hPc).mono (fun _ _ h => h) (fun _ h => h.1)

theorem encrypt_reach (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base (AWr c) s (EncryptResult c) :=
  (encrypt_reach_w (Pc := fun _ => True) c hv hb s he hlr (fun _ _ => trivial)).toReach

/-- Encryption theorem in the single-memory ARMv6-M model, with r12 and the stack window. -/
theorem encrypt_win (c : ACall) (s : State) (hp : APre c encOff s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      (EncryptResult c t ∧ t.regs 12 = 0#32 ∧
        Ctx.bytesAt t.mem (c.sp0 - 320#32) 320 =
          encWindow c.regs0 c.nonce (Ctx.bytesAt c.m0 (c.sp0 - 320#32) 320)) ∧
      WritesTo (AWr c) tr := by
  obtain ⟨hv, hb, he, hlr, hret⟩ := hp
  replace hret := Region.ne hret
  apply Reach.runUntil (by rw [he.mem]; exact hv.code)
    (fun y hy i hi eq => by
      rw [B_len] at hi
      subst y
      rcases hy with h | h | h
      · exact hv.code_not_swr hi h
      · exact not_out hb.codeO hi h
      · exact not_tag hb.codeT hi h)
    (fun i hi => hret i (by rwa [B_len] at hi))
  exact (encrypt_win_w (Pc := fun _ => True) c hv hb s he hlr (fun _ _ => trivial)).toReach.mono
    fun t ht => ⟨ht.1.pc, ht⟩

/-- Every valid call returns with `EncryptResult`; see `encrypt_correct` for the window. -/
theorem encrypt_returns (c : ACall) (s : State) (hp : APre c encOff s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      EncryptResult c t ∧ WritesTo (AWr c) tr :=
  let ⟨n, hn⟩ := encrypt_win c s hp
  ⟨n, fun fuel hf => let ⟨t, tr, h1, h2, h3⟩ := hn fuel hf; ⟨t, tr, h1, h2.1, h3⟩⟩

/-- Encryption theorem in the single-memory ARMv6-M model. -/
theorem encrypt_correct : EncryptCorrect :=
  ⟨encWindow, fun c s hp =>
    let ⟨n, hn⟩ := encrypt_win c s hp
    ⟨n, fun fuel hf => let ⟨t, tr, h1, ⟨h2, h3, h4⟩, h5⟩ := hn fuel hf; ⟨t, tr, h1, h2, h5, h3, h4⟩⟩⟩

end M0Crypto.Release.Aead
