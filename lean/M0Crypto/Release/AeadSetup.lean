import M0Crypto.Release.AeadKey
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`AEAD_SETUP`, second half: copy the one-time key (first 32 bytes of block 0) from
`CTX` to `BLK` with two `ldm`/`stm` pairs, then `m0c_poly1305_init(CTX, BLK)`.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.ChaCha20 (block)

theorem lr3c : listRegs 60#8 = [2, 3, 4, 5] := by decide
theorem bc3c : bitCount 60#8 = 4 := by decide

/-- Four words from `A + a`. -/
def ws (m : Mem) (A : Word) (a : Nat) : List Word := (List.range 4).map fun i => read32 m (A + BitVec.ofNat 32 (a + 4 * i))

theorem ws_get (m : Mem) (A : Word) (a i : Nat) (hi : i < 4) :
    (ws m A a)[i]'(by simp [ws]; omega) = read32 m (A + BitVec.ofNat 32 (a + 4 * i)) := by
  simp [ws]

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5

theorem copy_mem (u : State) :
    (execAll copy u).mem = storeWords (storeWords u.mem (u.regs 13 + 72#32) (ws u.mem (u.regs 13) 8))
      (u.regs 13 + 88#32) (ws (storeWords u.mem (u.regs 13 + 72#32) (ws u.mem (u.regs 13) 8)) (u.regs 13) 24) := by
  simp [copy, execAll, Instr.next, Instr.exec, loadRegs, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lr3c, bc3c, BitVec.add_assoc]
  rfl

theorem copy_regs (u : State) :
    (execAll copy u).regs 0 = u.regs 13 + 8#32 ∧ (execAll copy u).regs 1 = u.regs 13 + 72#32 ∧
    (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → (execAll copy u).regs r = u.regs r) := by
  refine ⟨?_, ?_, fun r h6 h15 => ?_⟩
  · simp [copy, execAll, Instr.next, Instr.exec, loadRegs, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lr3c, bc3c, BitVec.add_assoc]
  · simp [copy, execAll, Instr.next, Instr.exec, loadRegs, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lr3c, bc3c, BitVec.add_assoc]
  · exact execAll_regs_other _ _ r h15 (by
      simp [copy, Instr.dsts, lr3c]; omega)

theorem byte_store (m : Mem) (A : Word) (vs : List Word) (a i k : Nat) (hi : i < vs.length) (hk : k < 4)
    (hl : vs.length ≤ 2 ^ 28) :
    storeWords m (A + BitVec.ofNat 32 a) vs (A + BitVec.ofNat 32 (a + 4 * i + k)) = vs[i].extractLsb' (8 * k) 8 := by
  rw [← ofNat_add_assoc A (a + 4 * i) k, byte_of_read32 (storeWords m (A + BitVec.ofNat 32 a) vs) _ k hk,
    rd_store_same _ _ _ a i hi hl]

theorem byte_word (m : Mem) (A : Word) (b k : Nat) (hk : k < 4) :
    (read32 m (A + BitVec.ofNat 32 b)).extractLsb' (8 * k) 8 = m (A + BitVec.ofNat 32 (b + k)) := by
  rw [← byte_of_read32 _ _ k hk, ofNat_add_assoc]

/-- The copy: `BLK` bytes `0..31` are `CTX` bytes `0..31`. -/
theorem copy_bytes (m : Mem) (A : Word) (j : Nat) (hj : j < 32) :
    storeWords (storeWords m (A + 72#32) (ws m A 8)) (A + 88#32) (ws (storeWords m (A + 72#32) (ws m A 8)) A 24)
      (A + BitVec.ofNat 32 (72 + j)) = m (A + BitVec.ofNat 32 (8 + j)) := by
  have hk := Nat.mod_lt j (show 4 > 0 by decide)
  by_cases h16 : j < 16
  · rw [storeWords_other _ _ _ _ (fun i q hi hq => by
      rw [ofNat_add_assoc, ofNat_add_assoc]; simp [ws] at hi; exact off_ne _ (by omega) (by omega) (by omega))]
    rw [show 72 + j = 72 + 4 * (j / 4) + j % 4 by omega, show (72#32 : Word) = BitVec.ofNat 32 72 from rfl]
    rw [byte_store _ _ _ 72 (j / 4) (j % 4) (by simp [ws]; omega) hk (by simp [ws]), ws_get _ _ _ _ (by omega),
      byte_word _ _ _ _ hk, show 8 + 4 * (j / 4) + j % 4 = 8 + j by omega]
  · rw [show 72 + j = 88 + 4 * ((j - 16) / 4) + (j - 16) % 4 by omega, show (88#32 : Word) = BitVec.ofNat 32 88 from rfl]
    have hk' := Nat.mod_lt (j - 16) (show 4 > 0 by decide)
    rw [byte_store _ _ _ 88 ((j - 16) / 4) ((j - 16) % 4) (by simp [ws]; omega) hk' (by simp [ws]),
      ws_get _ _ _ _ (by omega), rd_store_other _ _ _ 72 _ (by simp [ws]; omega) (by simp [ws]; omega),
      byte_word _ _ _ _ hk', show 24 + 4 * ((j - 16) / 4) + (j - 16) % 4 = 8 + j by omega]

theorem swr_sub {A : Word} (hA : 176 ≤ A.toNat) (hA' : A.toNat + 160 ≤ 2 ^ 32) (k o : Nat) (hk : k ≤ 176)
    (ho : o + 176 < 320 + k) : SWr A (A - BitVec.ofNat 32 k + BitVec.ofNat 32 o) := by
  refine Region.mk (o := 176 - k + o) (by omega) ?_
  apply BitVec.eq_of_toNat_eq
  have h1 : (A - BitVec.ofNat 32 k).toNat = A.toNat - k := by simp [BitVec.toNat_sub]; omega
  have h2 : (A - 176#32).toNat = A.toNat - 176 := by simp [BitVec.toNat_sub]; omega
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (a := 176 - k + o) (by omega)]
  congr 1; omega

/-- State after `AEAD_SETUP`, at `e + setupEnd`; `ic` is the `init` call. -/
structure SetupPost (c : ACall) (e : Nat) (ic : Poly1305Init.ICtx) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 (e + setupEnd)
  sp : t.regs 13 = c.A
  hi : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  ictx : ic.ctx = c.A + 8#32
  ikey : ic.key = c.A + 72#32
  isp : ic.sp0 = c.A
  ibase : ic.base = c.base
  init : Poly1305Init.IResult ic t
  pkey : Ctx.bytesAt ic.m0 ic.key 32 = M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB
  nonce : read32 t.mem c.A = c.nonce
  high : Hi c t.mem
  out : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y

theorem setup_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i : BitVec 25)
    (hseq : seqAt B (e + copyOff) copy = true) (hbl : instrAt B (e + initCallOff) = some (.bl i))
    (ht : blTarget (e + initCallOff) i = BitVec.ofNat 32 initOff) (he : e % 2 = 0) (hex : e + setupEnd ≤ Artifacts.Release.size)
    (u : State) (hu : XPost c e u)
    (hrc : InRegion Pc c.base (e + copyOff) (seqSize copy))
    (hrb : Pc (c.base + BitVec.ofNat 32 (e + initCallOff)))
    (hPi : ∀ pc, Poly1305Init.InitPc c.base pc → Pc pc) :
    ReachW c.base Pc (SWr c.A) u (fun t => ∃ ic, SetupPost c e ic t) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hA := hv.A_lo
  have hA' := hv.A_hi
  have hA4 : c.A.toNat % 8 = 0 := by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
  have aoff : ∀ k < 160, (c.A + BitVec.ofNat 32 k).toNat = c.A.toNat + k := hv.A_off
  apply ReachW.blockR hrc hb2 hu.pc (by have := copyOff_even; omega) hseq (by decide)
    (by
      simp [alignedAll, copy, Instr.accesses, wordAccesses, Access.aligned, Instr.next, Instr.exec, loadRegs,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lr3c, bc3c,
        BitVec.add_assoc, hu.sp]
      refine ⟨fun x _ => ?_, fun x _ => ?_, fun x _ => ?_, fun x _ => ?_⟩ <;> omega)
    (by
      intro e' he' y ⟨a, ha, hw, q, hq, hy⟩
      simp only [traceAll, copy, List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.accesses, wordAccesses, Instr.next, Instr.exec, loadRegs,
          M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lr3c, bc3c,
          BitVec.add_assoc, hu.sp] at ha hw
      all_goals (obtain ⟨x, hx, rfl⟩ := ha; simp only at hw hq hy)
      all_goals first
        | (rw [hy, ← BitVec.add_assoc, ofNat_add_assoc, ofNat_add_assoc]; exact swr_A _ _ (by omega))
        | cases hw)
  obtain ⟨v0, v1, vr⟩ := copy_regs u
  have vm := copy_mem u
  rw [hu.sp] at v0 v1 vm
  have vpc : (execAll copy u).pc = c.base + BitVec.ofNat 32 (e + initCallOff) := by
    have hend : e + copyOff + seqSize copy = e + initCallOff := by have := copyOff_end; omega
    rw [execAll_pc _ _ (by decide), hu.pc, ofNat_add_assoc, hend]
  generalize hv' : execAll copy u = v at v0 v1 vr vm vpc
  have vblk : ∀ j < 32, v.mem (c.A + BitVec.ofNat 32 (72 + j)) = (block c.keyB 0#32 c.nonceB)[j]! :=
    fun j hj => by rw [vm, copy_bytes _ _ j hj]; exact hu.ctx j (by omega)
  have vo : ∀ y, (∀ o, 72 ≤ o → o < 104 → y ≠ c.A + BitVec.ofNat 32 o) → v.mem y = u.mem y := fun y hy => by
    rw [vm, storeWords_other _ _ _ _ (fun i q hi hq => by
        rw [ofNat_add_assoc, ofNat_add_assoc]; simp [ws] at hi; exact hy _ (by omega) (by omega)),
      storeWords_other _ _ _ _ (fun i q hi hq => by
        rw [ofNat_add_assoc, ofNat_add_assoc]; simp [ws] at hi; exact hy _ (by omega) (by omega))]
  apply ReachW.blR hrb hb2 initOff i vpc (by have := initCallOff_even; omega) hbl
    (by have := initCallOff_ret; omega) ht
  generalize hw : (v.setReg 14 ((c.base + BitVec.ofNat 32 (e + initCallOff + 4)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 initOff) = w
  have wr : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → w.regs r = v.regs r := fun r a b => by
    rw [← hw, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have wm : w.mem = v.mem := by rw [← hw]; rfl
  have w14 : w.regs 14 = (c.base + BitVec.ofNat 32 (e + initCallOff + 4)) ||| 1#32 := by
    rw [← hw, setReg_ne _ _ _ _ (by decide), setReg_eq]
  have w15 : w.regs 15 = c.base + BitVec.ofNat 32 initOff := by rw [← hw, setReg_eq]
  have s12 : (c.A - BitVec.ofNat 32 12).toNat = c.A.toNat - 12 := hv.sub_toNat 12 (by omega)
  have a8 := aoff 8 (by decide)
  have a72 := aoff 72 (by decide)
  let ic : Poly1305Init.ICtx := { base := c.base, sp0 := c.A, ctx := c.A + 8#32, key := c.A + 72#32,
                                  m0 := w.mem, regs0 := w.regs }
  have iv : Poly1305Init.IValid ic := {
    base4 := hv.base4
    sp4 := by show c.A.toNat % 4 = 0; omega
    spLo := by show 12 ≤ c.A.toNat; omega
    ctx4 := by show (c.A + 8#32).toNat % 4 = 0; rw [a8]; omega
    key4 := by show (c.A + 72#32).toNat % 4 = 0; rw [a72]; omega
    codeS := hv.win hv.codeS 164 12 _ (by show (c.A - BitVec.ofNat 32 12).toNat = _; rw [s12]; omega) (by omega)
    codeC := hv.win hv.codeS 184 64 _ (by show (c.A + 8#32).toNat = _; rw [a8]; omega) (by omega)
    ctxS := by
      show Disj (c.A + 8#32) 64 (c.A - BitVec.ofNat 32 12) 12
      exact ⟨by rw [a8]; omega, by rw [s12]; omega, .inr (by rw [a8, s12]; omega)⟩
    keyS := by
      show Disj (c.A + 72#32) 32 (c.A - BitVec.ofNat 32 12) 12
      exact ⟨by rw [a72]; omega, by rw [s12]; omega, .inr (by rw [a72, s12]; omega)⟩
    keyC := by
      show Disj (c.A + 72#32) 32 (c.A + 8#32) 64
      exact ⟨by rw [a72]; omega, by rw [a8]; omega, .inr (by rw [a72, a8]; omega)⟩
    code := by
      show CodeAt w.mem c.base B
      rw [wm]
      exact hv.codeAt_of (fun y hy => by
        rw [vo y (fun o h1 h2 e => hy (e ▸ swr_A _ o (by omega))), hu.out y hy]) }
  have ie : Poly1305Init.IEntry ic w := {
    regs := rfl, mem := rfl
    pc := by show w.regs 15 = _; rw [w15]; rfl
    sp := by show w.regs 13 = c.A; rw [wr 13 (by decide) (by decide), vr 13 (by decide) (by decide), hu.sp]
    r0 := by show w.regs 0 = _; rw [wr 0 (by decide) (by decide), v0]
    r1 := by show w.regs 1 = _; rw [wr 1 (by decide) (by decide), v1] }
  have hlr : (ic.regs0 14).getLsbD 0 = true := by show (w.regs 14).getLsbD 0 = true; rw [w14]; exact lr_odd _
  have iw : ∀ y, Poly1305Init.IWr ic y → SWr c.A y := by
    rintro y (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩)
    · exact swr_sub hA hA' 12 o (by omega) (by omega)
    · show SWr c.A (c.A + 8#32 + BitVec.ofNat 32 o); rw [ofNat_add_assoc]; exact swr_A _ _ (by omega)
  apply ((Poly1305Init.init_reach_w ic iv iw w ie hlr).monoPc hPi).mono (fun _ _ h => h)
  intro t ht
  refine ⟨ic, ?_⟩
  have niw : ∀ o < 160, (o < 8 ∨ 72 ≤ o) → ¬ Poly1305Init.IWr ic (c.A + BitVec.ofNat 32 o) := by
    rintro o ho h (⟨o', ho', e'⟩ | ⟨o', ho', e'⟩)
    · exact ne_of_disj (a := c.A - BitVec.ofNat 32 12) (b := c.A) (n := 12) (m := 160)
        (by rw [s12]; omega) (by omega) (.inl (by rw [s12]; omega)) ho' ho e'.symm
    · have e2 : c.A + BitVec.ofNat 32 o = c.A + BitVec.ofNat 32 (8 + o') := by
        rw [e']; exact ofNat_add_assoc _ _ _
      exact off_ne _ (by omega) (by omega) (by omega) e2
  have tw : ∀ o < 160, (o < 8 ∨ 104 ≤ o) → t.mem (c.A + BitVec.ofNat 32 o) = u.mem (c.A + BitVec.ofNat 32 o) :=
    fun o ho h => by
      rw [ht.frame _ (niw o ho (by omega))]
      show w.mem _ = _
      rw [wm]; exact vo _ (fun o' a b => off_ne _ (by omega) (by omega) (by omega))
  refine ⟨?_, ht.sp, ?_, rfl, rfl, rfl, rfl, ht, ?_, ?_, hu.high.congr fun o h1 h2 => tw o h2 (.inr h1), ?_⟩
  · rw [ht.pc]; show w.regs 14 &&& ~~~1#32 = _
    have hset : e + initCallOff + 4 = e + setupEnd := by have := initCallOff_ret; omega
    rw [w14, lr_mask _ (even_off c.base hv.base4 (e + initCallOff + 4)
      (by have := initCallOff_even; omega)), hset]
  · intro r a b
    rw [ht.regs r (by omega) (by omega) (by omega) (by omega) (by omega)]
    show w.regs r = _
    rw [wr r (by omega) (by omega), vr r (by omega) (by omega), hu.hi r (by omega) b]
  · show Ctx.bytesAt w.mem (c.A + 72#32) 32 = _
    apply List.ext_getElem?
    intro j
    by_cases hj : j < 32
    · rw [Frame.bytesAt_get _ _ _ _ hj, wm, ofNat_add_assoc, vblk j hj]
      simp only [M0Crypto.Spec.Aead.polyKey, List.getElem?_take, hj, ite_true]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [ChaCha20Spec.block_length']; omega)]
      rfl
    · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega),
        List.getElem?_eq_none (by simp [M0Crypto.Spec.Aead.polyKey, ChaCha20Spec.block_length']; omega)]
  · rw [← hu.nonce]
    apply read32_congr
    intro k hk
    exact tw k (by omega) (.inl (by omega))
  · intro y hy
    rw [ht.frame y (fun h => hy (iw y h))]
    show w.mem y = _
    rw [wm, vo y (fun o a b e => hy (e ▸ swr_A _ o (by omega))), hu.out y hy]

/-- **`AEAD_SETUP`** from function entry at `e`, tracking the program-counter region `Pc`. -/
theorem aead_setup_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i0 i1 : BitVec 25)
    (hpro : seqAt B e pro = true) (hb0 : instrAt B (e + proXorOff) = some (.bl i0))
    (ht0 : blTarget (e + proXorOff) i0 = BitVec.ofNat 32 xorOff) (hcp : seqAt B (e + copyOff) copy = true)
    (hb1 : instrAt B (e + initCallOff) = some (.bl i1))
    (ht1 : blTarget (e + initCallOff) i1 = BitVec.ofNat 32 initOff)
    (he : e % 2 = 0) (hex : e + setupEnd ≤ Artifacts.Release.size) (s : State) (h : AEntry c e s)
    (hrp : InRegion Pc c.base e (seqSize pro))
    (hrx : Pc (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hrc : InRegion Pc c.base (e + copyOff) (seqSize copy))
    (hrb : Pc (c.base + BitVec.ofNat 32 (e + initCallOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (hPi : ∀ pc, Poly1305Init.InitPc c.base pc → Pc pc) :
    ReachW c.base Pc (SWr c.A) s (fun t => ∃ ic, SetupPost c e ic t) :=
  pro_reach_w c hv e hpro he s h hrp fun p hp =>
    ReachS.bind ((key_reach_w c hv e i0 hb0 ht0 he
        (by have := copyOff_end; have := initCallOff_ret; omega) p hp hrx hPc).mono (fun _ _ h => h)
      fun u hu => setup_reach_w c hv e i1 hcp hb1 ht1 he hex u hu hrc hrb hPi)

/-- **`AEAD_SETUP`** from function entry at `e` (encrypt or decrypt): the one-time key is
block 0 of ChaCha20 (RFC 8439 §2.6), copied to `BLK` and loaded into the Poly1305 context. -/
theorem aead_setup (c : ACall) (hv : AValid c) (e : Nat) (i0 i1 : BitVec 25)
    (hpro : seqAt B e pro = true) (hb0 : instrAt B (e + proXorOff) = some (.bl i0))
    (ht0 : blTarget (e + proXorOff) i0 = BitVec.ofNat 32 xorOff) (hcp : seqAt B (e + copyOff) copy = true)
    (hb1 : instrAt B (e + initCallOff) = some (.bl i1))
    (ht1 : blTarget (e + initCallOff) i1 = BitVec.ofNat 32 initOff)
    (he : e % 2 = 0) (hex : e + setupEnd ≤ Artifacts.Release.size) (s : State) (h : AEntry c e s) :
    Reach c.base (SWr c.A) s (fun t => ∃ ic, SetupPost c e ic t) :=
  (aead_setup_w (Pc := fun _ => True) c hv e i0 i1 hpro hb0 ht0 hcp hb1 ht1 he hex s h
    (fun _ _ => trivial) trivial (fun _ _ => trivial) trivial (fun _ _ => trivial) (fun _ _ => trivial)).toReach

end M0Crypto.Release.Aead
