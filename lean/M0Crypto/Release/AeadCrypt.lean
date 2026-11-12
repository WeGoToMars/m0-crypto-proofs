import M0Crypto.Release.ReachInv
import M0Crypto.Release.AeadSetup
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`CRYPT` at offset `off`: counter 1, then `m0c_chacha20_xor(out, in, len, key)`.
After it, `out` holds RFC 8439 ChaCha20 of the caller's input from counter 1.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (chacha20)

theorem ofNat_zero_add (A : Word) : A + BitVec.ofNat 32 0 = A := BitVec.add_zero A

theorem rd_wr_0 (m : Mem) (A v : Word) (a : Nat) (ha : a % 4 = 0) (ha0 : a ≠ 0) (ha' : a < 2 ^ 30) :
    read32 (write32 m (A + BitVec.ofNat 32 a) v) A = read32 m A := by
  have := rd_wr_ne m A v a 0 ha (by decide) ha' (by decide) ha0
  rwa [ofNat_zero_add] at this

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3

theorem crypt_effect (t : State) :
    (execAll crypt t).mem = write32 t.mem (t.regs 13 + 4#32) 1#32 ∧
    (execAll crypt t).regs 0 = read32 (execAll crypt t).mem (t.regs 13 + 104#32) ∧
    (execAll crypt t).regs 1 = read32 (execAll crypt t).mem (t.regs 13 + 112#32) ∧
    (execAll crypt t).regs 2 = read32 (execAll crypt t).mem (t.regs 13 + 116#32) ∧
    (execAll crypt t).regs 3 = read32 (execAll crypt t).mem (t.regs 13 + 152#32) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 15 →
      (execAll crypt t).regs r = t.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h15 => execAll_regs_other _ _ r h15
    (by simp [crypt, Instr.dsts, Fin.ext_iff, h0, h1, h2]; omega)⟩ <;>
  simp [crypt, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg]

/-- After `CRYPT`. -/
structure CryptPost (c : ACall) (off : Nat) (t u : State) : Prop where
  pc : u.pc = c.base + BitVec.ofNat 32 (off + cryptEnd)
  sp : u.regs 13 = c.A
  hi : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = t.regs r
  out : Ctx.bytesAt u.mem c.out c.len.toNat = chacha20 c.keyB 1 c.nonceB c.ptB
  keep : ∀ y, (∀ o < 176, y ≠ c.A - BitVec.ofNat 32 176 + BitVec.ofNat 32 o) →
    (∀ o < 4, y ≠ c.A + BitVec.ofNat 32 (4 + o)) → ¬ OutR c y → u.mem y = t.mem y

/-- CRYPT writes no tag bytes: its trace uses only stack and output. -/
def CryptWr (c : ACall) (y : Word) : Prop := SWr c.A y ∨ OutR c y

/-- Expose the ChaCha call state while retaining its functional continuation. -/
theorem crypt_reach_select_gen {Pn : Word → Prop} {P : State → Event → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (Q : State → Prop)
    (hrc : InRegion Pn c.base off (seqSize crypt))
    (hrx : Pn (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hP : ∀ x ev, RegionWrites Pn (CryptWr c) x ev → P x ev)
    (hcall : ∀ (xc : Ctx) (u : State), Valid xc → ChaCha20Setup.Entry xc u →
      (xc.regs0 14).getLsbD 0 = true → xc.base = c.base → xc.out = c.out → xc.len = c.len →
      xc.ctr = 1#32 → xc.sp0 = c.A → xc.regs0 14 &&& ~~~1#32 = c.base + BitVec.ofNat 32 (off + cryptEnd) →
      xc.inp = c.inp → xc.key = c.key → xc.nonce = c.nonce →
      ReachS c.base P u (fun v => v.pc = xc.regs0 14 &&& ~~~1#32 ∧ ChaCha20Xor.Result xc v))
    (hselect : ∀ (xc : Ctx) (u : State), Valid xc → ChaCha20Setup.Entry xc u →
      xc.base = c.base → xc.out = c.out → xc.len = c.len → xc.ctr = 1#32 →
      xc.inp = c.inp → xc.key = c.key → xc.nonce = c.nonce → xc.sp0 = c.A →
      ReachS c.base P u (CryptPost c off t) → ReachS c.base P u Q) :
    ReachS c.base P t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hA := hv.A_lo
  have hA' := hv.A_hi
  obtain ⟨cm, c0, c1, c2, c3, cr⟩ := crypt_effect t
  rw [t13] at cm c0 c1 c2 c3
  have H1 : Hi c (execAll crypt t).mem := thi.congr fun o h1 h2 => by
    rw [cm]; exact write32_other' _ _ _ _ (fun q hq => by
      rw [ofNat_add_assoc]; exact off_ne _ (by omega) (by omega) (by omega))
  rw [H1.out] at c0; rw [H1.inp] at c1; rw [H1.len] at c2; rw [H1.key] at c3
  apply ReachS.blockW hP hrc hb2 tpc ho hseq (by decide)
    (by
      have hA4 : c.A.toNat % 8 = 0 := by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
      simp [alignedAll, crypt, Instr.accesses, Access.aligned, Instr.next, Instr.exec,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.sp,
        M0Crypto.Armv6M.State.reg, t13, hv.A_off 4 (by decide), hv.A_off 104 (by decide),
        hv.A_off 112 (by decide), hv.A_off 116 (by decide), hv.A_off 152 (by decide)]
      omega)
    (by
      intro e he y ⟨a, ha, hw, q, hq, hy⟩
      simp only [traceAll, crypt, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Instr.accesses, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
          M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, t13] at ha
      all_goals (subst ha; simp only at hw hq hy)
      all_goals first
        | (left; rw [hy, ofNat_add_assoc]; exact swr_A _ _ (by omega))
        | cases hw)
  generalize hs1 : execAll crypt t = s1 at cm c0 c1 c2 c3 cr H1
  have p1 : s1.pc = c.base + BitVec.ofNat 32 (off + cryptXorOff) := by
    rw [← hs1, execAll_pc _ _ (by decide), tpc, ofNat_add_assoc]; rfl
  apply ReachS.blW hP hrx hb2 xorOff i p1 (by have := cryptXorOff_even; omega) hbl
    (by have := cryptXorOff_ret; omega) ht
  generalize hu : (s1.setReg 14 ((c.base + BitVec.ofNat 32 (off + cryptXorOff + 4)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 xorOff) = u
  have ur : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → u.regs r = s1.regs r := fun r a b => by
    rw [← hu, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have um : u.mem = s1.mem := by rw [← hu]; rfl
  have u14 : u.regs 14 = (c.base + BitVec.ofNat 32 (off + cryptXorOff + 4)) ||| 1#32 := by
    rw [← hu, setReg_ne _ _ _ _ (by decide), setReg_eq]
  have u15 : u.regs 15 = c.base := by rw [← hu, setReg_eq]; simp [xorOff_base]
  have umem : ∀ y, ¬ SWr c.A y → u.mem y = c.m0 y := fun y hy => by
    rw [um, cm, write32_other' _ _ _ _ (fun q hq e => hy (by rw [e, ofNat_add_assoc]; exact swr_A _ _ (by omega)))]
    exact tout y hy
  have fp_toNat : (c.A - BitVec.ofNat 32 176).toNat = c.A.toNat - 176 := hv.sub_toNat 176 (Nat.le_refl _)
  let xc : Ctx := { base := c.base, sp0 := c.A, out := c.out, inp := c.inp, len := c.len,
                    key := c.key, nonce := c.nonce, ctr := 1#32, m0 := u.mem, regs0 := u.regs }
  have xv : Valid xc := {
    base4 := hv.base4
    sp8 := by show c.A.toNat % 8 = 0; rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    spLo := hA
    codeF := hv.win (disj_mono hv.codeS (Nat.le_refl _)) 0 184 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega)
      (by omega)
    codeO := hb.codeO
    outF := hv.win hb.outS 0 184 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    inF := hv.win hb.inS 0 176 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    inOut := hb.inOut
    keyF := hv.win hv.keyS 0 176 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    nonceF := hv.win hv.nonceS 0 176 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    code := hv.codeAt_of umem }
  have xe : ChaCha20Setup.Entry xc u := {
    regs := rfl, mem := rfl, pc := u15
    sp := by show u.regs 13 = c.A; rw [ur 13 (by decide) (by decide), cr 13 (by decide) (by decide) (by decide)
      (by decide) (by decide), t13]
    r0 := by show u.regs 0 = _; rw [ur 0 (by decide) (by decide), c0]
    r1 := by show u.regs 1 = _; rw [ur 1 (by decide) (by decide), c1]
    r2 := by show u.regs 2 = _; rw [ur 2 (by decide) (by decide), c2]
    r3 := by show u.regs 3 = _; rw [ur 3 (by decide) (by decide), c3]
    argN := by show read32 u.mem c.A = _; rw [um, cm, rd_wr_0 _ _ _ 4 (by decide) (by decide) (by decide), tn]
    argC := by show read32 u.mem (c.A + 4#32) = _; rw [um, cm]; exact M0Crypto.Armv6M.read32_write32_same _ _ _ }
  have hrest : ReachS c.base P u (CryptPost c off t) := by
    have hlr : (xc.regs0 14).getLsbD 0 = true := by show (u.regs 14).getLsbD 0 = true; rw [u14]; exact lr_odd _
    have hretE : xc.regs0 14 &&& ~~~1#32 = c.base + BitVec.ofNat 32 (off + cryptEnd) := by
      show u.regs 14 &&& ~~~1#32 = _
      have hset : off + cryptXorOff + 4 = off + cryptEnd := by have := cryptXorOff_ret; omega
      rw [u14, lr_mask _ (even_off c.base hv.base4 (off + cryptXorOff + 4)
        (by have := cryptXorOff_even; omega)), hset]
    apply (hcall xc u xv xe hlr rfl rfl rfl rfl rfl hretE rfl rfl rfl).mono (fun _ _ h => h)
    rintro v ⟨vpc, hr⟩
    have hok : M0Crypto.Spec.Aead.counterOk xc.ctr.toNat xc.len.toNat = true := by
      show M0Crypto.Spec.Aead.counterOk (1#32 : Word).toNat c.len.toNat = true
      have := c.len.isLt
      simp [M0Crypto.Spec.Aead.counterOk]; omega
    have outD := hv.win hb.outS 0 176 (c.A - BitVec.ofNat 32 176) (by omega) (by omega)
    refine ⟨?_, hr.sp, ?_, ?_, ?_⟩
    · rw [vpc]; show u.regs 14 &&& ~~~1#32 = _
      have hset : off + cryptXorOff + 4 = off + cryptEnd := by have := cryptXorOff_ret; omega
      rw [u14, lr_mask _ (even_off c.base hv.base4 (off + cryptXorOff + 4)
        (by have := cryptXorOff_even; omega)), hset]
    · intro r a b
      rw [hr.callee r a b]; show u.regs r = _
      rw [ur r (by omega) (by omega), cr r (by omega) (by omega) (by omega) (by omega) (by omega)]
    · have kB : xc.keyB = c.keyB := bytesAt_congr (fun j hj => umem _ (hv.not_swr hv.keyS hj))
      have nB : xc.nonceB = c.nonceB := bytesAt_congr (fun j hj => umem _ (hv.not_swr hv.nonceS hj))
      have mB : xc.msg = c.ptB := bytesAt_congr (fun j hj => umem _ (hv.not_swr hb.inS hj))
      apply List.ext_getElem?
      intro j
      by_cases hj : j < c.len.toNat
      · rw [Frame.bytesAt_get _ _ _ _ hj]
        have hS : ChaCha20Xor.OutS xc (c.out + BitVec.ofNat 32 j) := Region.not fun o ho =>
          ne_of_disj outD.1 outD.2.1 outD.2.2 hj ho
        rw [hr.mem _ hS, if_pos ⟨hok, Region.mk hj rfl⟩, Ctx.oidx, show xc.out = c.out from rfl,
          sub_off _ _ (by have := c.len.isLt; omega)]
        show some ((chacha20 xc.keyB (1#32 : Word).toNat xc.nonceB xc.msg)[j]!) = _
        rw [kB, nB, mB, show (1#32 : Word).toNat = 1 from rfl]
        have hl : j < (chacha20 c.keyB 1 c.nonceB c.ptB).length := by
          rw [ChaCha20Spec.chacha20_length, ACall.ptB, bytesAt_length]; exact hj
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
      · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega), List.getElem?_eq_none (by
          rw [ChaCha20Spec.chacha20_length, ACall.ptB, bytesAt_length]; omega)]
    · intro y h1 h2 h3
      rw [hr.mem y (Region.not h1), if_neg (fun h => h3 h.2)]
      show u.mem y = _
      rw [um, cm, write32_other' _ _ _ _ (fun q hq e => h2 q hq (by rw [e, ofNat_add_assoc]))]
  exact hselect xc u xv xe rfl rfl rfl rfl rfl rfl rfl rfl hrest

/-- Expose the ChaCha call state while retaining its functional continuation. -/
theorem crypt_reach_select_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (Q : State → Prop)
    (hrc : InRegion Pc c.base off (seqSize crypt))
    (hrx : Pc (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (hselect : ∀ (xc : Ctx) (u : State), Valid xc → ChaCha20Setup.Entry xc u →
      xc.base = c.base → xc.out = c.out → xc.len = c.len → xc.ctr = 1#32 →
      xc.inp = c.inp → xc.key = c.key → xc.nonce = c.nonce → xc.sp0 = c.A →
      ReachW c.base Pc (CryptWr c) u (CryptPost c off t) → ReachW c.base Pc (CryptWr c) u Q) :
    ReachW c.base Pc (CryptWr c) t Q :=
  crypt_reach_select_gen c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout Q hrc hrx (fun _ _ h => h)
    (fun xc u xv xe hlr hbase hout hlen hctr hsp _ _ _ _ => by
      have wr : ∀ y, ChaCha20Xor.WrOk xc y → CryptWr c y := by
        rintro y (hs | ⟨_, hy⟩)
        · obtain ⟨o, ho, rfl⟩ := Region.exists hs
          have : xc.fp = c.A - BitVec.ofNat 32 176 := by simp [Ctx.fp, hsp, ChaCha20Layout.chStackBytes_eq]
          rw [this]; exact .inl (swr_lo c.A o ho)
        · exact .inr (by simpa only [Ctx.oidx, OutR, hout, hlen] using hy)
      have h := (ChaCha20Xor.xor_reach_w xc xv (fun pc h => hPc pc (hbase ▸ h)) u xe hlr).monoW wr
      rw [hbase] at h; exact h)
    hselect

theorem crypt_reach_select (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (Q : State → Prop)
    (hselect : ∀ (xc : Ctx) (u : State), Valid xc → ChaCha20Setup.Entry xc u →
      xc.base = c.base → xc.out = c.out → xc.len = c.len → xc.ctr = 1#32 →
      xc.inp = c.inp → xc.key = c.key → xc.nonce = c.nonce → xc.sp0 = c.A →
      Reach c.base (CryptWr c) u (CryptPost c off t) → Reach c.base (CryptWr c) u Q) :
    Reach c.base (CryptWr c) t Q :=
  (crypt_reach_select_w (Pc := fun _ => True) c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout Q
    (fun _ _ => trivial) trivial (fun _ _ => trivial)
    (fun xc u a b c1 c2 c3 c4 c5 c6 c7 c8 hr => (hselect xc u a b c1 c2 c3 c4 c5 c6 c7 c8 hr.toReach).toReachW)).toReach

/-- The encryption call reaches a valid ChaCha entry with the caller's
buffer and length, and retains a continuation to its functional postcondition. -/
theorem crypt_reaches_chacha (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0)
    (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A)
    (thi : Hi c t.mem) (tn : read32 t.mem c.A = c.nonce)
    (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y) :
    Reach c.base (CryptWr c) t (fun u => ∃ xc : Ctx,
      Valid xc ∧ ChaCha20Setup.Entry xc u ∧ xc.base = c.base ∧ xc.out = c.out ∧
      xc.len = c.len ∧ xc.ctr = 1#32 ∧ xc.inp = c.inp ∧ xc.key = c.key ∧
      xc.nonce = c.nonce ∧ xc.sp0 = c.A ∧ Reach c.base (CryptWr c) u (CryptPost c off t)) := by
  apply crypt_reach_select c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout
  intro xc u hv' he hb' ho' hl hc hi hk hn hs hr
  exact Reach.done ⟨xc, hv', he, hb', ho', hl, hc, hi, hk, hn, hs, hr⟩

theorem crypt_reach_narrow_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (hrc : InRegion Pc c.base off (seqSize crypt))
    (hrx : Pc (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) :
    ReachW c.base Pc (CryptWr c) t (CryptPost c off t) :=
  crypt_reach_select_w c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout _ hrc hrx hPc
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hrest => hrest)

theorem crypt_reach_narrow (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y) :
    Reach c.base (CryptWr c) t (CryptPost c off t) :=
  (crypt_reach_narrow_w (Pc := fun _ => True) c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout
    (fun _ _ => trivial) trivial (fun _ _ => trivial)).toReach

theorem crypt_reach (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y) :
    Reach c.base (AWr c) t (CryptPost c off t) :=
  (crypt_reach_narrow c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout).monoW
    (fun _ h => h.elim Or.inl (fun h' => Or.inr (Or.inl h')))

theorem crypt_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0) (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (hrc : InRegion Pc c.base off (seqSize crypt))
    (hrx : Pc (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) :
    ReachW c.base Pc (AWr c) t (CryptPost c off t) :=
  (crypt_reach_narrow_w c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout hrc hrx hPc).monoW
    (fun _ h => h.elim Or.inl (fun h' => Or.inr (Or.inl h')))

end M0Crypto.Release.Aead
