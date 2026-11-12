import M0Crypto.Release.Blake2sUpdateLoop
import M0Crypto.Release.Blake2sFinalReach
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the epilogue (`str used; movs r0..r3, #0; add sp; pop`) -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sFinal (Stk stk_M1 Stk.of pop_eff addSp_eff zero_eff b240)

/-- Distinct small offsets from one base are distinct addresses. -/
theorem cne (c : Word) {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (h : x ≠ y) :
    c + BitVec.ofNat 32 x ≠ c + BitVec.ofNat 32 y := by
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := c.isLt
  omega

/-- Writing the `used` field to the buffer length completes the context. -/
theorem used_write (c : Word) {m : Mem} {st : SState} (h : CtxNU m c st) :
    Ctx (write32 m (c + 104#32) (BitVec.ofNat 32 st.pending.length)) c st := by
  have key : ∀ j, j + 4 ≤ 104 →
      read32 (write32 m (c + 104#32) (BitVec.ofNat 32 st.pending.length)) (c + BitVec.ofNat 32 j) =
        read32 m (c + BitVec.ofNat 32 j) := by
    intro j hj
    apply read32_congr
    intro q hq
    rw [ofNat_add_assoc]
    apply write32_other'
    intro k hk he
    rw [show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc] at he
    exact cne c (by omega) (by omega) (by omega) he
  refine ⟨⟨h.hsz, fun i hi => ?_, ?_, ?_, h.cnt, h.plen, ?_⟩, ?_⟩
  · rw [key (4 * i) (by omega)]; exact h.h i hi
  · rw [show (32#32 : Word) = BitVec.ofNat 32 32 from rfl, key 32 (by omega)]; exact h.clo
  · rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, key 36 (by omega)]; exact h.chi
  · have hp := h.plen
    refine Eq.trans ?_ h.buf
    apply bytesAt_congr
    intro i hi
    rw [show (40#32 : Word) = BitVec.ofNat 32 40 from rfl, ofNat_add_assoc]
    apply write32_other'
    intro k hk he
    rw [show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc] at he
    exact cne c (by omega) (by omega) (by omega) he
  · exact M0Crypto.Armv6M.read32_write32_same m _ _

theorem fb_off (s : State) (o : Nat) : s.regs 13 - 20#32 + BitVec.ofNat 32 o = fb s + BitVec.ofNat 32 (STREAM_LOCALS + o) := by
  rw [← ofNat_add_assoc]; unfold fb; bv_omega

/-- The pushed words are still in place at the end of the loop. -/
theorem push_mem {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState} (hI : Inv s st0 t k st) (o : Nat) (ho : o < 20) :
    t.mem (s.regs 13 - 20#32 + BitVec.ofNat 32 o) = pm s (s.regs 13 - 20#32 + BitVec.ofNat 32 o) := by
  have hn := (s.regs 13).isLt
  have hlo := e.spLo
  apply hI.ag
  · intro j hj he
    rw [fb_off] at he
    exact disj_ne e.cF (i := j) (o := STREAM_LOCALS + o) hj (by omega) he.symm
  · intro j hj he
    rw [fb_off] at he
    exact cne (fb s) (by omega) (by omega) (by omega) he.symm

/-- The effect of `str r7, [r4, #104]; movs r0..r3, #0; add sp, #4`. -/
theorem exit_eff (t : State) :
    (execAll storeUsed t).mem = write32 t.mem (t.regs 4 + 104#32) (t.regs 7) ∧
    (execAll storeUsed t).regs 13 = t.regs 13 + 4#32 ∧
    (∀ r : Reg, r.val < 4 → (execAll storeUsed t).regs r = 0#32) ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → (execAll storeUsed t).regs r = t.regs r) := by
  obtain ⟨s1, hs1⟩ : ∃ x, x = (Instr.memImm .str 7 4 26).next t := ⟨_, rfl⟩
  obtain ⟨zm, zz, zo⟩ := zero_eff s1
  obtain ⟨s2, hs2⟩ : ∃ x, x = execAll zeroScratch s1 := ⟨_, rfl⟩
  rw [← hs2] at zm zz zo
  have hx : execAll storeUsed t = (Instr.addSp 1).next s2 := by rw [hs2, hs1]; rfl
  obtain ⟨a13, aoth, am⟩ := addSp_eff s2
  have m1 : s1.mem = write32 t.mem (t.regs 4 + 104#32) (t.regs 7) := by rw [hs1]; exact mem_str t 7 4 26
  have r1 : ∀ r : Reg, r ≠ 15 → s1.regs r = t.regs r := fun r h => by rw [hs1]; exact regs_str t 7 4 26 r h
  refine ⟨by rw [hx, am, zm, m1], by rw [hx, a13, zo 13 (by decide) (by decide), r1 13 (by decide)],
    fun r h4 => ?_, fun r h4 h13 h15 => ?_⟩
  · rw [hx, aoth r (by omega) (by omega)]; exact zz r h4
  · rw [hx, aoth r h13 h15, zo r h4 h15, r1 r (fun h => h15 (by rw [h]; rfl))]

/-- The state `update` leaves behind. `r0`-`r3` are zero: no message byte stays in a scratch
register. -/
structure UpdatePost (s : State) (st0 : SState) (w : State) : Prop where
  pc : w.pc = s.regs 14 &&& ~~~1#32
  sp : w.regs 13 = s.regs 13
  r4 : w.regs 4 = s.regs 4
  r5 : w.regs 5 = s.regs 5
  r6 : w.regs 6 = s.regs 6
  r7 : w.regs 7 = s.regs 7
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → w.regs r = s.regs r
  ctx : Ctx w.mem (s.regs 0) (M0Crypto.Spec.Blake2s.absorb st0 (LL s))
  mem : ∀ y, ¬ WrU s y → w.mem y = s.mem y
  scratch : ∀ r : Reg, r.val < 4 → w.regs r = 0#32

theorem absorb_done {s : State} {st0 st : SState} {t : State} (hI : Inv s st0 t (nn s) st) :
    M0Crypto.Spec.Blake2s.absorb st0 (LL s) = st := by
  have h := hI.ab
  have hl : (LL s).length ≤ nn s := by simp [LL, bytesAt_length]
  rw [List.drop_of_length_le hl] at h
  rw [← h]; rfl

theorem out_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {st : SState} (hpc : t.pc = base + BitVec.ofNat 32 oOut) (hI : Inv s st0 t (nn s) st) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (UpdatePost s st0) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [((4 : Reg), (104#32 : Word), 4)] [] storeUsed oOut hpc (by decide)
    storeUsed_at (by decide) ?_ ?_ (by simp) (by decide +kernel) (by decide +kernel) ?_
  · apply Reach.aligned_one
    rw [hI.r4]; exact e.c4
  · intro p hp o ho j hj
    rw [List.mem_singleton] at hp; subst hp
    rw [hI.r4, show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc]
    exact wu_ctx s _ (by have ho' : o < 4 := ho; omega)
  obtain ⟨um, u13, uz, uo⟩ := exit_eff t
  obtain ⟨u, hu⟩ : ∃ x, x = execAll storeUsed t := ⟨_, rfl⟩
  rw [← hu] at um u13 uz uo ⊢
  have hn := (s.regs 13).isLt
  have hlo := e.spLo
  have hu13 : u.regs 13 = s.regs 13 - 20#32 := by rw [u13, hI.r13]; bv_omega
  have hpu : u.pc = base + BitVec.ofNat 32 oUPop := by
    rw [hu, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  -- the pushed words
  have hw : ∀ o < 20, u.mem (s.regs 13 - 20#32 + BitVec.ofNat 32 o) = pm s (s.regs 13 - 20#32 + BitVec.ofNat 32 o) := by
    intro o ho
    rw [um, write32_other' _ _ _ _ (fun k hk he => ?_)]
    · exact push_mem e hI o ho
    · rw [hI.r4, show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc, fb_off] at he
      exact disj_ne e.cF (i := 104 + k) (o := STREAM_LOCALS + o) (by omega) (by omega) he.symm
  have hstk : Stk s u.mem := Stk.of (stk_M1 s) hw
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hstk
  have e4 : u.regs 13 + 4#32 = s.regs 13 - 16#32 := by rw [hu13]; bv_omega
  have e8 : u.regs 13 + 8#32 = s.regs 13 - 12#32 := by rw [hu13]; bv_omega
  have e12 : u.regs 13 + 12#32 = s.regs 13 - 8#32 := by rw [hu13]; bv_omega
  have e16 : u.regs 13 + 16#32 = s.regs 13 - 4#32 := by rw [hu13]; bv_omega
  have hbit : (read32 u.mem (u.regs 13 + 16#32)).getLsbD 0 = true := by
    rw [e16, hs5]; exact e.lr
  obtain ⟨w, hex, wm, w13, w4, w5, w6, w7, wo, wpc⟩ := pop_eff u hbit
  refine ReachS.stepWNR hb2 oUPop uPop hpu (by decide) uPop_at (by rw [B_len]; decide) ?_ hex ?_ ?_
  · simp only [uPop, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
      Access.aligned, State.sp]
    rintro x ⟨a, ha, rfl⟩
    rw [b240] at ha
    simp only [Bool.toNat_true] at ha
    have hsp := e.sp4
    have h13 : (u.regs 13).toNat = (s.regs 13).toNat - 20 := by rw [hu13]; bv_omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, beq_iff_eq]
    omega
  · intro y ⟨a, ha, hk, _⟩
    simp only [uPop, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp at hk
  · refine ReachS.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [wpc, e16, hs5]
    · rw [w13, hu13]; bv_omega
    · rw [w4, hu13]; exact hs1
    · rw [w5, e4]; exact hs2
    · rw [w6, e8]; exact hs3
    · rw [w7, e12]; exact hs4
    · intro r h8 h11
      rw [wo r (Or.inr h8) (fun h => by omega) (fun h => by omega)]
      rw [uo r (by omega) (fun h => by omega) (fun h => by omega)]
      exact hI.hi r h8 h11
    · rw [wm, um, hI.r4, hI.r7, absorb_done hI]
      exact used_write _ hI.ctx
    · intro y hy
      rw [wm, um, write32_other' _ _ _ _ (fun k hk he => ?_)]
      · exact hI.ag.eq (fun o ho he => hy (Or.inr ⟨o, ho, he⟩)) (fun o ho he => hy (Or.inl ⟨o, ho, he⟩))
      · rw [hI.r4, show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc] at he
        exact hy (Or.inr ⟨104 + k, by omega, he⟩)
    · intro r h4
      rw [wo r (Or.inl h4) (by omega) (by omega)]; exact uz r h4

end M0Crypto.Release.Blake2sUpdate
