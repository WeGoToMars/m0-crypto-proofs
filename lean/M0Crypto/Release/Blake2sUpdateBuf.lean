import M0Crypto.Release.Blake2sUpdateDirect
import M0Crypto.Release.Blake2sFrames
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sUpdateBytes
import M0Crypto.Release.Blake2sUpdateCall

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the buffer path (register effects, frame memory, loop invariants and the append at `oHave`)

One module; the sections follow the dependency order. -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2s (regs_addReg regs_movImm mem_addReg mem_movImm)
open M0Crypto.Release.Blake2sCopy (cmp_eff)
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Spec.Blake2s (absorb compress blockWords pad)
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Spec.Blake2s (absorb compress blockWords pad absorb_fit absorb_append)
open M0Crypto.Release.Blake2sCode (SiteAt)

/-! ## Register effects of the buffer path -/

theorem regs_subReg (s : State) (d n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subReg d n m).next s).regs r =
      if r = d.toReg then s.reg n - s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Release.sub_flags]

theorem mem_subReg (s : State) (d n m : LowReg) : ((Instr.subReg d n m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem cmpReg_eff (n m : LowReg) (s : State) :
    (execAll [Instr.dp .cmp n m] s).c = decide ((s.regs m.toReg).toNat ≤ (s.regs n.toReg).toNat) ∧
    (execAll [Instr.dp .cmp n m] s).z = (s.regs n.toReg == s.regs m.toReg) ∧
    (execAll [Instr.dp .cmp n m] s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 15 → (execAll [Instr.dp .cmp n m] s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, fun r h15 => execAll_regs_other _ _ r h15 (by simp [Instr.dsts])⟩ <;>
    simp [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, addFlags, M0Crypto.Armv6M.addWithCarry]
  · have := (s.regs m.toReg).isLt; have := (s.regs n.toReg).isLt; omega
  · have ha := (s.regs n.toReg).isLt
    have hb := (s.regs m.toReg).isLt
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      apply BitVec.eq_of_toNat_eq
      omega
    · intro h
      rw [h]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega


def setupC7 : List Instr :=
  [.movImm 0 0x28, .addReg 0 0 4, .addReg 0 0 7, .lslImm 1 5 0, .addReg 7 7 2, .addReg 5 5 2,
   .subReg 6 6 2]

theorem setupC_eq : setupC = setupC7 ++ [Instr.cmpImm 2 8] := rfl

theorem lsl0_fst (x : Word) (c : Bool) : (lslC x 0 c).1 = x := by simp [lslC]

theorem setupC7_eff (t : State) :
    (execAll setupC7 t).regs 0 = 40#32 + t.regs 4 + t.regs 7 ∧
    (execAll setupC7 t).regs 1 = t.regs 5 ∧
    (execAll setupC7 t).regs 7 = t.regs 7 + t.regs 2 ∧
    (execAll setupC7 t).regs 5 = t.regs 5 + t.regs 2 ∧
    (execAll setupC7 t).regs 6 = t.regs 6 - t.regs 2 ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 5 → r.val ≠ 6 → r.val ≠ 7 → r.val ≠ 15 →
      (execAll setupC7 t).regs r = t.regs r) ∧
    (execAll setupC7 t).mem = t.mem := by
  obtain ⟨a1, h1⟩ : ∃ x, x = (Instr.movImm 0 0x28).next t := ⟨_, rfl⟩
  obtain ⟨a2, h2⟩ : ∃ x, x = (Instr.addReg 0 0 4).next a1 := ⟨_, rfl⟩
  obtain ⟨a3, h3⟩ : ∃ x, x = (Instr.addReg 0 0 7).next a2 := ⟨_, rfl⟩
  obtain ⟨a4, h4⟩ : ∃ x, x = (Instr.lslImm 1 5 0).next a3 := ⟨_, rfl⟩
  obtain ⟨a5, h5⟩ : ∃ x, x = (Instr.addReg 7 7 2).next a4 := ⟨_, rfl⟩
  obtain ⟨a6, h6⟩ : ∃ x, x = (Instr.addReg 5 5 2).next a5 := ⟨_, rfl⟩
  obtain ⟨a7, h7⟩ : ∃ x, x = (Instr.subReg 6 6 2).next a6 := ⟨_, rfl⟩
  have hx : execAll setupC7 t = a7 := by rw [h7, h6, h5, h4, h3, h2, h1]; rfl
  rw [hx]
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  -- frame facts
  have f1 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → a1.regs r = t.regs r := fun r h0 h15 => by
    rw [h1, regs_movImm _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f2 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → a2.regs r = a1.regs r := fun r h0 h15 => by
    rw [h2, regs_addReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f3 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → a3.regs r = a2.regs r := fun r h0 h15 => by
    rw [h3, regs_addReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f4 : ∀ r : Reg, r.val ≠ 1 → r.val ≠ 15 → a4.regs r = a3.regs r := fun r h0 h15 => by
    rw [h4, regs_lsl _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f5 : ∀ r : Reg, r.val ≠ 7 → r.val ≠ 15 → a5.regs r = a4.regs r := fun r h0 h15 => by
    rw [h5, regs_addReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f6 : ∀ r : Reg, r.val ≠ 5 → r.val ≠ 15 → a6.regs r = a5.regs r := fun r h0 h15 => by
    rw [h6, regs_addReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f7 : ∀ r : Reg, r.val ≠ 6 → r.val ≠ 15 → a7.regs r = a6.regs r := fun r h0 h15 => by
    rw [h7, regs_subReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have s1 : a1.regs 0 = 40#32 := by
    rw [h1, regs_movImm _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s2 : a2.regs 0 = a1.regs 0 + a1.regs 4 := by
    rw [h2, regs_addReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s3 : a3.regs 0 = a2.regs 0 + a2.regs 7 := by
    rw [h3, regs_addReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s4 : a4.regs 1 = a3.regs 5 := by
    rw [h4, regs_lsl _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans (lsl0_fst _ _)
  have s5 : a5.regs 7 = a4.regs 7 + a4.regs 2 := by
    rw [h5, regs_addReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s6 : a6.regs 5 = a5.regs 5 + a5.regs 2 := by
    rw [h6, regs_addReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s7 : a7.regs 6 = a6.regs 6 - a6.regs 2 := by
    rw [h7, regs_subReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f7 0 (by decide) (by decide), f6 0 (by decide) (by decide), f5 0 (by decide) (by decide), f4 0 (by decide) (by decide), s3, s2, s1, f2 7 (by decide) (by decide), f1 7 (by decide) (by decide), f1 4 (by decide) (by decide)]
  · rw [f7 1 (by decide) (by decide), f6 1 (by decide) (by decide), f5 1 (by decide) (by decide), s4, f3 5 (by decide) (by decide), f2 5 (by decide) (by decide), f1 5 (by decide) (by decide)]
  · rw [f7 7 (by decide) (by decide), f6 7 (by decide) (by decide), s5, f4 7 (by decide) (by decide), f3 7 (by decide) (by decide), f2 7 (by decide) (by decide), f1 7 (by decide) (by decide), f4 2 (by decide) (by decide), f3 2 (by decide) (by decide), f2 2 (by decide) (by decide), f1 2 (by decide) (by decide)]
  · rw [f7 5 (by decide) (by decide), s6, f5 5 (by decide) (by decide), f4 5 (by decide) (by decide), f3 5 (by decide) (by decide), f2 5 (by decide) (by decide), f1 5 (by decide) (by decide), f5 2 (by decide) (by decide), f4 2 (by decide) (by decide), f3 2 (by decide) (by decide), f2 2 (by decide) (by decide), f1 2 (by decide) (by decide)]
  · rw [s7, f6 6 (by decide) (by decide), f5 6 (by decide) (by decide), f4 6 (by decide) (by decide), f3 6 (by decide) (by decide), f2 6 (by decide) (by decide), f1 6 (by decide) (by decide), f6 2 (by decide) (by decide), f5 2 (by decide) (by decide), f4 2 (by decide) (by decide), f3 2 (by decide) (by decide), f2 2 (by decide) (by decide), f1 2 (by decide) (by decide)]
  · intro r h0 h1' h5' h6' h7' h15
    rw [f7 r h6' h15, f6 r h5' h15, f5 r h7' h15, f4 r h1' h15, f3 r h0 h15, f2 r h0 h15, f1 r h0 h15]
  · rw [h7, mem_subReg, h6, mem_addReg, h5, mem_addReg, h4, mem_lsl, h3, mem_addReg, h2, mem_addReg, h1, mem_movImm]

theorem setupC_cmp (u : State) :
    (execAll [Instr.cmpImm 2 8] u).c = decide (8 ≤ (u.regs 2).toNat) ∧
    (execAll [Instr.cmpImm 2 8] u).z = (u.regs 2 == (8 : BitVec 8).setWidth 32) ∧
    (execAll [Instr.cmpImm 2 8] u).mem = u.mem ∧
    (∀ r : Reg, r.val ≠ 15 → (execAll [Instr.cmpImm 2 8] u).regs r = u.regs r) := cmp_eff 2 8 u

def takeA2 : List Instr := [.movImm 2 0x40, .subReg 2 2 7]

theorem takeA_eq : takeA = takeA2 ++ [Instr.dp .cmp 2 6] := rfl

theorem takeA2_eff (t : State) :
    (execAll takeA2 t).regs 2 = 64#32 - t.regs 7 ∧
    (∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → (execAll takeA2 t).regs r = t.regs r) ∧
    (execAll takeA2 t).mem = t.mem := by
  obtain ⟨a1, h1⟩ : ∃ x, x = (Instr.movImm 2 0x40).next t := ⟨_, rfl⟩
  obtain ⟨a2, h2⟩ : ∃ x, x = (Instr.subReg 2 2 7).next a1 := ⟨_, rfl⟩
  have hx : execAll takeA2 t = a2 := by rw [h2, h1]; rfl
  rw [hx]
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  have f1 : ∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → a1.regs r = t.regs r := fun r h0 h15 => by
    rw [h1, regs_movImm _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have f2 : ∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → a2.regs r = a1.regs r := fun r h0 h15 => by
    rw [h2, regs_subReg _ _ _ _ _ (n15 r h15)]; exact if_neg (fun h => h0 (by rw [h]; rfl))
  have s1 : a1.regs 2 = 64#32 := by
    rw [h1, regs_movImm _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  have s2 : a2.regs 2 = a1.regs 2 - a1.regs 7 := by
    rw [h2, regs_subReg _ _ _ _ _ (by decide)]; exact (if_pos rfl).trans rfl
  refine ⟨?_, fun r h2' h15 => ?_, ?_⟩
  · rw [s2, s1, f1 7 (by decide) (by decide)]
  · rw [f2 r h2' h15, f1 r h2' h15]
  · rw [h2, mem_subReg, h1, mem_movImm]

theorem takeB_eff (t : State) :
    (execAll takeB t).regs 2 = t.regs 6 ∧
    (∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → (execAll takeB t).regs r = t.regs r) ∧
    (execAll takeB t).mem = t.mem := by
  have e : execAll takeB t = (Instr.lslImm 2 6 0).next t := rfl
  refine ⟨?_, fun r h2' h15 => ?_, ?_⟩
  · rw [e, regs_lsl _ _ _ _ _ (by decide)]
    exact (if_pos rfl).trans (lsl0_fst _ _)
  · rw [e, regs_lsl _ _ _ _ _ (fun h => h15 (by rw [h]; rfl))]
    exact if_neg (fun h => h2' (by rw [h]; rfl))
  · rw [e, mem_lsl]

/-! ## Frame memory -/

theorem bytesAt_ext {m1 m2 : Mem} {p1 p2 : Word} {n : Nat}
    (h : ∀ i < n, m1 (p1 + BitVec.ofNat 32 i) = m2 (p2 + BitVec.ofNat 32 i)) :
    bytesAt m1 p1 n = bytesAt m2 p2 n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem buf_mem {base : Word} {s t v : State} {st0 : SState} (e : UpdateEntry base s st0)
    {k : Nat} {st : SState} (hI : Inv s st0 t k st) (tk : Nat) (hu : st.pending.length + tk ≤ 64)
    (hk : k + tk ≤ nn s)
    (hcp : ∀ i < tk, v.mem (s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length + i)) =
      t.mem (s.regs 1 + BitVec.ofNat 32 (k + i)))
    (hout : ∀ y, (∀ i < tk, y ≠ s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length + i)) →
      (∀ o < 20, y ≠ fb s + BitVec.ofNat 32 (SAVED_4 + o)) → v.mem y = t.mem y) :
    CtxNU v.mem (s.regs 0) ⟨st.h, st.count, st.pending ++ (((LL s).drop k).take tk)⟩ ∧ Ag s v := by
  have hcb : (s.regs 0).toNat + 112 ≤ 2 ^ 32 := e.cF.1
  have hctx : ∀ o, o < 40 + st.pending.length →
      v.mem (s.regs 0 + BitVec.ofNat 32 o) = t.mem (s.regs 0 + BitVec.ofNat 32 o) := by
    intro o ho
    refine hout _ (fun i hi he => ?_) (fun o2 ho2 he => ?_)
    · have h1 := congrArg BitVec.toNat he
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at h1
      omega
    · have : s.regs 13 - STREAM_FRAME_W = fb s := rfl
      exact disj_ne e.cF (i := o) (by omega) (o := SAVED_4 + o2) (by omega) (by rw [← this] at he; exact he)
  have hr32 : ∀ o, o + 4 ≤ 40 + st.pending.length → read32 v.mem (s.regs 0 + BitVec.ofNat 32 o) =
      read32 t.mem (s.regs 0 + BitVec.ofNat 32 o) := by
    intro o ho
    apply read32_congr
    intro j hj
    rw [ofNat_add_assoc]
    exact hctx _ (by omega)
  have hMlen : (((LL s).drop k).take tk).length = tk := by
    simp only [List.length_take, List.length_drop, LL, bytesAt_length]; omega
  have hag : Ag s v := by
    intro y hy1 hy2
    rw [hout y (fun i hi he => hy1 (40 + st.pending.length + i) (by omega) he)
      (fun o ho he => hy2 (SAVED_4 + o) (by omega) he)]
    exact hI.ag y hy1 hy2
  refine ⟨⟨hI.ctx.hsz, ?_, ?_, ?_, hI.ctx.cnt, ?_, ?_⟩, hag⟩
  · intro i hi
    have := hr32 (4 * i) (by omega)
    simp only [this]
    exact hI.ctx.h i hi
  · have := hr32 32 (by omega)
    show read32 v.mem (s.regs 0 + 32#32) = _
    rw [show (32#32 : Word) = BitVec.ofNat 32 32 from rfl, this]; exact hI.ctx.clo
  · have := hr32 36 (by omega)
    show read32 v.mem (s.regs 0 + 36#32) = _
    rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, this]; exact hI.ctx.chi
  · simp only [List.length_append, hMlen]; omega
  · simp only [List.length_append, hMlen]
    rw [bytesAt_append]
    have p1 : bytesAt v.mem (s.regs 0 + 40#32) st.pending.length = st.pending := by
      have : bytesAt v.mem (s.regs 0 + 40#32) st.pending.length =
          bytesAt t.mem (s.regs 0 + 40#32) st.pending.length := by
        apply bytesAt_congr
        intro i hi
        rw [show (40#32 : Word) = BitVec.ofNat 32 40 from rfl, ofNat_add_assoc]
        exact hctx _ (by omega)
      rw [this]; exact hI.ctx.buf
    have p2 : bytesAt v.mem (s.regs 0 + 40#32 + BitVec.ofNat 32 st.pending.length) tk =
        ((LL s).drop k).take tk := by
      rw [LL, bytesAt_slice _ _ _ _ _ hk]
      apply bytesAt_ext
      intro i hi
      rw [show (40#32 : Word) = BitVec.ofNat 32 40 from rfl, ofNat_add_assoc, ofNat_add_assoc, ← Nat.add_assoc,
        hcp i hi, ofNat_add_assoc]
      exact src_ag hI.ag e.pC e.pF (by omega)
    rw [p1, p2]

/-! ## Buffer-path loop -/

theorem cp3 (u : State) : condPassed 3 u = !u.c := rfl

/-- `Inv` only reads registers from `r4` up and memory. -/
theorem Inv.keep {s : State} {st0 : SState} {t u : State} {k : Nat} {st : SState} (h : Inv s st0 t k st)
    (hr : ∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → u.regs r = t.regs r) (hm : u.mem = t.mem) :
    Inv s st0 u k st :=
  ⟨by rw [hr 4 (by decide) (by decide)]; exact h.r4, by rw [hr 5 (by decide) (by decide)]; exact h.r5,
   by rw [hr 6 (by decide) (by decide)]; exact h.r6, by rw [hr 7 (by decide) (by decide)]; exact h.r7,
   by rw [hr 13 (by decide) (by decide)]; exact h.r13,
   fun r h8 h11 => by rw [hr r (by omega) (by omega)]; exact h.hi r h8 h11, h.kn,
   by rw [hm]; exact h.ctx, Ag.of_mem h.ag hm, h.tot, h.ab⟩

/-- After choosing the chunk length: at `oHave` with `r2 = take`. -/
def TakePost (base : Word) (s : State) (st0 : SState) (k : Nat) (st : SState) (v : State) : Prop :=
  v.pc = base + BitVec.ofNat 32 oHave ∧ ∃ tk, 1 ≤ tk ∧ tk ≤ nn s - k ∧ st.pending.length + tk ≤ 64 ∧
    v.regs 2 = BitVec.ofNat 32 tk ∧ Inv s st0 v k st

theorem take_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState}
    (hpc : t.pc = base + BitVec.ofNat 32 oBuf) (hI : Inv s st0 t k st) (hk : k < nn s)
    (hlt : st.pending.length < 64) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (TakePost base s st0 k st) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : nn s = (s.regs 2).toNat := rfl
  have hn32 := (s.regs 2).isLt
  refine ReachS.symBlockWNR hb2 [] [] [] takeA oBuf hpc (by decide) takeA_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  rw [takeA_eq, execAll_append]
  obtain ⟨a2, hA2⟩ : ∃ x, x = execAll takeA2 t := ⟨_, rfl⟩
  rw [← hA2]
  obtain ⟨b2, bo, bm⟩ := takeA2_eff t
  rw [← hA2] at b2 bo bm
  obtain ⟨cc, cz, cm, cr⟩ := cmpReg_eff 2 6 a2
  obtain ⟨a, hA⟩ : ∃ x, x = execAll [Instr.dp .cmp 2 6] a2 := ⟨_, rfl⟩
  rw [← hA] at cc cz cm cr ⊢
  have hu : st.pending.length ≤ 64 := hI.ctx.plen
  have ar2 : a2.regs 2 = BitVec.ofNat 32 (64 - st.pending.length) := by
    rw [b2, hI.r7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have ar6 : a2.regs 6 = BitVec.ofNat 32 (nn s - k) := by rw [bo 6 (by decide) (by decide)]; exact hI.r6
  have hI1 : Inv s st0 a k st := hI.keep (fun r h4 h15 => by
      rw [cr r h15, bo r (by omega) h15]) (by rw [cm, bm])
  have hp : a.pc = base + BitVec.ofNat 32 oBufBls := by
    rw [hA, execAll_pc _ _ (by decide), hA2, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc, ofNat_add_assoc]; rfl
  have hav : (a2.regs 2).toNat = 64 - st.pending.length := by
    rw [ar2, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have hnk : (a2.regs 6).toNat = nn s - k := by
    rw [ar6, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have ar2' : a.regs 2 = BitVec.ofNat 32 (64 - st.pending.length) := by rw [cr 2 (by decide), ar2]
  have ar6' : a.regs 6 = BitVec.ofNat 32 (nn s - k) := by rw [cr 6 (by decide), ar6]
  have h6' : (a2.regs (LowReg.toReg 6)).toNat = nn s - k := hnk
  have h2' : (a2.regs (LowReg.toReg 2)).toNat = 64 - st.pending.length := hav
  have ccz : a.c = decide (nn s - k ≤ 64 - st.pending.length) ∧
      a.z = decide (64 - st.pending.length = nn s - k) := by
    constructor
    · rw [cc, h6', h2']
    · rw [cz]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro h; have := congrArg BitVec.toNat h; omega
      · intro h; apply BitVec.eq_of_toNat_eq; omega
  apply ReachS.bcondPcNR hb2 oBufBls oHave 9 (brImm8 oBufBls oHave) hp (by decide +kernel) bufBls_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    rw [cp9, ccz.1, ccz.2] at hc
    have hle : 64 - st.pending.length ≤ nn s - k := by
      apply Decidable.byContradiction
      intro hgt
      have h1 : decide (nn s - k ≤ 64 - st.pending.length) = true := by simp; omega
      have h2 : decide (64 - st.pending.length = nn s - k) = false := by simp; omega
      rw [h1, h2] at hc
      simp at hc
    refine ReachS.done ⟨by rw [sr_pc], 64 - st.pending.length, by omega, hle, by omega, ?_, hI1.setPc _⟩
    rw [sr_ne _ _ _ _ (by decide)]; exact ar2'
  · intro hc
    rw [cp9, ccz.1, ccz.2] at hc
    have hgt : nn s - k < 64 - st.pending.length := by
      apply Decidable.byContradiction
      intro hle
      by_cases h3 : 64 - st.pending.length = nn s - k
      · have h1 : decide (nn s - k ≤ 64 - st.pending.length) = true := by simp; omega
        have h2 : decide (64 - st.pending.length = nn s - k) = true := by simp; omega
        rw [h1, h2] at hc
        simp at hc
      · have h1 : decide (nn s - k ≤ 64 - st.pending.length) = false := by simp; omega
        rw [h1] at hc
        simp at hc
    obtain ⟨y, hy⟩ : ∃ x, x = a.setReg 15 (base + BitVec.ofNat 32 (oBufBls + 2)) := ⟨_, rfl⟩
    rw [← hy]
    have hIy : Inv s st0 y k st := by rw [hy]; exact hI1.setPc _
    have hpy : y.pc = base + BitVec.ofNat 32 oTakeB := by
      rw [hy, sr_pc, show oBufBls + 2 = oTakeB by decide]
    refine ReachS.symBlockWNR hb2 [] [] [] takeB oTakeB hpy (by decide) takeB_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨d2, do_, dm⟩ := takeB_eff y
    refine ReachS.done ⟨?_, nn s - k, by omega, Nat.le_refl _, by omega, ?_, ?_⟩
    · rw [execAll_pc _ _ (by decide), hpy, ofNat_add_assoc]; rfl
    · rw [d2, hIy.r6]
    · exact hIy.keep (fun r h4 h15 => do_ r (by omega) h15) dm

/-! ## Append bookkeeping -/

/-- What the append leaves, relative to the state `t` at `oHave`. -/
structure BufFin (base : Word) (s t x : State) (k tk : Nat) (u : Nat) : Prop where
  pc : x.pc = base + BitVec.ofNat 32 oNext
  r4 : x.regs 4 = t.regs 4
  r5 : x.regs 5 = t.regs 5 + BitVec.ofNat 32 tk
  r6 : x.regs 6 = t.regs 6 - BitVec.ofNat 32 tk
  r7 : x.regs 7 = t.regs 7 + BitVec.ofNat 32 tk
  r13 : x.regs 13 = t.regs 13
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → x.regs r = t.regs r
  hcp : ∀ i < tk, x.mem (s.regs 0 + BitVec.ofNat 32 (40 + u + i)) = t.mem (s.regs 1 + BitVec.ofNat 32 (k + i))
  hout : ∀ y, (∀ i < tk, y ≠ s.regs 0 + BitVec.ofNat 32 (40 + u + i)) →
    (∀ o < 20, y ≠ fb s + BitVec.ofNat 32 (SAVED_4 + o)) → x.mem y = t.mem y

/-- After the append: at `oNext` with more input consumed. -/
def BufPost (base : Word) (s : State) (st0 : SState) (k : Nat) (v : State) : Prop :=
  v.pc = base + BitVec.ofNat 32 oNext ∧ ∃ k' st', k < k' ∧ k' ≤ nn s ∧ Inv s st0 v k' st'

theorem buf_post {base : Word} {s t x : State} {st0 : SState} (e : UpdateEntry base s st0)
    {k : Nat} {st : SState} (hI : Inv s st0 t k st) (tk : Nat) (h1 : 1 ≤ tk)
    (hk : k + tk ≤ nn s) (hu : st.pending.length + tk ≤ 64)
    (hF : BufFin base s t x k tk st.pending.length) : BufPost base s st0 k x := by
  obtain ⟨hmc, hmag⟩ := buf_mem e hI tk hu hk hF.hcp hF.hout
  have hMlen : (((LL s).drop k).take tk).length = tk := by
    simp only [List.length_take, List.length_drop, LL, bytesAt_length]; omega
  have hn32 := (s.regs 2).isLt
  have hnn : nn s = (s.regs 2).toNat := rfl
  refine ⟨hF.pc, k + tk, ⟨st.h, st.count, st.pending ++ (((LL s).drop k).take tk)⟩, by omega, hk, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hmc, hmag, ?_, ?_⟩
  · rw [hF.r4, hI.r4]
  · rw [hF.r5, hI.r5, ofNat_add_assoc]
  · rw [hF.r6, hI.r6]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · rw [hF.r7, hI.r7]
    simp only [List.length_append, hMlen]
    rw [BitVec.ofNat_add]
  · rw [hF.r13, hI.r13]
  · intro r h8 h11
    rw [hF.hi r h8 h11, hI.hi r h8 h11]
  · have := hI.tot
    simp only [List.length_append, hMlen]
    omega
  · rw [← hI.ab]
    have e1 : absorb st ((LL s).drop k) = absorb (absorb st (((LL s).drop k).take tk)) (((LL s).drop k).drop tk) := by
      rw [← absorb_append, List.take_append_drop]
    rw [e1, absorb_fit _ st (by omega)]
    simp only [List.drop_drop]

/-! ## The append at `oHave` (byte loop or `m0c_blake2s_copy`) -/

theorem disj_symm {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) : Disj b m a n :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem wu_of_wcu {base : Word} {s u : State} {pc y : Word} (c : Nat)
    (hF : u.regs 13 - 20#32 = fb s + BitVec.ofNat 32 SAVED_4) (h0 : u.regs 0 = s.regs 0 + BitVec.ofNat 32 c)
    (hc : c + (u.regs 2).toNat ≤ 112) (h : WCu base u pc y) : WU base s pc y := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hs => ?_⟩
  · rcases h1 with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
    · refine Or.inl ⟨SAVED_4 + o, by omega, ?_⟩
      rw [hF]; unfold fb; bv_omega
    · refine Or.inr ⟨c + o, by omega, ?_⟩
      rw [h0]; bv_omega
  · obtain ⟨o, ho, rfl⟩ := h2 hs
    refine ⟨c + o, by omega, ?_⟩
    rw [h0]; bv_omega

theorem have_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState} {tk : Nat}
    (hpc : t.pc = base + BitVec.ofNat 32 oHave) (hI : Inv s st0 t k st) (h1 : 1 ≤ tk)
    (h2 : tk ≤ nn s - k) (h3 : st.pending.length + tk ≤ 64) (hr2 : t.regs 2 = BitVec.ofNat 32 tk) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (BufPost base s st0 k) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : nn s = (s.regs 2).toNat := rfl
  have hn32 := (s.regs 2).isLt
  have hcode := code_ag e.code hI.ag e.codeC e.codeF
  have hCb : (s.regs 0).toNat + 112 ≤ 2 ^ 32 := e.cF.1
  have hPb : (s.regs 1).toNat + nn s ≤ 2 ^ 32 := e.pC.1
  have hsn := (s.regs 13).isLt
  have hu64 := hI.ctx.plen
  have hk : k + tk ≤ nn s := by omega
  refine ReachS.symBlockWNR hb2 [] [] [] setupC oHave hpc (by decide) setupC_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  rw [setupC_eq, execAll_append]
  obtain ⟨w7, hW7⟩ : ∃ x, x = execAll setupC7 t := ⟨_, rfl⟩
  rw [← hW7]
  obtain ⟨q0, q1, q7, q5, q6, qo, qm⟩ := setupC7_eff t
  rw [← hW7] at q0 q1 q7 q5 q6 qo qm
  obtain ⟨cc, cz, cm, cr⟩ := cmp_eff 2 8 w7
  obtain ⟨w, hW⟩ : ∃ x, x = execAll [Instr.cmpImm 2 8] w7 := ⟨_, rfl⟩
  rw [← hW] at cc cz cm cr ⊢
  have wr0 : w.regs 0 = s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length) := by
    rw [cr 0 (by decide), q0, hI.r4, hI.r7, BitVec.ofNat_add]; bv_omega
  have wr1 : w.regs 1 = s.regs 1 + BitVec.ofNat 32 k := by rw [cr 1 (by decide), q1]; exact hI.r5
  have wr2 : w.regs 2 = BitVec.ofNat 32 tk := by
    rw [cr 2 (by decide), qo 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr2
  have wr5 : w.regs 5 = t.regs 5 + BitVec.ofNat 32 tk := by rw [cr 5 (by decide), q5, hr2]
  have wr6 : w.regs 6 = t.regs 6 - BitVec.ofNat 32 tk := by rw [cr 6 (by decide), q6, hr2]
  have wr7 : w.regs 7 = t.regs 7 + BitVec.ofNat 32 tk := by rw [cr 7 (by decide), q7, hr2]
  have wo : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 5 → r.val ≠ 6 → r.val ≠ 7 → r.val ≠ 15 →
      w.regs r = t.regs r := fun r a b c d f g => by rw [cr r g, qo r a b c d f g]
  have wm : w.mem = t.mem := by rw [cm, qm]
  have wc : w.c = decide (8 ≤ tk) := by
    rw [cc]
    have : (w7.regs (LowReg.toReg 2)).toNat = tk := by
      have e2 : w7.regs (LowReg.toReg 2) = BitVec.ofNat 32 tk := by
        have := qo 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        exact this.trans hr2
      rw [e2, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
    rw [this]; rfl
  have hpw : w.pc = base + BitVec.ofNat 32 oHaveBlo := by
    rw [hW, execAll_pc _ _ (by decide), hW7, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc, ofNat_add_assoc]; rfl
  have hd0n : (s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length)).toNat = (s.regs 0).toNat + (40 + st.pending.length) :=
    toNat_add_ofNat _ _ (by omega)
  have hs1n : (s.regs 1 + BitVec.ofNat 32 k).toNat = (s.regs 1).toNat + k := toNat_add_ofNat _ _ (by omega)
  have hDS : Disj (s.regs 1 + BitVec.ofNat 32 k) tk (s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length)) tk :=
    disj_r (disj_l e.pC (by rw [hs1n]; omega) (by rw [hs1n]; omega)) (by rw [hd0n]; omega) (by rw [hd0n]; omega)
  have hDj := disj_symm hDS
  have hr13 : w.regs 13 = s.regs 13 - 24#32 := by
    rw [wo 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r13
  have whi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → w.regs r = t.regs r := fun r a b => by
    apply wo r <;> omega
  have w4 : w.regs 4 = t.regs 4 := wo 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply ReachS.bcondPcNR hb2 oHaveBlo oBytesL 3 (brImm8 oHaveBlo oBytesL) hpw (by decide +kernel) haveBlo_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    rw [cp3, wc] at hc
    have hlt8 : tk < 8 := by
      revert hc; cases h : decide (8 ≤ tk) <;> simp at h ⊢ <;> omega
    obtain ⟨y, hy⟩ : ∃ x, x = w.setReg 15 (base + BitVec.ofNat 32 oBytesL) := ⟨_, rfl⟩
    rw [← hy]
    have yr : ∀ r : Reg, r.val ≠ 15 → y.regs r = w.regs r := fun r h15 => by
      rw [hy, sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]
    have ym : y.mem = t.mem := by rw [hy]; exact wm
    have hpy : y.pc = base + BitVec.ofNat 32 oBytesL := by rw [hy, sr_pc]
    have hy0 : y.regs 0 = s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length) := by rw [yr 0 (by decide), wr0]
    have hy1 : y.regs 1 = s.regs 1 + BitVec.ofNat 32 k := by rw [yr 1 (by decide), wr1]
    have hy2 : y.regs 2 = BitVec.ofNat 32 tk := by rw [yr 2 (by decide), wr2]
    refine ReachS.monoQ (ReachS.mono (byte_reach (Wr := CtxR s) (Rd := UR s) (t := y) hb2 h1 (by omega)
      (by rw [hy0, hy1]; exact hDj) hpy hy2
      (fun i hi => by rw [hy0, ofNat_add_assoc]; exact ⟨_, by omega, rfl⟩)
      (fun i hi => UR.data_at (c := k) hy1 (by omega)))
      (P' := PNR ldAll (WU base s) (UR s)) (fun _ _ h => ⟨⟨fun y hy => wu_of_ctxR (h.1.1 y hy), h.1.2⟩, h.2⟩) (fun _ h => h)) ?_
    rintro x ⟨hxpc, bi⟩
    refine buf_post e hI tk h1 hk h3 ⟨hxpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [bi.hi 4 (by decide) (by decide), yr 4 (by decide), w4]
    · rw [bi.hi 5 (by decide) (by decide), yr 5 (by decide), wr5]
    · rw [bi.hi 6 (by decide) (by decide), yr 6 (by decide), wr6]
    · rw [bi.hi 7 (by decide) (by decide), yr 7 (by decide), wr7]
    · rw [bi.hi 13 (by decide) (by decide), yr 13 (by decide), hr13, hI.r13]
    · intro r h8 h11
      rw [bi.hi r (by omega) (by omega), yr r (by omega), whi r h8 h11]
    · intro i hi
      have := bi.cp.1 i hi
      rw [hy0, hy1, ofNat_add_assoc, ofNat_add_assoc, ym] at this
      exact this
    · intro y' hy1' hy2'
      have := bi.cp.2 y' (fun i hi he => hy1' i hi (by rw [hy0, ofNat_add_assoc] at he; exact he))
      rw [this, ym]
  · intro hc
    rw [cp3, wc] at hc
    have hge8 : 8 ≤ tk := by
      revert hc; cases h : decide (8 ≤ tk) <;> simp at h ⊢ <;> omega
    obtain ⟨y, hy⟩ : ∃ x, x = w.setReg 15 (base + BitVec.ofNat 32 (oHaveBlo + 2)) := ⟨_, rfl⟩
    rw [← hy]
    have yr : ∀ r : Reg, r.val ≠ 15 → y.regs r = w.regs r := fun r h15 => by
      rw [hy, sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]
    have ym : y.mem = t.mem := by rw [hy]; exact wm
    have hpy : y.pc = base + BitVec.ofNat 32 oCopyBl := by
      rw [hy, sr_pc, show oHaveBlo + 2 = oCopyBl by decide]
    have hy0 : y.regs 0 = s.regs 0 + BitVec.ofNat 32 (40 + st.pending.length) := by rw [yr 0 (by decide), wr0]
    have hy1 : y.regs 1 = s.regs 1 + BitVec.ofNat 32 k := by rw [yr 1 (by decide), wr1]
    have hy2 : y.regs 2 = BitVec.ofNat 32 tk := by rw [yr 2 (by decide), wr2]
    have hy13 : y.regs 13 = s.regs 13 - 24#32 := by rw [yr 13 (by decide), hr13]
    have hy2n : (y.regs 2).toNat = tk := by
      rw [hy2, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
    have hFr : y.regs 13 - 20#32 = fb s + BitVec.ofNat 32 SAVED_4 := by
      rw [hy13]; unfold fb; bv_omega
    have hfbn : (s.regs 13 - STREAM_FRAME_W).toNat = (s.regs 13).toNat - STREAM_FRAME := by
      have := e.spLo; bv_omega
    have hFn : (y.regs 13 - 20#32).toNat = (s.regs 13).toNat - 44 := by
      have := e.spLo; rw [hy13]; bv_omega
    have hSn : (y.regs 1).toNat = (s.regs 1).toNat + k := by rw [hy1]; exact hs1n
    have hDn : (y.regs 0).toNat = (s.regs 0).toNat + (40 + st.pending.length) := by rw [hy0]; exact hd0n
    have hsF : Disj (s.regs 0) 112 (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME := e.cF
    have hDj' : Disj (y.regs 0) tk (y.regs 1) tk := by rw [hy0, hy1]; exact hDj
    have hCbn := e.cF.1
    have hbs := e.codeC.1
    have hbF := e.codeF.1
    refine ReachS.bind (ReachS.monoQ (bl_copyS (W := WU base s) (R := UR s) (u := y) oCopyBl e.base4 hpy (by decide) copyBl_at
      (by decide) blCopy (by rw [ym]; exact hcode) (by rw [hy13]; have := e.sp4; have := e.spLo; bv_omega)
      (by rw [hy13]; have := e.spLo; bv_omega) (by omega) (by omega) (by rw [hy2n]; exact hDj')
      (disj_r e.codeC (b' := y.regs 0) (by omega) (by omega))
      (disj_r e.codeF (b' := y.regs 13 - 20#32) (by omega) (by omega))
      (disj_r (disj_l hsF (a' := y.regs 0) (by omega) (by omega)) (b' := y.regs 13 - 20#32) (by omega) (by omega))
      (disj_r (disj_l e.pF (a' := y.regs 1) (by omega) (by omega)) (b' := y.regs 13 - 20#32) (by omega) (by omega))
      (fun pc y' h => wu_of_wcu (c := 40 + st.pending.length) hFr hy0 (by omega) h)
      (fun y' hy' => by
        obtain ⟨o, ho, h⟩ := hy'
        rw [hy1] at h
        rw [h]
        exact UR.data_at (c := k) rfl (by omega))) ?_)
    intro x bp
    have hpx : x.pc = base + BitVec.ofNat 32 oCopyB := by rw [bp.pc]; rfl
    obtain ⟨x', hx'⟩ : ∃ z, z = x.setReg 15 (base + BitVec.ofNat 32 oNext) := ⟨_, rfl⟩
    refine ReachS.bPcNR hb2 oCopyB oNext (brImm11 oCopyB oNext) hpx (by decide) copyB_at (by decide)
      (by decide +kernel) ?_
    rw [← hx']
    have xr : ∀ r : Reg, r.val ≠ 15 → x'.regs r = x.regs r := fun r h15 => by
      rw [hx', sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]
    have xm : x'.mem = x.mem := by rw [hx']; rfl
    refine ReachS.done (buf_post e hI tk h1 hk h3 ⟨by rw [hx', sr_pc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [xr 4 (by decide), bp.keep 4 (by decide) (by decide), yr 4 (by decide), w4]
    · rw [xr 5 (by decide), bp.keep 5 (by decide) (by decide), yr 5 (by decide), wr5]
    · rw [xr 6 (by decide), bp.keep 6 (by decide) (by decide), yr 6 (by decide), wr6]
    · rw [xr 7 (by decide), bp.keep 7 (by decide) (by decide), yr 7 (by decide), wr7]
    · rw [xr 13 (by decide), bp.sp, hy13, hI.r13]
    · intro r h8 h11
      rw [xr r (by omega), bp.keep r (by omega) h11, yr r (by omega), whi r h8 h11]
    · intro i hi
      have := bp.copy i (by omega)
      rw [hy0, hy1, ofNat_add_assoc, ofNat_add_assoc, ym] at this
      rw [xm]; exact this
    · intro y' hy1' hy2'
      have := bp.mem y' (fun o ho he => hy2' o ho (by rw [hFr, show (SAVED_4_W : Word) = BitVec.ofNat 32 SAVED_4 from rfl, ofNat_add_assoc] at he; exact he))
        (fun o ho he => hy1' o (by omega) (by rw [hy0, ofNat_add_assoc] at he; exact he))
      rw [xm, this, ym]

end M0Crypto.Release.Blake2sUpdate
