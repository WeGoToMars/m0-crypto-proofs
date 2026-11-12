import M0Crypto.Release.Blake2sFinalRet
import M0Crypto.Release.Blake2sFinalPad
import M0Crypto.Release.Blake2sFinalW
import M0Crypto.Release.ReachPcL2
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final`: the function-level contract -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt)
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat read32_storeWords_same)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 Cp cp_src add_ofNat_inj)
open M0Crypto.Release.Blake2sCompress (off_eq)

/-- What `final` leaves: returned, `sp` and `r4`-`r11` restored, the digest of the stream written
to `out`, memory unchanged outside what `final` may write, and `r0`-`r3` zero (no digest word
stays in a scratch register). -/
structure FinalPost (s t : State) (st : M0Crypto.Spec.Blake2s.State) : Prop where
  pc : t.pc = s.regs 14 &&& ~~~1#32
  sp : t.regs 13 = s.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → t.regs r = s.regs r
  out : bytesAt t.mem (s.regs 1) 32 = M0Crypto.Spec.Blake2s.finish st
  mem : ∀ y, ¬ WrF s y → t.mem y = s.mem y
  scratch : ∀ r : Reg, r.val < 4 → t.regs r = 0#32

theorem wr_frame (s : State) (o : Nat) (h : o < STREAM_FRAME) : WrF s (s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 o) :=
  Or.inl ⟨o, h, rfl⟩
theorem wr_ctx (s : State) (o : Nat) (h : o < 112) : WrF s (s.regs 0 + BitVec.ofNat 32 o) :=
  Or.inr (Or.inl ⟨o, h, rfl⟩)
theorem wr_out (s : State) (o : Nat) (h : o < 32) : WrF s (s.regs 1 + BitVec.ofNat 32 o) :=
  Or.inr (Or.inr ⟨o, h, rfl⟩)

theorem rd_same (M M' : Mem) (b : Word) (n : Nat) (hm : ∀ o < n, M' (b + BitVec.ofNat 32 o) = M (b + BitVec.ofNat 32 o))
    (i : Nat) (hi : 4 * i + 4 ≤ n) : read32 M' (b + BitVec.ofNat 32 (4 * i)) = read32 M (b + BitVec.ofNat 32 (4 * i)) := by
  apply read32_congr
  intro k hk
  rw [ofNat_add_assoc]
  exact hm _ (by omega)

/-- The five words `push {r4-r7,lr}` stored at the bottom of the frame. -/
def Stk (s : State) (M : Mem) : Prop :=
  read32 M (s.regs 13 - 20#32) = s.regs 4 ∧ read32 M (s.regs 13 - 16#32) = s.regs 5 ∧
  read32 M (s.regs 13 - 12#32) = s.regs 6 ∧ read32 M (s.regs 13 - 8#32) = s.regs 7 ∧
  read32 M (s.regs 13 - 4#32) = s.regs 14

theorem stk_M1 (s : State) :
    Stk s (storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) := by
  have key : ∀ i (hi : i < 5), read32 (storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * i)) =
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14][i]'(by simpa using hi) :=
    fun i hi => read32_storeWords_same _ _ _ i (by simpa using hi) (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := key 0 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 0) = s.regs 13 - 20#32 by bv_omega] at this
    simpa using this
  · have := key 1 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 1) = s.regs 13 - 16#32 by bv_omega] at this
    simpa using this
  · have := key 2 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 2) = s.regs 13 - 12#32 by bv_omega] at this
    simpa using this
  · have := key 3 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 3) = s.regs 13 - 8#32 by bv_omega] at this
    simpa using this
  · have := key 4 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 4) = s.regs 13 - 4#32 by bv_omega] at this
    simpa using this

theorem Stk.of {s : State} {M M' : Mem} (h : Stk s M)
    (hm : ∀ o < 20, M' (s.regs 13 - 20#32 + BitVec.ofNat 32 o) = M (s.regs 13 - 20#32 + BitVec.ofNat 32 o)) :
    Stk s M' := by
  have key : ∀ i, 4 * i + 4 ≤ 20 → read32 M' (s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * i)) =
      read32 M (s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * i)) := fun i hi => rd_same M M' _ 20 hm i hi
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := key 0 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 0) = s.regs 13 - 20#32 by bv_omega] at this
    rw [this, h0]
  · have := key 1 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 1) = s.regs 13 - 16#32 by bv_omega] at this
    rw [this, h1]
  · have := key 2 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 2) = s.regs 13 - 12#32 by bv_omega] at this
    rw [this, h2]
  · have := key 3 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 3) = s.regs 13 - 8#32 by bv_omega] at this
    rw [this, h3]
  · have := key 4 (by omega)
    rw [show s.regs 13 - 20#32 + BitVec.ofNat 32 (4 * 4) = s.regs 13 - 4#32 by bv_omega] at this
    rw [this, h4]

theorem m1_far (s : State) (y : Word) (h : ∀ o < 20, y ≠ s.regs 13 - 20#32 + BitVec.ofNat 32 o) :
    storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] y = s.mem y := by
  apply storeWords_other
  intro i k hi hk he
  simp at hi
  exact h (4 * i + k) (by omega) (by rw [he, ofNat_add_assoc])

/-- The state after the padding loops, as the compress call needs it. -/
structure PadOut (s : State) (st : M0Crypto.Spec.Blake2s.State) (t : State) : Prop where
  sp : t.regs 13 = s.regs 13 - 24#32
  r0 : t.regs 0 = 0#32
  r1 : t.regs 1 = s.regs 0 + 40#32
  r2 : (t.regs 2).toNat + 2 ^ 32 * (t.regs 3).toNat = st.count + st.pending.length
  r4 : t.regs 4 = s.regs 0
  r5 : t.regs 5 = s.regs 1
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r
  far : ∀ y, (∀ i, st.pending.length ≤ i → i < 64 → y ≠ s.regs 0 + 40#32 + BitVec.ofNat 32 i) →
    (∀ o < 20, y ≠ s.regs 13 - 20#32 + BitVec.ofNat 32 o) → t.mem y = s.mem y
  zero : ∀ i, st.pending.length ≤ i → i < 64 → t.mem (s.regs 0 + 40#32 + BitVec.ofNat 32 i) = 0#8
  stk : Stk s t.mem

/-- What the state before the first-pass `ldr` of `final` must show: `r4` is the context pointer
and memory is as the `push` left it, so the load reads the entry value. -/
def FF (s z : State) : Prop :=
  z.regs 4 = s.regs 0 ∧
    z.mem = storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]

theorem fPro_split : fPro = fPro.take 5 ++ fPro.drop 5 := (List.take_append_drop 5 fPro).symm
theorem fPro5_split : fPro.take 5 = (fPro.take 5).dropLast ++ [ldrU2] := by decide
theorem fPro5_drop : (fPro.take 5).dropLast = fPro.take 4 := by decide
theorem fpro_all : fPro.take 4 ++ [ldrU2] ++ fPro.drop 5 = fPro := by decide

theorem fpro_pre {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    FF s (execAll (fPro.take 4) s) := by
  obtain ⟨-, r4, -, -, -, -, -, -, rmem, -⟩ := pro_eff e
  have hx : execAll fPro s = execAll (fPro.drop 4) (execAll (fPro.take 4) s) := by
    rw [← execAll_append, List.take_append_drop]
  rw [hx] at r4 rmem
  refine ⟨?_, ?_⟩
  · rw [← r4]
    exact (execAll_regs_other (fPro.drop 4) _ 4 (by decide) (by decide)).symm
  · rw [← rmem]
    exact (execAll_mem (fPro.drop 4) _ (by decide)).symm

theorem fpro5_r4 {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    (execAll (fPro.take 5) s).regs 4 = s.regs 0 := by
  obtain ⟨-, r4, -⟩ := pro_eff e
  have hx : execAll fPro s = execAll (fPro.drop 5) (execAll (fPro.take 5) s) := by
    rw [← execAll_append, List.take_append_drop]
  rw [hx] at r4
  rw [← r4]
  exact (execAll_regs_other (fPro.drop 5) _ 4 (by decide) (by decide)).symm

theorem fpro5_hn : NoLdrBlock (fPro.drop 5) = true := by decide
theorem fpro5_nosite : ∀ off ∈ allSites, off < fStart ∨ fStart + seqSize fPro ≤ off := by decide +kernel

theorem pad_reachS {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    {Q : State → Prop}
    (K : ∀ t : State, t.pc = base + BitVec.ofNat 32 oFComp → PadOut s st t →
      ReachS base (PNR ldAll (WF base s) (CtxRF s)) t Q) :
    ReachS base (PL2R ldAll (WF base s) (FF s) (CtxRF s)) s Q := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  obtain ⟨r13, r4, r5, r6, r0, r1, r2, rhi, rmem, rpc⟩ := pro_eff e
  obtain ⟨cd1, cd2, cd3⟩ := e.codeC
  obtain ⟨g1, g2, g3⟩ := e.cF
  have hspn := (s.regs 13).isLt
  have hseq5 := fPro_at
  rw [fPro_split, seqAt_append, Bool.and_eq_true] at hseq5
  refine ReachS.symBlockWL2R (Ld := ldAll) (FF s) hb2 [((13 : Reg), 4), ((0 : Reg), 4)]
    [((13 : Reg), (0#32 - 20#32), 20)] [((0 : Reg), (104#32 : Word), 4)]
    (fPro.take 5) fStart e.pc (by decide) hseq5.1 (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel)
    fPro5_split (by rw [fPro5_drop]; decide) (by rw [fPro5_drop]; exact fpro_pre e) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact e.sp4
    · exact e.c4
  · intro p hp o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    have ho' : o < 20 := ho
    have hj' : j < seqSize fPro := by
      have : seqSize (fPro.take 5) ≤ seqSize fPro := by decide
      omega
    have := wr_frame s (STREAM_LOCALS + o) (by omega)
    rw [show s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 (STREAM_LOCALS + o) = s.regs 13 + (0#32 - 20#32) + BitVec.ofNat 32 o by
      rw [← ofNat_add_assoc]; bv_omega] at this
    exact WF_nosite (not_siteAt_range (a := fStart) (n := seqSize fPro) (by decide +kernel) fpro5_nosite hj') this
  · apply rr_one
    intro o ho
    have ho' : o < 4 := ho
    exact ⟨104 + o, by omega, by rw [← ofNat_add_assoc]⟩
  refine ReachS.mono (P := PNR ldAll (WF base s) (CtxRF s)) ?_ (fun _ _ h => PNR.toPL2R _ h) (fun _ h => h)
  have hpc2 : (execAll (fPro.take 5) s).pc = base + BitVec.ofNat 32 (fStart + seqSize (fPro.take 5)) := by
    rw [execAll_pc _ _ (by decide), e.pc, ofNat_add_assoc]
  refine ReachS.symBlockWNR (Ld := ldAll) hb2 [((4 : Reg), 4)] [] [((4 : Reg), (32#32 : Word), 8)] (fPro.drop 5)
    (fStart + seqSize (fPro.take 5)) hpc2
    (by have : seqSize (fPro.take 5) % 2 = 0 := by decide
        have : fStart % 2 = 0 := by decide
        omega) hseq5.2 (by decide) ?_ (by simp) ?_ (by decide +kernel) (by decide +kernel) ?_ fpro5_hn
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    show ((execAll (fPro.take 5) s).regs 4).toNat % 4 = 0
    rw [fpro5_r4 e]; exact e.c4
  · apply rr_one
    intro o ho
    have ho' : o < 8 := ho
    show CtxRF s ((execAll (fPro.take 5) s).regs 4 + 32#32 + BitVec.ofNat 32 o)
    rw [fpro5_r4 e]
    exact ⟨32 + o, by omega, by rw [← ofNat_add_assoc]⟩
  have hx : execAll (fPro.drop 5) (execAll (fPro.take 5) s) = execAll fPro s := by
    rw [← execAll_append, List.take_append_drop]
  rw [hx]
  have hbuf : (s.regs 0 + 40#32).toNat + 64 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (s.regs 0).isLt; omega
  have hbuf4 : (s.regs 0 + 40#32).toNat % 4 = 0 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (s.regs 0).isLt; have := e.c4; omega
  have hctx : ∀ i < 64, CtxRF s (s.regs 0 + 40#32 + BitVec.ofNat 32 i) := by
    intro i hi
    exact ⟨40 + i, by omega, by rw [← ofNat_add_assoc]⟩
  have hWB : ∀ i < 64, WF base s (base + BitVec.ofNat 32 oPadBBody) (s.regs 0 + 40#32 + BitVec.ofNat 32 i) := by
    intro i hi
    have := WF_ctx (base := base) (a := oPadBBody) (n := 1) (j := 0) (by omega) (by decide +kernel)
      (by decide +kernel) (hctx i hi)
    simpa using this
  have hWW : ∀ i < 64, WF base s (base + BitVec.ofNat 32 oPadWBody) (s.regs 0 + 40#32 + BitVec.ofNat 32 i) := by
    intro i hi
    have := WF_ctx (base := base) (a := oPadWBody) (n := 1) (j := 0) (by omega) (by decide +kernel)
      (by decide +kernel) (hctx i hi)
    simpa using this
  have hplen := e.ctx.plen
  have hpi0 : PI (execAll fPro s).regs (execAll fPro s).mem (s.regs 0 + 40#32) st.pending.length
      st.pending.length (execAll fPro s) := by
    refine ⟨fun _ _ _ _ => rfl, r6, Nat.le_refl _, hplen, ⟨fun i h1 h2 => absurd h2 (by omega), fun y _ => rfl⟩, r0, r1⟩
  have hdj : ∀ i, st.pending.length ≤ i → i < 64 → ∀ o < 20,
      s.regs 13 - 20#32 + BitVec.ofNat 32 o ≠ s.regs 0 + 40#32 + BitVec.ofNat 32 i := by
    intro i h1 h2 o ho he
    have := M0Crypto.Release.Blake2sInit.disj_ne e.cF (i := 40 + i) (j := STREAM_LOCALS + o) (by omega) (by omega)
    apply this
    rw [← ofNat_add_assoc]
    have h20 : s.regs 13 - 20#32 = (s.regs 13 - STREAM_FRAME_W) + BitVec.ofNat 32 STREAM_LOCALS := by bv_omega
    rw [h20, ofNat_add_assoc] at he
    rw [← he]
  have mkout : ∀ t2, PI (execAll fPro s).regs (execAll fPro s).mem (s.regs 0 + 40#32) st.pending.length 64 t2 →
      PadOut s st t2 := by
    intro t hpi
    have hr : ∀ r : Reg, r.val ≠ 6 → r.val ≠ 7 → r.val ≠ 15 → t.regs r = (execAll fPro s).regs r := hpi.1
    have hpz := hpi.2.2.2.2.1
    have hfar : ∀ y, (∀ i, st.pending.length ≤ i → i < 64 → y ≠ s.regs 0 + 40#32 + BitVec.ofNat 32 i) →
        (∀ o < 20, y ≠ s.regs 13 - 20#32 + BitVec.ofNat 32 o) → t.mem y = s.mem y := by
      intro y h1 h2
      rw [hpz.2 y h1, rmem]
      exact m1_far s y h2
    refine ⟨?_, hpi.r0, hpi.r1, ?_, ?_, ?_, ?_, hfar, hpz.1, ?_⟩
    · rw [hr 13 (by decide) (by decide) (by decide), r13]
    · rw [hr 2 (by decide) (by decide) (by decide), hr 3 (by decide) (by decide) (by decide)]; exact r2
    · rw [hr 4 (by decide) (by decide) (by decide), r4]
    · rw [hr 5 (by decide) (by decide) (by decide), r5]
    · intro r h8 h13 h15
      rw [hr r (by omega) (by omega) h15, rhi r (by omega) h13 h15]
    · have hst : Stk s (execAll fPro s).mem := by rw [rmem]; exact stk_M1 s
      apply Stk.of hst
      intro o ho
      rw [hpz.2 _ (fun i h1 h2 => hdj i h1 h2 o ho)]
  exact padB_loop hb2 hbuf hWB (R := (execAll fPro s).regs) (m1 := (execAll fPro s).mem)
    (fun k t hpc hpi hk4 => padW_loop hb2 hbuf hbuf4 hWW (fun t2 hpc2 hpi2 => K t2 hpc2 (mkout t2 hpi2)) k t hpc hpi hk4)
    st.pending.length _ rpc hpi0

theorem stk_eq (s : State) (o : Nat) :
    s.regs 13 - 20#32 + BitVec.ofNat 32 o = (s.regs 13 - STREAM_FRAME_W) + BitVec.ofNat 32 (STREAM_LOCALS + o) := by
  rw [← ofNat_add_assoc]; bv_omega

theorem push_ne {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    {a : Word} {n : Nat} (h : Disj a n (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME) {i : Nat} (hi : i < n) (o : Nat) (ho : o < 20) :
    a + BitVec.ofNat 32 i ≠ s.regs 13 - 20#32 + BitVec.ofNat 32 o := by
  rw [stk_eq]
  exact M0Crypto.Release.Blake2sInit.disj_ne h hi (by omega)

theorem pad_ge (l : List M0Crypto.Spec.Blake2s.Byte) (i : Nat) (h : i < (M0Crypto.Spec.Blake2s.pad l).length)
    (hl : l.length ≤ i) : (M0Crypto.Spec.Blake2s.pad l)[i] = 0#8 := by
  unfold M0Crypto.Spec.Blake2s.pad at h ⊢
  rw [List.getElem_append_right hl]
  simp

theorem pad_bytes {base : Word} {s t : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    (po : PadOut s st t) :
    bytesAt t.mem (s.regs 0 + 40#32) 64 = M0Crypto.Spec.Blake2s.pad st.pending := by
  have hplen := e.ctx.plen
  have hcb := e.ctx.buf
  have hc := e.codeC
  apply List.ext_getElem
  · simp [bytesAt, M0Crypto.Spec.Blake2s.pad]; omega
  · intro i h1 h2
    have hi : i < 64 := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    by_cases hlt : i < st.pending.length
    · have hfar : t.mem (s.regs 0 + 40#32 + BitVec.ofNat 32 i) = s.mem (s.regs 0 + 40#32 + BitVec.ofNat 32 i) := by
        apply po.far
        · intro j hj hj64 he
          have := add_ofNat_inj (s.regs 0 + 40#32) i j (by omega) (by omega) he
          omega
        · intro o ho he
          apply push_ne e e.cF (n := 112) (i := 40 + i) (by omega) o ho
          rw [← he]
          bv_omega
      rw [hfar]
      simp only [M0Crypto.Spec.Blake2s.pad, List.getElem_append_left hlt]
      have := congrArg (fun l => l[i]?) hcb
      simp only [bytesAt, List.getElem?_map, List.getElem?_range, hlt, if_true] at this
      rw [List.getElem?_eq_getElem hlt] at this
      simpa using this
    · rw [po.zero i (by omega) hi]
      exact (pad_ge st.pending i h2 (by omega)).symm

open M0Crypto.Release.Blake2sInit (disj_ne) in
theorem pad_code {base : Word} {s t : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    (po : PadOut s st t) : CodeAt t.mem base B := by
  intro i h
  have hi : i < Artifacts.Release.size := by rw [← B_len]; exact h
  rw [po.far _ ?_ ?_]
  · exact e.code i h
  · intro k _ hk he
    apply disj_ne e.codeC hi (j := 40 + k) (by omega)
    rw [he]; bv_omega
  · intro o ho he
    apply disj_ne e.codeF hi (j := STREAM_LOCALS + o) (by omega)
    rw [he]; exact stk_eq s o

theorem fcall_nosite : ∀ off ∈ allSites, off < oFComp ∨ oFComp + seqSize fCall ≤ off := by decide +kernel
theorem cs_out : ∀ off ∈ M0Crypto.Release.Blake2sCode.compressSites, off ∉ finalOutSites := by decide +kernel
theorem outW_sites : ∀ off ∈ allSites, off < oOutW ∨ oOutW + seqSize outW ≤ off ∨ off ∈ finalOutSites := by
  decide +kernel
theorem outB_sites : ∀ off ∈ allSites, off < oOutB + 2 ∨ oOutB + 2 + 1 ≤ off ∨ off ∈ finalOutSites := by
  decide +kernel

open M0Crypto.Release.Blake2sInit (disj_ne) in
theorem final_k {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    (t : State) (hpc : t.pc = base + BitVec.ofNat 32 oFComp) (po : PadOut s st t) :
    ReachS base (PNR ldAll (WF base s) (CtxRF s)) t (FinalPost s · st) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hcode := pad_code e po
  have hsp : t.regs 13 - COMPRESS_FRAME_W = s.regs 13 - STREAM_FRAME_W := by rw [po.sp]; bv_omega
  have hr1 : t.regs 1 = t.regs 4 + 40#32 := by rw [po.r1, po.r4]
  have hsp4 : (t.regs 13).toNat % 4 = 0 := by
    have := e.sp4; have := e.spLo; rw [po.sp]; bv_omega
  have hspLo : 176 ≤ (t.regs 13).toNat := by
    have := e.spLo; rw [po.sp]; bv_omega
  have hc4 : (t.regs 4).toNat % 4 = 0 := by rw [po.r4]; exact e.c4
  have hv13' : s.regs 13 - 24#32 + 24#32 = s.regs 13 := by bv_omega
  have hWk : ∀ k < 4, ∀ j < seqSize fCall,
      WF base s (base + BitVec.ofNat 32 (oFComp + j)) (t.regs 13 + 0#32 + BitVec.ofNat 32 k) := by
    intro k hk j hj
    have := wr_frame s (COMPRESS_FRAME + k) (by omega)
    rw [show s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 (COMPRESS_FRAME + k) = t.regs 13 + 0#32 + BitVec.ofNat 32 k by
      rw [po.sp, ← ofNat_add_assoc]; bv_omega] at this
    exact WF_nosite (not_siteAt_range (a := oFComp) (n := seqSize fCall) (by decide +kernel) fcall_nosite hj) this
  have hWcall : ∀ pc y, WCall base t pc y → WF base s pc y := by
    rintro pc y ⟨hy, hs⟩
    refine ⟨?_, fun hsite => ?_⟩
    · rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · rw [hsp]; exact wr_frame s o (by omega)
      · rw [po.r4]; exact wr_ctx s o (by omega)
    · obtain ⟨⟨o, ho, rfl⟩, off, hoff, hpcE⟩ := hs hsite
      refine ⟨fun ⟨o3, h3, he3⟩ => ?_, fun _ => ⟨o, by omega, by rw [po.r4]⟩⟩
      have := off_eq (M0Crypto.Release.Blake2sCode.compressSites_lt off hoff) (finalOutSites_lt o3 h3)
        (hpcE.symm.trans he3)
      exact absurd (this ▸ h3) (cs_out off hoff)
  refine ReachS.bind (ReachS.monoQ (call_reach e.base4 hpc hcode po.r0 hr1 po.r2 hsp4 hspLo hc4
    (by rw [po.r4]; exact e.codeC) (by rw [hsp]; exact e.codeF) (by rw [po.r4, hsp]; exact e.cF)
    (fun o ho => ⟨o, ho, by rw [po.r4]⟩) hWk hWcall) ?_)
  intro u hc
  have hu4 : u.regs 4 = s.regs 0 := by rw [hc.keep 4 (by decide) (by decide), po.r4]
  have hu5 : u.regs 5 = s.regs 1 := by rw [hc.keep 5 (by decide) (by decide), po.r5]
  have hu13 : u.regs 13 = s.regs 13 - 24#32 := by rw [hc.sp, po.sp]
  have hD : Disj (u.regs 5) 32 (u.regs 4) 32 := by
    rw [hu4, hu5]
    obtain ⟨a, b, c'⟩ := e.cO
    exact ⟨b, by omega, by omega⟩
  have hWw : ∀ j < seqSize outW, ∀ i < 32,
      WF base s (base + BitVec.ofNat 32 (oOutW + j)) (u.regs 5 + BitVec.ofNat 32 i) := fun j hj i hi =>
    WF_out (a := oOutW) (n := seqSize outW) hj (by decide +kernel) outW_sites ⟨i, hi, by rw [hu5]⟩
  have hWb : ∀ i < 32, WF base s (base + BitVec.ofNat 32 (oOutB + 2)) (u.regs 5 + BitVec.ofNat 32 i) := by
    intro i hi
    have := WF_out (base := base) (a := oOutB + 2) (n := 1) (j := 0) (y := u.regs 5 + BitVec.ofNat 32 i)
      (s := s) (by omega) (by decide +kernel) outB_sites ⟨i, hi, by rw [hu5]⟩
    simpa using this
  refine ReachS.bind (ReachS.monoQ (out_reach hb2 hD (by rw [hu4]; exact e.c4) hWw hWb (fun i hi => ⟨i, by omega, by rw [hu4]⟩) hc.pc) ?_)
  intro v ho
  have hv13 : v.regs 13 = s.regs 13 - 24#32 := by
    rw [ho.hi 13 (by decide) (by decide), hu13]
  have hmemUT : ∀ y, ¬ WrF s y → u.mem y = t.mem y := fun y hy =>
    hc.mem y (fun o' ho' he => hy (by rw [he, hsp]; exact wr_frame s o' (by omega)))
      (fun o' ho' he => hy (by rw [he, po.r4]; exact wr_ctx s o' (by omega)))
  have hmemTS : ∀ y, ¬ WrF s y → t.mem y = s.mem y := fun y hy =>
    po.far y (fun i h1 h2 he => hy (by
        rw [he, show s.regs 0 + 40#32 + BitVec.ofNat 32 i = s.regs 0 + BitVec.ofNat 32 (40 + i) by bv_omega]
        exact wr_ctx s _ (by omega)))
      (fun o ho he => hy (by rw [he, stk_eq]; exact wr_frame s _ (by omega)))
  have hmemVU : ∀ y, ¬ WrF s y → v.mem y = u.mem y := fun y hy =>
    ho.cp.2 y (fun i hi he => hy (by rw [he, hu5]; exact wr_out s i hi))
  have hstk : Stk s v.mem := by
    apply Stk.of po.stk
    intro o' ho'
    rw [ho.cp.2 _ (fun i hi he => by
        rw [hu5] at he
        apply disj_ne e.oF hi (j := STREAM_LOCALS + o') (by omega)
        rw [← he]; exact stk_eq s o')]
    apply hc.mem
    · intro o'' ho'' he
      rw [hsp, stk_eq] at he
      have := add_ofNat_inj _ _ _ (by omega) (by omega) he
      omega
    · intro o'' ho'' he
      rw [po.r4] at he
      apply disj_ne e.cF (i := o'') (j := STREAM_LOCALS + o') (by omega) (by omega)
      rw [← he]; exact stk_eq s o'
  have hbit : (read32 v.mem (v.regs 13 + 4#32 + 16#32)).getLsbD 0 = true := by
    rw [show v.regs 13 + 4#32 + 16#32 = s.regs 13 - 4#32 by rw [hv13]; bv_omega, hstk.2.2.2.2]
    exact e.lr
  refine ReachS.monoQ (ret_reach hb2 ho.pc (by rw [hv13]; have := e.sp4; have := e.spLo; bv_omega) hbit) ?_
  intro w hr
  have hs4 : read32 v.mem (v.regs 13 + 4#32) = s.regs 4 := by
    rw [show v.regs 13 + 4#32 = s.regs 13 - 20#32 by rw [hv13]; bv_omega]; exact hstk.1
  have hs5 : read32 v.mem (v.regs 13 + 4#32 + 4#32) = s.regs 5 := by
    rw [show v.regs 13 + 4#32 + 4#32 = s.regs 13 - 16#32 by rw [hv13]; bv_omega]; exact hstk.2.1
  have hs6 : read32 v.mem (v.regs 13 + 4#32 + 8#32) = s.regs 6 := by
    rw [show v.regs 13 + 4#32 + 8#32 = s.regs 13 - 12#32 by rw [hv13]; bv_omega]; exact hstk.2.2.1
  have hs7 : read32 v.mem (v.regs 13 + 4#32 + 12#32) = s.regs 7 := by
    rw [show v.regs 13 + 4#32 + 12#32 = s.regs 13 - 8#32 by rw [hv13]; bv_omega]; exact hstk.2.2.2.1
  have hhi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → w.regs r = s.regs r := by
    intro r h8 h11
    have n13 : r.val ≠ 13 := by omega
    have n15 : r.val ≠ 15 := by omega
    rw [hr.hi r h8 n13 n15, ho.hi r (by omega) n15, hc.keep r (by omega) h11,
      po.hi r h8 n13 n15]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr.scratch⟩
  · rw [hr.pc, show v.regs 13 + 4#32 + 16#32 = s.regs 13 - 4#32 by rw [hv13]; bv_omega, hstk.2.2.2.2]
  · rw [hr.sp, hv13, hv13']
  · intro r h4 h11
    by_cases c4 : r.val = 4
    · rw [show r = 4 from Fin.ext c4, hr.r4, hs4]
    by_cases c5 : r.val = 5
    · rw [show r = 5 from Fin.ext c5, hr.r5, hs5]
    by_cases c6 : r.val = 6
    · rw [show r = 6 from Fin.ext c6, hr.r6, hs6]
    by_cases c7 : r.val = 7
    · rw [show r = 7 from Fin.ext c7, hr.r7, hs7]
    exact hhi r (by omega) h11
  · have hm32 : ∀ o < 32, t.mem (s.regs 0 + BitVec.ofNat 32 o) = s.mem (s.regs 0 + BitVec.ofNat 32 o) := by
      intro o ho
      apply po.far
      · intro i h1 h2 he
        rw [show s.regs 0 + 40#32 + BitVec.ofNat 32 i = s.regs 0 + BitVec.ofNat 32 (40 + i) by bv_omega] at he
        have := add_ofNat_inj _ _ _ (by omega) (by omega) he
        omega
      · intro o' ho' he
        exact push_ne e e.cF (n := 112) (by omega) o' ho' he
    have hH8 : M0Crypto.Release.Blake2s.arr8 (M0Crypto.Release.Blake2s.wd t.mem (s.regs 0)) = st.h := by
      apply M0Crypto.Release.Blake2sStream.arr8_eq _ _ e.ctx.hsz
      intro i hi
      have := rd_same s.mem t.mem (s.regs 0) 32 hm32 i (by omega)
      unfold M0Crypto.Release.Blake2s.wd
      rw [this]; exact e.ctx.h i hi
    have hH16 : M0Crypto.Release.Blake2s.arr16 (M0Crypto.Release.Blake2s.wd t.mem (s.regs 0 + 40#32)) =
        M0Crypto.Spec.Blake2s.blockWords st.pending :=
      M0Crypto.Release.Blake2sStream.arr16_wd _ _ _ (pad_bytes e po)
    have hdig : bytesAt u.mem (s.regs 0) 32 = M0Crypto.Spec.Blake2s.finish st := by
      unfold M0Crypto.Spec.Blake2s.finish
      apply M0Crypto.Release.Blake2sStream.bytesAt_digest
      · simp [M0Crypto.Spec.Blake2s.compress]
      · intro i hi
        have := hc.hout i hi
        rw [po.r4, hH8, hH16] at this
        exact this
    rw [hr.mem, ← hdig]
    unfold bytesAt
    apply List.map_congr_left
    intro i hi
    have hi' : i < 32 := by simpa using hi
    have := ho.cp.1 i hi'
    rw [hu5, hu4] at this
    exact this
  · intro y hy
    rw [hr.mem, hmemVU y hy, hmemUT y hy, hmemTS y hy]

/-- `m0c_blake2s_final`: from entry, the function returns having written the digest of the stream. -/
theorem final_reachSR {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    ReachS base (PL2R ldAll (WF base s) (FF s) (CtxRF s)) s (FinalPost s · st) :=
  pad_reachS e (final_k e)

theorem final_reachS {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    ReachS base (PL2 (WF base s) (FF s)) s (FinalPost s · st) :=
  (final_reachSR e).mono (fun _ _ h => h.1) (fun _ h => h)

theorem final_reach {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    Reach base (WrF s) s (FinalPost s · st) :=
  ((final_reachS e).mono (P' := PcWr (WF base s)) (fun _ _ h => h.1) (fun _ h => h)).pcWr_mono
    fun _ _ h => h.1

end M0Crypto.Release.Blake2sFinal
