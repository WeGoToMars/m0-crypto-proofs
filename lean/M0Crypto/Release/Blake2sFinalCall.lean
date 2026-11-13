import M0Crypto.Release.Blake2sFinalPad
import M0Crypto.Release.Blake2sFinalW
import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFinalOut
import M0Crypto.Release.Blake2sInstr
import M0Crypto.Release.Call
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final`: the compress call -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2s (regs_strSp mem_strSp)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem fcall_eff (t : State) :
    (execAll fCall t).regs 0 = t.regs 4 ∧
    (∀ r : Reg, r ≠ 0 → r.val ≠ 15 → (execAll fCall t).regs r = t.regs r) ∧
    (execAll fCall t).mem = write32 t.mem (t.regs 13) (~~~(t.regs 0)) := by
  obtain ⟨s1, hs1⟩ : ∃ x, x = (Instr.dp .mvns 0 0).next t := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ x, x = (Instr.strSp 0 0).next s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ x, x = (Instr.addImm3 0 4 0).next s2 := ⟨_, rfl⟩
  have hx : execAll fCall t = s3 := by rw [hs3, hs2, hs1]; rfl
  rw [hx]
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  have a1 : ∀ r : Reg, r ≠ 0 → r.val ≠ 15 → s1.regs r = t.regs r := by
    intro r h0 h15; rw [hs1, regs_mvns _ _ _ _ (n15 r h15)]; exact if_neg (fun h' => h0 h')
  have a2 : ∀ r : Reg, r.val ≠ 15 → s2.regs r = s1.regs r := by
    intro r h15; rw [hs2, regs_strSp _ _ _ _ (n15 r h15)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs3, regs_addImm3 _ _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_
    show s2.regs 4 + _ = _
    rw [a2 4 (by decide), a1 4 (by decide) (by decide)]; simp
  · intro r h0 h15
    rw [hs3, regs_addImm3 _ _ _ _ _ (n15 r h15)]
    refine (if_neg (fun h' => h0 h')).trans ?_
    rw [a2 r h15, a1 r h0 h15]
  · rw [hs3, mem_addImm3, hs2, mem_strSp, hs1, mem_mvns]
    have e13 : s1.sp = t.regs 13 := by
      show s1.regs 13 = _; exact a1 13 (by decide) (by decide)
    have e0 : s1.reg 0 = ~~~(t.regs 0) := by
      show s1.regs 0 = _
      rw [hs1, regs_mvns _ _ _ _ (by decide)]; exact if_pos rfl
    rw [← hs1, e13, e0]; simp

open M0Crypto.Release.Blake2sInit (disj_ne w32_other)
open M0Crypto.Release.Blake2s (wd arr8 arr16)
open M0Crypto.Release.Blake2sCompress (Entry Post WrOf fpOf Mw compress_reach compress_reachS compress_reachSR)
open M0Crypto.Release.Blake2sCode (SiteAt compressSites)

theorem disj_sub {a : Word} {n : Nat} {b : Word} {m n' m' : Nat} (h : Disj a n b m) (h1 : n' ≤ n) (h2 : m' ≤ m) :
    Disj a n' b m' := by
  obtain ⟨g1, g2, g3⟩ := h
  exact ⟨by omega, by omega, by omega⟩

theorem blFinal : Release.blTarget oFBl (blImm oFBl cmpStart) = BitVec.ofNat 32 cmpStart := by
  unfold Release.blTarget; decide +kernel

theorem code_w32 {m : Mem} {base : Word} (hc : CodeAt m base B) (a v : Word)
    (h : ∀ i < B.length, ∀ k < 4, base + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 k) :
    CodeAt (write32 m a v) base B := by
  intro i hi
  rw [w32_other _ _ _ _ (fun k hk => h i hi k hk)]
  exact hc i hi

/-- What the compress call leaves: control after the `bl`, `sp` and `r4`-`r11` kept, the chain
words equal the compression of the padded block, memory otherwise unchanged. -/
structure CallPost (base : Word) (t u : State) (T : Nat) : Prop where
  pc : u.pc = base + BitVec.ofNat 32 oTstO
  sp : u.regs 13 = t.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → u.regs r = t.regs r
  hout : ∀ i < 8, read32 u.mem (t.regs 4 + BitVec.ofNat 32 (4 * i)) =
    (M0Crypto.Spec.Blake2s.compress (arr8 (wd t.mem (t.regs 4))) (arr16 (wd t.mem (t.regs 4 + 40#32))) T true)[i]!
  mem : ∀ y, (∀ o < STREAM_LOCALS, y ≠ t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) →
    (∀ o < 32, y ≠ t.regs 4 + BitVec.ofNat 32 o) → u.mem y = t.mem y

theorem arr8_congr {f g : Nat → Word} (h : ∀ i < 8, f i = g i) : arr8 f = arr8 g := by
  unfold arr8
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem arr16_congr {f g : Nat → Word} (h : ∀ i < 16, f i = g i) : arr16 f = arr16 g := by
  unfold arr16
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]

theorem rd_w32_far (m : Mem) (a v x : Word) (hx : x.toNat + 4 ≤ 2 ^ 32) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (h : x.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ x.toNat) : read32 (write32 m a v) x = read32 m x := by
  apply read32_congr
  intro j hj
  apply w32_other
  intro k hk heq
  have := congrArg BitVec.toNat heq
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

/-- The writes of the call to compress, seen from the state `t` before the `bl`. -/
def WCall (base : Word) (t : State) (pc y : Word) : Prop :=
  (((∃ o < COMPRESS_FRAME, y = t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) ∨ (∃ o < 32, y = t.regs 4 + BitVec.ofNat 32 o)) ∧
    (SiteAt base pc → (∃ o < 32, y = t.regs 4 + BitVec.ofNat 32 o) ∧
      ∃ off ∈ compressSites, pc = base + BitVec.ofNat 32 off))

/-- The call: `~f0` is stored, `bl compress` runs, and control returns just after the call. -/
theorem call_reach {base : Word} {W : Word → Word → Prop} {Rd : Word → Prop} {t : State} {T : Nat}
    (hb4 : base.toNat % 4 = 0) (hpc : t.pc = base + BitVec.ofNat 32 oFComp)
    (hcode : CodeAt t.mem base B)
    (hr0 : t.regs 0 = 0#32) (hr1 : t.regs 1 = t.regs 4 + 40#32)
    (hT : (t.regs 2).toNat + 2 ^ 32 * (t.regs 3).toNat = T)
    (hsp4 : (t.regs 13).toNat % 4 = 0) (hspLo : 176 ≤ (t.regs 13).toNat)
    (hc4 : (t.regs 4).toNat % 4 = 0)
    (codeC : Disj base Artifacts.Release.size (t.regs 4) 112)
    (codeF : Disj base Artifacts.Release.size (t.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME)
    (cF : Disj (t.regs 4) 112 (t.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME)
    (hRd : ∀ o < 112, Rd (t.regs 4 + BitVec.ofNat 32 o))
    (hWk : ∀ k < 4, ∀ j < seqSize fCall, W (base + BitVec.ofNat 32 (oFComp + j)) (t.regs 13 + 0#32 + BitVec.ofNat 32 k))
    (hW : ∀ pc y, WCall base t pc y → W pc y) :
    ReachS base (PNR ldAll W Rd) t (CallPost base t · T) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have hsp := (t.regs 13).isLt
  refine ReachS.symBlockWNR (Ld := ldAll) hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 : Word), 4)] [] fCall oFComp hpc (by decide)
    fCall_at (by decide) (by simp; exact hsp4) ?_ (by simp) (by decide +kernel) (by decide +kernel) ?_
  · intro p hp o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hWk o ho j hj
  obtain ⟨f0, fo, fm⟩ := fcall_eff t
  obtain ⟨u, hu⟩ : ∃ x, x = execAll fCall t := ⟨_, rfl⟩
  rw [← hu] at f0 fo fm ⊢
  have hup : u.pc = base + BitVec.ofNat 32 oFBl := by
    rw [hu, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  have f0' : u.regs 0 = t.regs 4 := f0
  have hv : ~~~(t.regs 0) = 0xFFFFFFFF#32 := by rw [hr0]; rfl
  have hum : u.mem = write32 t.mem (t.regs 13) 0xFFFFFFFF#32 := by rw [fm, hv]
  have ev : ∀ r : Reg, r ≠ 0 → r.val ≠ 15 → u.regs r = t.regs r := fo
  apply ReachS.blPcNR hb2 oFBl cmpStart _ hup (by decide) fBl_at (by decide) blFinal
  obtain ⟨sc, hsc⟩ : ∃ x, x = (u.setReg 14 ((base + BitVec.ofNat 32 (oFBl + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 cmpStart) := ⟨_, rfl⟩
  rw [← hsc]
  have sr : ∀ r : Reg, r ≠ 14 → r.val ≠ 15 → sc.regs r = u.regs r := by
    intro r h14 h15
    rw [hsc, sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl), sr_ne _ _ _ _ h14]
  have scm : sc.mem = u.mem := by rw [hsc]; rfl
  have scpc : sc.pc = base + BitVec.ofNat 32 cmpStart := by rw [hsc, sr_pc]
  have s13 : sc.regs 13 = t.regs 13 := by rw [sr 13 (by decide) (by decide), ev 13 (by decide) (by decide)]
  have s0 : sc.regs 0 = t.regs 4 := by rw [sr 0 (by decide) (by decide), f0']
  have s1 : sc.regs 1 = t.regs 4 + 40#32 := by rw [sr 1 (by decide) (by decide), ev 1 (by decide) (by decide), hr1]
  have s2 : sc.regs 2 = t.regs 2 := by rw [sr 2 (by decide) (by decide), ev 2 (by decide) (by decide)]
  have s3 : sc.regs 3 = t.regs 3 := by rw [sr 3 (by decide) (by decide), ev 3 (by decide) (by decide)]
  have fp : fpOf sc = t.regs 13 - COMPRESS_FRAME_W := by unfold fpOf; rw [s13]
  have tpos : (t.regs 13 - COMPRESS_FRAME_W).toNat = (t.regs 13).toNat - COMPRESS_FRAME := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e : Entry base sc := by
    refine ⟨hb4, scpc, ?_, by rw [s13]; exact hsp4, by rw [s13]; omega, by rw [s0]; exact hc4,
      by rw [s1]; have := hc4; bv_omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [scm, hum]
      apply code_w32 hcode
      intro i hi k hk
      have := disj_ne codeF (i := i) (j := COMPRESS_FRAME + k) (by rw [B_len] at hi; exact hi) (by omega)
      rw [show t.regs 13 = (t.regs 13 - COMPRESS_FRAME_W) + BitVec.ofNat 32 COMPRESS_FRAME by bv_omega, ofNat_add_assoc]
      exact this
    · have h14 : sc.regs 14 = (base + BitVec.ofNat 32 (oFBl + 4)) ||| 1#32 := by
        rw [hsc, sr_ne _ _ _ _ (by decide)]; simp [State.setReg]
      rw [h14]; exact M0Crypto.Release.lr_odd _
    · rw [fp]; exact codeF |> fun h => disj_sub h (Nat.le_refl _) (by omega)
    · rw [s0]; exact disj_sub codeC (Nat.le_refl _) (by omega)
    · rw [s0, fp]; exact disj_sub cF (by omega) (by omega)
    · rw [s1, fp]
      obtain ⟨g1, g2, g3⟩ := cF
      have h40 : (t.regs 4 + 40#32).toNat = (t.regs 4).toNat + 40 := toNat_add_ofNat _ 40 (by omega)
      refine ⟨by omega, by omega, ?_⟩
      omega
    · rw [scm, hum, s13]
      right; exact M0Crypto.Armv6M.read32_write32_same _ _ _
  have h14 : sc.regs 14 = (base + BitVec.ofNat 32 (oFBl + 4)) ||| 1#32 := by
    rw [hsc, sr_ne _ _ _ _ (by decide)]; simp [State.setReg]
  obtain ⟨g1, g2, g3⟩ := cF
  obtain ⟨k1, k2, k3⟩ := codeC
  have h40 : (t.regs 4 + 40#32).toNat = (t.regs 4).toNat + 40 := toNat_add_ofNat _ 40 (by omega)
  have wdc : ∀ a : Word, a.toNat + 64 ≤ 2 ^ 32 → (a.toNat + 64 ≤ (t.regs 13).toNat - COMPRESS_FRAME ∨ (t.regs 13).toNat + 4 ≤ a.toNat) →
      ∀ i, i < 16 → wd sc.mem a i = wd t.mem a i := by
    intro a ha hd i hi
    unfold wd
    rw [scm, hum]
    have hai : (a + BitVec.ofNat 32 (4 * i)).toNat = a.toNat + 4 * i := toNat_add_ofNat _ _ (by omega)
    apply rd_w32_far _ _ _ _ (by omega) (by omega)
    omega
  have hq : ∀ u', Post sc u' → CallPost base t u' T := by
    intro u' hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hp.pc, h14, M0Crypto.Release.lr_mask]
      · rw [show oFBl + 4 = oTstO by decide]
      · have hlt : oFBl + 4 < Artifacts.Release.size := by decide
        rw [toNat_add_ofNat _ _ (by omega)]
        have : base.toNat % 2 = 0 := hb2
        have : (oFBl + 4) % 2 = 0 := by decide
        omega
    · rw [hp.sp, s13]
    · intro r h4 h11
      have hn0 : r ≠ 0 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
      have hn14 : r ≠ 14 := fun h => by rw [h] at h11; exact absurd h11 (by decide)
      have hn15 : r.val ≠ 15 := by omega
      have hcases : ∀ q : Reg, 4 ≤ q.val → q.val ≤ 11 → q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by
        decide
      have : u'.regs r = sc.regs r := by
        rcases hcases r h4 h11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hp.r4
        · exact hp.r5
        · exact hp.r6
        · exact hp.r7
        · exact hp.r8
        · exact hp.r9
        · exact hp.r10
        · exact hp.r11
      rw [this, sr r hn14 hn15, ev r hn0 hn15]
    · intro i hi
      have hh := hp.hout i hi
      rw [s0] at hh
      have hc0 : arr8 (wd sc.mem (t.regs 4)) = arr8 (wd t.mem (t.regs 4)) :=
        arr8_congr (fun j hj => wdc _ (by omega) (by omega) j (by omega))
      have hc1 : arr16 (Mw sc) = arr16 (wd t.mem (t.regs 4 + 40#32)) := by
        unfold Mw; rw [s1]
        exact arr16_congr (fun j hj => wdc _ (by omega) (by omega) j hj)
      have hf : decide (read32 sc.mem (sc.regs 13) ≠ 0#32) = true := by
        rw [scm, hum, s13, M0Crypto.Armv6M.read32_write32_same]; decide
      have hT' : (sc.regs 2).toNat + 2 ^ 32 * (sc.regs 3).toNat = T := by rw [s2, s3]; exact hT
      rw [hh, hc0, hc1, hf, hT']
    · intro y hy1 hy2
      have := hp.mem y (by intro o ho; rw [fp]; exact hy1 o (by omega))
        (by intro o ho; rw [s0]; exact hy2 o ho)
      rw [this, scm, hum]
      apply w32_other
      intro k hk heq
      apply hy1 (COMPRESS_FRAME + k) (by omega)
      rw [heq]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine (compress_reachSR e (CallPost base t · T) hq).mono (fun _ ev hp => ⟨⟨fun y hy => hW _ _ ?_, hp.1.2⟩,
    fun hl y hy => by
      rcases hp.2 (show Blake2sCompress.cLd ev.instr = true from hl) y hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · rw [s1, ofNat_add_assoc]; exact hRd _ (by omega)
      · rw [s0]; exact hRd _ (by omega)⟩) (fun _ h => h)
  obtain ⟨hw, hs⟩ := hp.1.1 y hy
  refine ⟨?_, fun hsite => ?_⟩
  · rcases hw with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
    · exact Or.inl ⟨o, ho, by rw [fp]⟩
    · exact Or.inr ⟨o, ho, by rw [s0]⟩
  · obtain ⟨⟨o, ho, rfl⟩, hc⟩ := hs hsite
    exact ⟨⟨o, ho, by rw [s0]⟩, hc⟩
