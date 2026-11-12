import M0Crypto.Release.Blake2sUpdateEntry
import M0Crypto.Release.ReachPcL
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_update`: the whole function -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Release.Blake2sStreamEff (regs_ldr mem_ldr)

theorem upro_nosite : ∀ off ∈ allSites, off < uStart ∨ uStart + seqSize uPro ≤ off := by decide +kernel

/-- The state before the prologue's `ldr` (the declared public load): `r4` is the context and memory is
the frame-saved one. -/
def UF (s z : State) : Prop := z.regs 4 = s.regs 0 ∧ z.mem = pm s

theorem uPro_split : uPro = uPro.dropLast ++ [ldrU1] := by decide

theorem upro_pre {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    UF s (execAll uPro.dropLast s) := by
  obtain ⟨-, r4, -, -, -, -, rmem⟩ := upro_eff e
  have hx : execAll uPro s = (Instr.memImm .ldr 7 4 26).next (execAll uPro.dropLast s) := by
    have := execAll_append uPro.dropLast [ldrU1] s
    rw [← uPro_split] at this
    rw [this]; rfl
  rw [hx] at r4 rmem
  refine ⟨?_, ?_⟩
  · rw [← r4, regs_ldr _ _ _ _ _ (by decide), if_neg (by decide)]
  · rw [← rmem, mem_ldr]

theorem update_reachSR {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    ReachS base (PLR ldAll (WU base s) (UF s) (UR s)) s (UpdatePost s st0) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  obtain ⟨r13, r4, r5, r6, r7, rhi, rmem⟩ := upro_eff e
  have hspn := (s.regs 13).isLt
  have hlo := e.spLo
  refine ReachS.symBlockWLR (Ld := ldAll) (UF s) hb2 [((13 : Reg), 4), ((0 : Reg), 4)]
    [((13 : Reg), (0#32 - 20#32), 20)] [((0 : Reg), (104#32 : Word), 4)] uPro uStart e.pc (by decide)
    uPro_at (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) uPro_split (by decide) (upro_pre e)
    (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact e.sp4
    · exact e.c4
  · intro p hp o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    have ho' : o < 20 := ho
    exact wu_frame_w s (not_siteAt_range (by decide +kernel) upro_nosite hj) _ _ STREAM_LOCALS o
      (by unfold fb; bv_omega) (by omega)
  · apply rr_one
    intro o ho
    have ho' : o < 4 := ho
    exact UR.ctx_at (c := 104) rfl (by omega)
  refine ReachS.mono (P := PNR ldAll (WU base s) (UR s)) ?_ (fun _ _ h => PNR.toPLR _ h) (fun _ h => h)
  obtain ⟨x, hx⟩ : ∃ y, y = execAll uPro s := ⟨_, rfl⟩
  rw [← hx] at r13 r4 r5 r6 r7 rhi rmem ⊢
  have hpx : x.pc = base + BitVec.ofNat 32 oUCmp0 := by
    rw [hx, execAll_pc _ _ (by decide), e.pc, ofNat_add_assoc]; rfl
  have hI0 : Inv s st0 x 0 st0 :=
    ⟨r4, by rw [r5]; bv_omega, by rw [r6]; simp [nn], r7, r13, rhi, Nat.zero_le _,
     by rw [rmem]; exact ctxNU_pm e, by intro y _ _; show x.mem y = pm s y; rw [rmem], by omega, by simp⟩
  refine ReachS.symBlockWNR hb2 [] [] [] cmpN0 oUCmp0 hpx (by decide) cmpN0_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨ac, az, am, ar⟩ := cmp_eff 6 0 x
  obtain ⟨u1, hu1⟩ : ∃ y, y = execAll cmpN0 x := ⟨_, rfl⟩
  have az' : u1.z = (x.regs 6 == (0 : BitVec 8).setWidth 32) := by rw [hu1]; exact az
  have hI1 : Inv s st0 u1 0 st0 := hI0.same (fun r h15 _ => by rw [hu1]; exact ar r h15) (by rw [hu1]; exact am)
  have hp1 : u1.pc = base + BitVec.ofNat 32 oUBeqOut := by
    rw [hu1, execAll_pc _ _ (by decide), hpx, ofNat_add_assoc]; rfl
  rw [← hu1]
  apply ReachS.bcondPcNR hb2 oUBeqOut oOut 0 (brImm8 oUBeqOut oOut) hp1 (by decide +kernel) uBeqOut_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    have hz : u1.z = true := by rw [cp0] at hc; simpa using hc
    have hn0 : nn s = 0 := by
      rw [az'] at hz
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      rw [r6] at this
      simp at this
      simpa [nn] using this
    have hI2 := hI1.setPc (base + BitVec.ofNat 32 oOut)
    rw [← hn0] at hI2
    exact out_reach e (by rw [sr_pc]) (by rw [← hn0] at *; exact hI2)
  · intro hc
    have hz : u1.z = false := by rw [cp0] at hc; simpa using hc
    have hk : 0 < nn s := by
      apply Decidable.byContradiction
      intro hge
      have h0 : x.regs 6 = (0 : BitVec 8).setWidth 32 := by
        rw [r6]; apply BitVec.eq_of_toNat_eq; simp [nn] at hge ⊢; omega
      rw [az', h0] at hz
      simp at hz
    refine ReachS.bind (ReachS.monoQ (loop_reach e (nn s) _ 0 st0 (by omega) ?_ (hI1.setPc _) hk) ?_)
    · rw [sr_pc]; rw [show oUBeqOut + 2 = oLoop by decide]
    · rintro v ⟨hpv, st', hI'⟩
      exact out_reach e hpv hI'

theorem update_reachS {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    ReachS base (PL (WU base s) (UF s)) s (UpdatePost s st0) :=
  (update_reachSR e).mono (fun _ _ h => h.1) (fun _ h => h)

theorem update_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    Reach base (WrU s) s (UpdatePost s st0) :=
  ((update_reachS e).mono (P' := PcWr (WU base s)) (fun _ _ h => h.1) (fun _ h => h)).pcWr_mono
    fun _ _ h => h.1

end M0Crypto.Release.Blake2sUpdate
