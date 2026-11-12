import M0Crypto.Release.Blake2sUpdateBuf
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: one loop iteration and the loop -/

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

theorem buf_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState}
    (hpc : t.pc = base + BitVec.ofNat 32 oBuf) (hI : Inv s st0 t k st) (hk : k < nn s)
    (hlt : st.pending.length < 64) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (BufPost base s st0 k) := by
  refine ReachS.bind (ReachS.monoQ (take_reach e hpc hI hk hlt) ?_)
  rintro v ⟨hpv, tk, h1, h2, h3, hr2, hIv⟩
  exact have_reach e hpv hIv h1 h2 h3 hr2

/-- One pass through the loop body ends at `oNext` with more input consumed. -/
theorem iter_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState}
    (hpc : t.pc = base + BitVec.ofNat 32 oLoop) (hI : Inv s st0 t k st) (hk : k < nn s) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (BufPost base s st0 k) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hu := hI.ctx.plen
  -- `cmp r7, #64; bne dispatch`
  refine ReachS.symBlockWNR hb2 [] [] [] cmpU64 oLoop hpc (by decide) cmpU64_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨ac, az, am, ar⟩ := cmp_eff 7 0x40 t
  obtain ⟨u1, hu1⟩ : ∃ x, x = execAll cmpU64 t := ⟨_, rfl⟩
  have az' : u1.z = (t.regs 7 == (0x40 : BitVec 8).setWidth 32) := by rw [hu1]; exact az
  have hI1 : Inv s st0 u1 k st := hI.same (fun r h15 _ => by rw [hu1]; exact ar r h15) (by rw [hu1]; exact am)
  have hp1 : u1.pc = base + BitVec.ofNat 32 oLoopBne := by
    rw [hu1, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  rw [← hu1]
  have hdt : ∀ w : State, w.pc = base + BitVec.ofNat 32 oDT → ∀ st1, Inv s st0 w k st1 →
      st1.pending.length < 64 → ReachS base (PNR ldAll (WU base s) (UR s)) w (BufPost base s st0 k) := by
    intro w hpw st1 hI2 hlt
    refine ReachS.bind (ReachS.monoQ (dt_reach e hpw hI2 hk hlt) ?_)
    rintro v (⟨hpv, st2, hI3, hl3⟩ | ⟨hpv, st2, hI3, hp0, hgt, hal⟩)
    · exact buf_reach e hpv hI3 hk hl3
    · refine ReachS.bind (ReachS.monoQ (direct_loop e _ v k st2 rfl hpv hI3 hp0 hgt hal) ?_)
      rintro x ⟨hpx, k', st', hk1, hk2, hI4, hl4⟩
      refine ReachS.monoQ (buf_reach e hpx hI4 hk2 hl4) ?_
      rintro z ⟨hpz, k'', st'', hk3, hk4, hI5⟩
      exact ⟨hpz, k'', st'', by omega, hk4, hI5⟩
  apply ReachS.bcondPcNR hb2 oLoopBne oDT 1 (brImm8 oLoopBne oDT) hp1 (by decide +kernel) loopBne_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    rw [cp1] at hc
    have hz : u1.z = false := by simpa using hc
    have hne : st.pending.length < 64 := by
      apply Decidable.byContradiction
      intro hge
      have h64 : st.pending.length = 64 := by omega
      rw [az', hI.r7, h64] at hz
      simp at hz
    exact hdt _ (by rw [sr_pc]) st (hI1.setPc _) hne
  · intro hc
    rw [cp1] at hc
    have hz : u1.z = true := by simpa using hc
    have hp64 : st.pending.length = 64 := by
      rw [az', hI.r7] at hz
      have := beq_iff_eq.mp hz
      have h2 := congrArg BitVec.toNat this
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth] at h2
      simp at h2
      omega
    refine ReachS.bind (ReachS.monoQ (flush_reach e (by rw [sr_pc, show oLoopBne + 2 = oFlush by decide])
      (hI1.setPc _) hk hp64) ?_)
    rintro v ⟨hpv, st1, hI2, hl2⟩
    exact hdt v hpv st1 hI2 hl2

/-- The loop ends at `oOut` with all the input consumed. -/
def LoopPost (base : Word) (s : State) (st0 : SState) (v : State) : Prop :=
  v.pc = base + BitVec.ofNat 32 oOut ∧ ∃ st', Inv s st0 v (nn s) st'

theorem loop_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    ∀ d : Nat, ∀ (t : State) (k : Nat) (st : SState), nn s - k = d →
      t.pc = base + BitVec.ofNat 32 oLoop → Inv s st0 t k st → k < nn s →
      ReachS base (PNR ldAll (WU base s) (UR s)) t (LoopPost base s st0) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro t k st hd hpc hI hk
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn32 := (s.regs 2).isLt
  have hnn : nn s = (s.regs 2).toNat := rfl
  refine ReachS.bind (ReachS.monoQ (iter_reach e hpc hI hk) ?_)
  rintro x ⟨hpx, k', st', hk1, hk2, hI'⟩
  -- `cmp r6, #0; bne loop`
  refine ReachS.symBlockWNR hb2 [] [] [] cmpN0 oNext hpx (by decide) next_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨ac, az, am, ar⟩ := cmp_eff 6 0 x
  obtain ⟨u1, hu1⟩ : ∃ y, y = execAll cmpN0 x := ⟨_, rfl⟩
  have az' : u1.z = (x.regs 6 == (0 : BitVec 8).setWidth 32) := by rw [hu1]; exact az
  have hI1 : Inv s st0 u1 k' st' := hI'.same (fun r h15 _ => by rw [hu1]; exact ar r h15) (by rw [hu1]; exact am)
  have hp1 : u1.pc = base + BitVec.ofNat 32 oNextBne := by
    rw [hu1, execAll_pc _ _ (by decide), hpx, ofNat_add_assoc]; rfl
  rw [← hu1]
  have hr6 : (x.regs 6).toNat = nn s - k' := by
    rw [hI'.r6, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  apply ReachS.bcondPcNR hb2 oNextBne oLoop 1 (brImm8 oNextBne oLoop) hp1 (by decide +kernel) nextBne_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    rw [cp1] at hc
    have hz : u1.z = false := by simpa using hc
    have hlt : k' < nn s := by
      apply Decidable.byContradiction
      intro hge
      have : x.regs 6 = (0 : BitVec 8).setWidth 32 := by
        apply BitVec.eq_of_toNat_eq
        rw [hr6]; simp; omega
      rw [az', this] at hz
      simp at hz
    exact ih (nn s - k') (by omega) _ k' st' rfl (by rw [sr_pc]) (hI1.setPc _) hlt
  · intro hc
    rw [cp1] at hc
    have hz : u1.z = true := by simpa using hc
    have hk' : k' = nn s := by
      rw [az'] at hz
      have := beq_iff_eq.mp hz
      have h2 := congrArg BitVec.toNat this
      rw [hr6] at h2
      simp at h2
      omega
    subst hk'
    refine ReachS.done ⟨by rw [sr_pc, show oNextBne + 2 = oOut by decide], st', hI1.setPc _⟩

end M0Crypto.Release.Blake2sUpdate
