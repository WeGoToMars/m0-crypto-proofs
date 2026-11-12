import M0Crypto.Release.Blake2sUpdateFlush
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the dispatch between the buffer path and the direct-block loop -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Release.Blake2sFinal (tstO_z tstO_keep tstO_mem)
open M0Crypto.Release.Blake2sLd (ldAll)

theorem cp9 (u : State) : condPassed 9 u = (!u.c || u.z) := rfl
theorem cp8 (u : State) : condPassed 8 u = (u.c && !u.z) := rfl

theorem Inv.same {s : State} {st0 : SState} {t u : State} {k : Nat} {st : SState} (h : Inv s st0 t k st)
    (hr : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → u.regs r = t.regs r) (hm : u.mem = t.mem) :
    Inv s st0 u k st :=
  ⟨by rw [hr 4 (by decide) (by decide)]; exact h.r4, by rw [hr 5 (by decide) (by decide)]; exact h.r5,
   by rw [hr 6 (by decide) (by decide)]; exact h.r6, by rw [hr 7 (by decide) (by decide)]; exact h.r7,
   by rw [hr 13 (by decide) (by decide)]; exact h.r13,
   fun r h8 h11 => by rw [hr r (by omega) (by omega)]; exact h.hi r h8 h11, h.kn,
   by rw [hm]; exact h.ctx, Ag.of_mem h.ag hm, h.tot, h.ab⟩

theorem Inv.setPc {s : State} {st0 : SState} {u : State} {k : Nat} {st : SState} (h : Inv s st0 u k st)
    (v : Word) : Inv s st0 (u.setReg 15 v) k st :=
  h.same (fun r h15 _ => sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)) rfl

/-- Where the loop goes after the flush test: to the buffer path, or to the direct-block loop. -/
def DtPost (base : Word) (s : State) (st0 : SState) (k : Nat) (v : State) : Prop :=
  (v.pc = base + BitVec.ofNat 32 oBuf ∧ ∃ st', Inv s st0 v k st' ∧ st'.pending.length < 64) ∨
  (v.pc = base + BitVec.ofNat 32 oDirect ∧ ∃ st', Inv s st0 v k st' ∧ st'.pending.length = 0 ∧
    64 < nn s - k ∧ (v.regs 5).toNat % 4 = 0)

theorem dt_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState}
    (hpc : t.pc = base + BitVec.ofNat 32 oDT) (hI : Inv s st0 t k st) (hk : k < nn s)
    (hlt : st.pending.length < 64) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (DtPost base s st0 k) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : nn s = (s.regs 2).toNat := rfl
  have hn32 := (s.regs 2).isLt
  -- `cmp r7, #0; bne buffer`
  refine ReachS.symBlockWNR hb2 [] [] [] cmpU0 oDT hpc (by decide) cmpU0_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨ac, az, am, ar⟩ := cmp_eff 7 0 t
  obtain ⟨u1, hu1⟩ : ∃ x, x = execAll cmpU0 t := ⟨_, rfl⟩
  have az' : u1.z = (t.regs 7 == (0 : BitVec 8).setWidth 32) := by rw [hu1]; exact az
  have hI1 : Inv s st0 u1 k st := hI.same (fun r h15 _ => by rw [hu1]; exact ar r h15) (by rw [hu1]; exact am)
  have hp1 : u1.pc = base + BitVec.ofNat 32 oDTBne1 := by
    rw [hu1, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  rw [← hu1]
  apply ReachS.bcondPcNR hb2 oDTBne1 oBuf 1 (brImm8 oDTBne1 oBuf) hp1 (by decide +kernel) dtBne1_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    exact ReachS.done (Or.inl ⟨by rw [sr_pc], st, hI1.setPc _, hlt⟩)
  · intro hc
    rw [cp1] at hc
    have hz : u1.z = true := by simpa using hc
    have hpl : st.pending.length = 0 := by
      rw [az', hI.r7] at hz
      have := beq_iff_eq.mp hz
      have h2 := congrArg BitVec.toNat this
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth] at h2
      have : st.pending.length ≤ 64 := hI.ctx.plen
      simp at h2
      omega
    -- `cmp r6, #64; bls buffer`
    obtain ⟨u2, hu2⟩ : ∃ x, x = u1.setReg 15 (base + BitVec.ofNat 32 (oDTBne1 + 2)) := ⟨_, rfl⟩
    rw [← hu2]
    have hI2 : Inv s st0 u2 k st := by rw [hu2]; exact hI1.setPc _
    have hp2 : u2.pc = base + BitVec.ofNat 32 oDTCmp := by
      rw [hu2, sr_pc, show oDTBne1 + 2 = oDTCmp by decide]
    refine ReachS.symBlockWNR hb2 [] [] [] cmpN64 oDTCmp hp2 (by decide) cmpN64_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨bc, bz, bm, br⟩ := cmp_eff 6 0x40 u2
    obtain ⟨u3, hu3⟩ : ∃ x, x = execAll cmpN64 u2 := ⟨_, rfl⟩
    have bc' : u3.c = decide ((0x40 : BitVec 8).toNat ≤ (u2.regs 6).toNat) := by rw [hu3]; exact bc
    have bz' : u3.z = (u2.regs 6 == (0x40 : BitVec 8).setWidth 32) := by rw [hu3]; exact bz
    have hI3 : Inv s st0 u3 k st := hI2.same (fun r h15 _ => by rw [hu3]; exact br r h15) (by rw [hu3]; exact bm)
    have hp3 : u3.pc = base + BitVec.ofNat 32 oDTBls := by
      rw [hu3, execAll_pc _ _ (by decide), hp2, ofNat_add_assoc]; rfl
    rw [← hu3]
    have hr6 : (u3.regs 6).toNat = nn s - k := by
      have h6 : u3.regs 6 = BitVec.ofNat 32 (nn s - k) := by rw [hI3.r6]
      rw [h6, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      omega
    have hr6' : (u2.regs 6).toNat = nn s - k := by
      have h6 : u2.regs 6 = u3.regs 6 := by rw [hu3]; exact (br 6 (by decide)).symm
      rw [h6, hr6]
    apply ReachS.bcondPcNR hb2 oDTBls oBuf 9 (brImm8 oDTBls oBuf) hp3 (by decide +kernel) dtBls_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      exact ReachS.done (Or.inl ⟨by rw [sr_pc], st, hI3.setPc _, hlt⟩)
    · intro hc
      rw [cp9] at hc
      have hgt : 64 < nn s - k := by
        have hcz : u3.c = true ∧ u3.z = false := by
          revert hc
          cases u3.c <;> cases u3.z <;> simp
        rw [bc'] at hcz
        rw [bz'] at hcz
        have h1 := hcz.1
        have h2 := hcz.2
        simp only [decide_eq_true_eq] at h1
        have h3 : ¬ (u2.regs 6 = (0x40 : BitVec 8).setWidth 32) := fun h => by
          rw [h] at h2; simp at h2
        have h4 : (u2.regs 6).toNat ≠ 64 := by
          intro h
          apply h3
          apply BitVec.eq_of_toNat_eq
          rw [h]; rfl
        have : (0x40 : BitVec 8).toNat = 64 := rfl
        omega
      -- `lsls r0, r5, #30; bne buffer`
      obtain ⟨u4, hu4⟩ : ∃ x, x = u3.setReg 15 (base + BitVec.ofNat 32 (oDTBls + 2)) := ⟨_, rfl⟩
      rw [← hu4]
      have hI4 : Inv s st0 u4 k st := by rw [hu4]; exact hI3.setPc _
      have hp4 : u4.pc = base + BitVec.ofNat 32 oDTTst := by
        rw [hu4, sr_pc, show oDTBls + 2 = oDTTst by decide]
      refine ReachS.symBlockWNR hb2 [] [] [] tstP oDTTst hp4 (by decide) tstP_at (by decide) (by simp) (by simp)
        (by simp) (by decide +kernel) (by decide +kernel) ?_
      obtain ⟨u5, hu5⟩ : ∃ x, x = execAll tstP u4 := ⟨_, rfl⟩
      have dz : u5.z = decide ((u4.regs 5).toNat % 4 = 0) := by rw [hu5]; exact tstO_z u4
      have hI5 : Inv s st0 u5 k st := hI4.same (fun r h15 h0 => by rw [hu5]; exact tstO_keep u4 r h15 h0)
        (by rw [hu5]; exact tstO_mem u4)
      have hp5 : u5.pc = base + BitVec.ofNat 32 oDTBne2 := by
        rw [hu5, execAll_pc _ _ (by decide), hp4, ofNat_add_assoc]; rfl
      rw [← hu5]
      apply ReachS.bcondPcNR hb2 oDTBne2 oBuf 1 (brImm8 oDTBne2 oBuf) hp5 (by decide +kernel) dtBne2_at
        (by decide +kernel) (by decide +kernel)
      · intro hc
        exact ReachS.done (Or.inl ⟨by rw [sr_pc], st, hI5.setPc _, hlt⟩)
      · intro hc
        rw [cp1] at hc
        have hz : u5.z = true := by simpa using hc
        rw [dz] at hz
        have hal : (u4.regs 5).toNat % 4 = 0 := by simpa using hz
        refine ReachS.done (Or.inr ⟨by rw [sr_pc, show oDTBne2 + 2 = oDirect by decide], st, hI5.setPc _, hpl, ?_, ?_⟩)
        · exact hgt
        · rw [sr_ne _ _ _ _ (by decide)]
          have : u5.regs 5 = u4.regs 5 := hI5.r5.trans hI4.r5.symm
          rw [this]; exact hal

end M0Crypto.Release.Blake2sUpdate
