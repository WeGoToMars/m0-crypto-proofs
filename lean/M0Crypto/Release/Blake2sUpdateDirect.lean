import M0Crypto.Release.Blake2sUpdateDt
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the direct-block loop -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length arr8_eq arr16_wd)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2s (regs_addReg regs_movImm mem_addReg mem_movImm wd arr8 arr16)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Spec.Blake2s (absorb compress blockWords pad)

theorem regs_subImm8 (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subImm8 d i).next s).regs r = if r = d.toReg then s.reg d - i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Release.sub_flags]

theorem mem_subImm8 (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.subImm8 d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem dirAdv_eff (t : State) :
    (execAll dirAdv t).regs 5 = t.regs 5 + 64#32 ∧ (execAll dirAdv t).regs 6 = t.regs 6 - 64#32 ∧
    (∀ r : Reg, r.val ≠ 5 → r.val ≠ 6 → r.val ≠ 15 → (execAll dirAdv t).regs r = t.regs r) ∧
    (execAll dirAdv t).mem = t.mem ∧
    (execAll dirAdv t).c = decide ((0x40 : BitVec 8).toNat ≤ (t.regs 6 - 64#32).toNat) ∧
    (execAll dirAdv t).z = (t.regs 6 - 64#32 == (0x40 : BitVec 8).setWidth 32) := by
  obtain ⟨a1, ha1⟩ : ∃ x, x = (Instr.addImm8 5 0x40).next t := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ x, x = (Instr.subImm8 6 0x40).next a1 := ⟨_, rfl⟩
  have hx : execAll dirAdv t = (Instr.cmpImm 6 0x40).next a2 := by rw [ha2, ha1]; rfl
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  have a1r5 : a1.regs 5 = t.regs 5 + 64#32 := by
    rw [ha1, regs_addImm8 _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_; rfl
  have a1o : ∀ r : Reg, r.val ≠ 5 → r.val ≠ 15 → a1.regs r = t.regs r := by
    intro r h5 h15
    rw [ha1, regs_addImm8 _ _ _ _ (n15 r h15)]
    exact if_neg (fun h => h5 (by rw [h]; rfl))
  have a1m : a1.mem = t.mem := by rw [ha1, mem_addImm8]
  have a2r6 : a2.regs 6 = t.regs 6 - 64#32 := by
    rw [ha2, regs_subImm8 _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_
    show a1.regs 6 - _ = _
    rw [a1o 6 (by decide) (by decide)]; rfl
  have a2o : ∀ r : Reg, r.val ≠ 6 → r.val ≠ 15 → a2.regs r = a1.regs r := by
    intro r h6 h15
    rw [ha2, regs_subImm8 _ _ _ _ (n15 r h15)]
    exact if_neg (fun h => h6 (by rw [h]; rfl))
  have a2m : a2.mem = a1.mem := by rw [ha2, mem_subImm8]
  obtain ⟨bc, bz, bm, br⟩ := cmp_eff 6 0x40 a2
  have e3 : (Instr.cmpImm 6 0x40).next a2 = execAll [Instr.cmpImm 6 0x40] a2 := rfl
  rw [hx, e3]
  refine ⟨?_, ?_, fun r h5 h6 h15 => ?_, ?_, ?_, ?_⟩
  · rw [br 5 (by decide), a2o 5 (by decide) (by decide), a1r5]
  · rw [br 6 (by decide), a2r6]
  · rw [br r h15, a2o r h6 h15, a1o r h5 h15]
  · rw [bm, a2m, a1m]
  · rw [bc]; have h : a2.regs (LowReg.toReg 6) = t.regs 6 - 64#32 := a2r6; rw [h]
  · rw [bz]; have h : a2.regs (LowReg.toReg 6) = t.regs 6 - 64#32 := a2r6; rw [h]

def pre2 : List Instr := [.lslImm 1 5 0]

theorem dirPre_eq : dirPre = pre2 ++ nfBody := rfl

theorem pre2_at : seqAt B oDirect pre2 = true := by
  have h := direct_at
  rw [dirPre_eq, seqAt_append, Bool.and_eq_true] at h
  exact h.1

theorem nfD_at : seqAt B (oDirect + seqSize pre2) nfBody = true := by
  have h := direct_at
  rw [dirPre_eq, seqAt_append, Bool.and_eq_true] at h
  exact h.2

theorem direct_end : oDirect + seqSize pre2 + seqSize nfBody = oDirectBl := by decide

theorem pre2_eff (t : State) :
    (execAll pre2 t).regs 1 = t.regs 5 ∧
    (∀ r : Reg, r.val ≠ 1 → r.val ≠ 15 → (execAll pre2 t).regs r = t.regs r) ∧
    (execAll pre2 t).mem = t.mem := by
  refine ⟨?_, fun r h1 h15 => execAll_regs_other _ _ r h15 (by simp [pre2, Instr.dsts, Fin.ext_iff]; omega), ?_⟩
  · have e : execAll pre2 t = (Instr.lslImm 1 5 0).next t := rfl
    rw [e, regs_lsl _ _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_
    simp [lslC, State.reg]
    try rfl
  · have e : execAll pre2 t = (Instr.lslImm 1 5 0).next t := rfl
    rw [e, mem_lsl]

theorem disj_ne {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) {i o : Nat}
    (hi : i < n) (ho : o < m) : a + BitVec.ofNat 32 i ≠ b + BitVec.ofNat 32 o := by
  intro he
  have h1 := congrArg BitVec.toNat he
  obtain ⟨x, y, z⟩ := h
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at h1
  omega

theorem bytesAt_slice (m : Mem) (p : Word) (k len n : Nat) (h : k + len ≤ n) :
    ((bytesAt m p n).drop k).take len = bytesAt m (p + BitVec.ofNat 32 k) len := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + len + r := ⟨n - (k + len), by omega⟩
  rw [bytesAt_append, bytesAt_append]
  simp [bytesAt_length]

/-- The direct loop ends in the buffer path, with more input consumed. -/
def DirPost (base : Word) (s : State) (st0 : SState) (k0 : Nat) (v : State) : Prop :=
  v.pc = base + BitVec.ofNat 32 oBuf ∧ ∃ k' st', k0 < k' ∧ k' < nn s ∧ Inv s st0 v k' st' ∧
    st'.pending.length < 64

theorem direct_tl_nosite : ∀ off ∈ allSites,
    off < oDirect + seqSize pre2 + seqSize nfPre + seqSize nfSt ∨
      oDirect + seqSize pre2 + seqSize nfPre + seqSize nfSt + seqSize nfTl ≤ off := by decide +kernel

theorem direct_loop {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    ∀ d : Nat, ∀ (t : State) (k : Nat) (st : SState), nn s - k = d →
      t.pc = base + BitVec.ofNat 32 oDirect → Inv s st0 t k st → st.pending.length = 0 →
      64 < nn s - k → (t.regs 5).toNat % 4 = 0 →
      ReachS base (PNR ldAll (WU base s) (UR s)) t (DirPost base s st0 k) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro t k st hd hpc hI hp hgt hal
  rcases st with ⟨h0, c0, p0⟩
  have hp0 : p0 = [] := by cases p0 <;> simp at hp ⊢
  subst hp0
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : nn s = (s.regs 2).toNat := rfl
  have hn32 := (s.regs 2).isLt
  have hcode := code_ag e.code hI.ag e.codeC e.codeF
  have hpb := e.pF.1
  have hr5n : (t.regs 5).toNat = (s.regs 1).toNat + k := by
    rw [hI.r5, toNat_add_ofNat _ _ (by omega)]
  refine ReachS.symBlockWNR hb2 [] [] [] pre2 oDirect hpc (by decide) pre2_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨u1, u_o, um⟩ := pre2_eff t
  obtain ⟨t2, ht2⟩ : ∃ x, x = execAll pre2 t := ⟨_, rfl⟩
  rw [← ht2] at u1 u_o um ⊢
  have hpc2 : t2.pc = base + BitVec.ofNat 32 (oDirect + seqSize pre2) := by
    rw [ht2, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
  have r13 : t2.regs 13 = s.regs 13 - 24#32 := by rw [u_o 13 (by decide) (by decide)]; exact hI.r13
  have r4 : t2.regs 4 = s.regs 0 := by rw [u_o 4 (by decide) (by decide)]; exact hI.r4
  have hr1 : t2.regs 1 = s.regs 1 + BitVec.ofNat 32 k := by rw [u1]; exact hI.r5
  have hr1n : (t2.regs 1).toNat = (s.regs 1).toNat + k := by rw [u1]; exact hr5n
  have hfr : t2.regs 13 - COMPRESS_FRAME_W = s.regs 13 - STREAM_FRAME_W := by rw [r13]; bv_omega
  have hsn := (s.regs 13).isLt
  have hsp4 : (t2.regs 13).toNat % 4 = 0 := by
    have := e.sp4; have := e.spLo; rw [r13]; bv_omega
  have hspLo : 176 ≤ (t2.regs 13).toNat := by
    have := e.spLo; rw [r13]; bv_omega
  have hc4 : (t2.regs 4).toNat % 4 = 0 := by rw [r4]; exact e.c4
  have hcF := e.cF
  have hcF1 := hcF.1
  have h40 : (s.regs 0 + 40#32).toNat = (s.regs 0).toNat + 40 := toNat_add_ofNat _ 40 (by omega)
  have h32 : (s.regs 0 + 32#32).toNat = (s.regs 0).toNat + 32 := toNat_add_ofNat _ 32 (by omega)
  have hblk4 : (t2.regs 1).toNat % 4 = 0 := by rw [hr1n, ← hr5n]; exact hal
  have hcnt64 : c0 + 64 < 2 ^ 64 := by
    have := hI.tot; have := e.cnt; simp only [List.length_nil] at *; omega
  have hMlen : (((LL s).drop k).take 64).length = 64 := by
    simp only [List.length_take, List.length_drop, LL, bytesAt_length]; omega
  have hM : arr16 (wd t.mem (t2.regs 1)) = blockWords (((LL s).drop k).take 64) := by
    apply arr16_wd
    rw [pad_len64 _ hMlen]
    have e1 : bytesAt t.mem (t2.regs 1) 64 = bytesAt s.mem (t2.regs 1) 64 := by
      apply bytesAt_congr
      intro i hi
      apply hI.ag.eq
      · intro o ho he
        rw [hr1, BitVec.add_assoc, ← BitVec.ofNat_add] at he
        exact disj_ne e.pC (i := k + i) (by omega) ho he
      · intro o ho he
        rw [hr1, BitVec.add_assoc, ← BitVec.ofNat_add] at he
        exact disj_ne e.pF (i := k + i) (by omega) (o := o + 0) (by omega) (by simpa [fb] using he)
    rw [e1, hr1, LL, bytesAt_slice _ _ _ _ _ (by omega)]
  have hE := direct_end
  have hcode2 : CodeAt t2.mem base B := by rw [um]; exact hcode
  have cD : Disj (t2.regs 4) 40 (t2.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME := by
    rw [r4, hfr]; exact disj_l hcF (Nat.le_refl _) (by omega)
  have hblkF : Disj (t2.regs 1) 64 (t2.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME := by
    rw [hfr]; exact disj_l e.pF (by omega) (by omega)
  have hblkC : Disj (t2.regs 1) 64 (t2.regs 4 + 32#32) 8 := by
    rw [r4]
    exact disj_r (disj_l e.pC (by omega) (by omega)) (by omega) (by omega)
  refine ReachS.bind (ReachS.monoQ (nf_reachS (W := WU base s) (R := UR s) (t := t2) (oDirect + seqSize pre2) e.base4 hpc2
    (by decide) nfD_at (by rw [hE]; exact directBl_at) (by rw [hE]; decide) (by rw [hE]; exact blDirect)
    hcode2 hsp4 hspLo hc4 hblk4 (by rw [r4]; exact disj_r e.codeC (Nat.le_refl _) (by omega))
    (by rw [hfr]; exact e.codeF) cD hblkF hblkC
    (by rw [um, r4, ctx_cnt hI.ctx]; omega)
    (fun k hk j hj => wu_ctx_w s _ _ k r4 (by simp; omega))
    (fun k hk j hj => wu_frame_w s (not_siteAt_range (by decide +kernel) direct_tl_nosite hj) _ _ COMPRESS_FRAME k
      (by rw [r13]; unfold fb; bv_omega) (by omega))
    (fun pc y h => wu_of_cwu hfr r4 h)
    (fun j hj => UR.ctx_at (c := 32) (by rw [r4]) (by omega))
    (fun j hj => UR.data_at (c := k) hr1 (by omega))
    (fun j hj => UR.ctx_at (c := 0) (by rw [r4]; simp) (by omega))) ?_)
  intro v hv
  have hpv : v.pc = base + BitVec.ofNat 32 oDirectAdv := by
    rw [hv.pc, hE]; rfl
  obtain ⟨hmc, hmag⟩ := nf_inv (base := base) (st := ⟨h0, c0, []⟩) hI (by rw [um]) r4 r13 hv _ hM hcnt64
  refine ReachS.symBlockWNR hb2 [] [] [] dirAdv oDirectAdv hpv (by decide) dirAdv_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨d5, d6, dO, dm, dc, dz⟩ := dirAdv_eff v
  obtain ⟨w, hw⟩ : ∃ x, x = execAll dirAdv v := ⟨_, rfl⟩
  rw [← hw] at d5 d6 dO dm dc dz ⊢
  have hkeep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → v.regs r = t.regs r := fun r h4 h11 => by
    rw [hv.keep r h4 h11]
    by_cases h1 : r.val = 1
    · omega
    · exact u_o r h1 (by omega)
  have hv6 : v.regs 6 = BitVec.ofNat 32 (nn s - k) := by
    rw [hkeep 6 (by decide) (by decide)]; exact hI.r6
  have hw6 : w.regs 6 = BitVec.ofNat 32 (nn s - (k + 64)) := by
    rw [d6, hv6]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hw6n : (w.regs 6).toNat = nn s - (k + 64) := by
    rw [hw6, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have hIw : Inv s st0 w (k + 64) ⟨compress h0 (blockWords (((LL s).drop k).take 64)) (c0 + 64) false, c0 + 64, []⟩ := by
    refine ⟨?_, ?_, hw6, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
    · rw [dO 4 (by decide) (by decide) (by decide), hkeep 4 (by decide) (by decide), hI.r4]
    · rw [d5, hkeep 5 (by decide) (by decide), hI.r5, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [dO 7 (by decide) (by decide) (by decide), hkeep 7 (by decide) (by decide), hI.r7]
    · rw [dO 13 (by decide) (by decide) (by decide), hv.sp, r13]
    · intro r h8 h11
      rw [dO r (by omega) (by omega) (by omega), hkeep r (by omega) h11, hI.hi r h8 h11]
    · rw [dm]; exact hmc
    · exact Ag.of_mem hmag dm
    · have := hI.tot
      simp only [List.length_nil] at *
      omega
    · rw [← hI.ab]
      have hlen : 64 < ((LL s).drop k).length := by
        simp only [List.length_drop, LL, bytesAt_length]; omega
      rw [M0Crypto.Spec.Blake2s.absorb_direct h0 c0 _ hlen]
      simp only [List.drop_drop]
  have hp5 : (w.regs 5).toNat = (s.regs 1).toNat + (k + 64) := by
    rw [hIw.r5, toNat_add_ofNat _ _ (by omega)]
  have hpcw : w.pc = base + BitVec.ofNat 32 oDirectBhi := by
    rw [hw, execAll_pc _ _ (by decide), hpv, ofNat_add_assoc]; rfl
  apply ReachS.bcondPcNR hb2 oDirectBhi oDirect 8 (brImm8 oDirectBhi oDirect) hpcw (by decide +kernel) directBhi_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    rw [cp8, dc, dz] at hc
    have hgt' : 64 < nn s - (k + 64) := by
      have hcz : (decide ((0x40 : BitVec 8).toNat ≤ (v.regs 6 - 64#32).toNat) = true) ∧
          ¬ ((v.regs 6 - 64#32 == (0x40 : BitVec 8).setWidth 32) = true) := by
        revert hc
        cases decide ((0x40 : BitVec 8).toNat ≤ (v.regs 6 - 64#32).toNat) <;>
          cases (v.regs 6 - 64#32 == (0x40 : BitVec 8).setWidth 32) <;> simp
      obtain ⟨h1, h2⟩ := hcz
      simp only [decide_eq_true_eq] at h1
      have h4 : (v.regs 6 - 64#32).toNat ≠ 64 := by
        intro h
        apply h2
        have : v.regs 6 - 64#32 = (0x40 : BitVec 8).setWidth 32 :=
          BitVec.eq_of_toNat_eq (by rw [h]; rfl)
        rw [this]; simp
      rw [← d6, hw6n] at h1 h4
      have : (0x40 : BitVec 8).toNat = 64 := rfl
      omega
    have := ih (nn s - (k + 64)) (by omega) _ (k + 64) _ rfl (by rw [sr_pc]) (hIw.setPc _) rfl hgt'
      (by rw [sr_ne _ _ _ _ (by decide), hp5]; omega)
    refine ReachS.monoQ this ?_
    rintro v' ⟨hpc', k', st', hk1, hk2, hI', hl⟩
    exact ⟨hpc', k', st', by omega, hk2, hI', hl⟩
  · intro hc
    rw [cp8, dc, dz] at hc
    have hle : nn s - (k + 64) ≤ 64 := by
      have hcz : ¬ (decide ((0x40 : BitVec 8).toNat ≤ (v.regs 6 - 64#32).toNat) = true ∧
          ¬ ((v.regs 6 - 64#32 == (0x40 : BitVec 8).setWidth 32) = true)) := by
        revert hc
        cases decide ((0x40 : BitVec 8).toNat ≤ (v.regs 6 - 64#32).toNat) <;>
          cases (v.regs 6 - 64#32 == (0x40 : BitVec 8).setWidth 32) <;> simp
      rw [← d6, hw6n] at hcz
      have : (0x40 : BitVec 8).toNat = 64 := rfl
      apply Decidable.byContradiction
      intro hgt2
      apply hcz
      refine ⟨?_, ?_⟩
      · simp only [decide_eq_true_eq]; omega
      · intro h3
        have h4 := beq_iff_eq.mp h3
        have h5 := congrArg BitVec.toNat h4
        rw [hw6n] at h5
        simp at h5
        omega
    refine ReachS.done ⟨by rw [sr_pc, show oDirectBhi + 2 = oBuf by decide], k + 64, _, by omega, by omega,
      hIw.setPc _, by simp⟩

end M0Crypto.Release.Blake2sUpdate
