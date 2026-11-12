import M0Crypto.Release.Blake2sUpdateInv
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the compress sites (flush and direct block) as loop-invariant steps -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode (SiteAt not_siteAt_range allSites)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length arr8_eq arr16_wd)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2s (regs_addReg regs_movImm mem_addReg mem_movImm wd arr8 arr16)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1)
open M0Crypto.Spec.Blake2s (absorb compress blockWords pad)
open M0Crypto.Release.Blake2sLd (ldAll)

theorem disj_l {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) {a' : Word} {n' : Nat}
    (h1 : a.toNat ≤ a'.toNat) (h2 : a'.toNat + n' ≤ a.toNat + n) : Disj a' n' b m := by
  obtain ⟨x, y, z⟩ := h
  exact ⟨by omega, y, by omega⟩

theorem disj_r {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) {b' : Word} {m' : Nat}
    (h1 : b.toNat ≤ b'.toNat) (h2 : b'.toNat + m' ≤ b.toNat + m) : Disj a n b' m' := by
  obtain ⟨x, y, z⟩ := h
  exact ⟨x, by omega, by omega⟩

theorem Ag.of_mem {s t u : State} (h : Ag s t) (hm : u.mem = t.mem) : Ag s u :=
  fun y a b => by rw [hm]; exact h y a b

theorem pad_len64 (l : List (BitVec 8)) (h : l.length = 64) : pad l = l := by
  simp [pad, h]

theorem blFlush : Aead.blTarget oFlushBl (blImm oFlushBl cmpStart) = BitVec.ofNat 32 cmpStart := by
  unfold Aead.blTarget; decide +kernel
theorem blDirect : Aead.blTarget oDirectBl (blImm oDirectBl cmpStart) = BitVec.ofNat 32 cmpStart := by
  unfold Aead.blTarget; decide +kernel
theorem blCopy : Aead.blTarget oCopyBl (blImm oCopyBl copyStart) = BitVec.ofNat 32 copyStart := by
  unfold Aead.blTarget; decide +kernel

/-- Registers and memory after a compress site: the new chain, count and an empty buffer. -/
theorem nf_inv {base : Word} {s t t2 v : State} {st0 : SState} {k : Nat} {st : SState} {o : Nat}
    (hI : Inv s st0 t k st) (ht2m : t2.mem = t.mem) (r4 : t2.regs 4 = s.regs 0)
    (r13 : t2.regs 13 = s.regs 13 - 24#32)
    (hv : NfPost base o t2 v) (M : List (BitVec 8)) (hM : arr16 (wd t.mem (t2.regs 1)) = blockWords M)
    (hcnt : st.count + 64 < 2 ^ 64) :
    CtxNU v.mem (s.regs 0) ⟨compress st.h (blockWords M) (st.count + 64) false, st.count + 64, []⟩ ∧
      Ag s v := by
  have hc := ctx_cnt hI.ctx
  have hH8 : arr8 (wd t.mem (s.regs 0)) = st.h := by
    apply arr8_eq _ _ hI.ctx.hsz
    intro i hi
    unfold wd
    exact hI.ctx.h i hi
  refine ⟨⟨?_, ?_, ?_, ?_, hcnt, by simp, by simp [bytesAt]⟩, ?_⟩
  · simp [compress]
  · intro i hi
    have := hv.hout i hi
    rw [r4, ht2m, hH8, hM, hc] at this
    exact this
  · have ht := hv.tot
    rw [r4, ht2m, hc] at ht
    exact (lohi_of_tot _ _ (st.count + 64) hcnt ht).1
  · have ht := hv.tot
    rw [r4, ht2m, hc] at ht
    exact (lohi_of_tot _ _ (st.count + 64) hcnt ht).2
  · intro y hy1 hy2
    have := hv.mem y (fun o ho he => hy2 o (by omega) (by rw [he, r13]; unfold fb; bv_omega))
      (fun o ho he => hy1 o (by omega) (by rw [r4] at he; exact he))
    rw [this, ht2m]
    exact hI.ag y hy1 hy2

def pre1 : List Instr := [.movImm 1 0x28, .addReg 1 1 4]

theorem flushPre_eq : flushPre = pre1 ++ nfBody := rfl

theorem pre1_at : seqAt B oFlush pre1 = true := by
  have h := flush_at
  rw [flushPre_eq, seqAt_append, Bool.and_eq_true] at h
  exact h.1

theorem nfF_at : seqAt B (oFlush + seqSize pre1) nfBody = true := by
  have h := flush_at
  rw [flushPre_eq, seqAt_append, Bool.and_eq_true] at h
  exact h.2

theorem clrUsed_at : seqAt B oClrUsed clrUsed = true := by rw [seqAt_eq_scan]; decide +kernel

theorem flush_end : oFlush + seqSize pre1 + seqSize nfBody = oFlushBl := by decide

theorem pre1_eff (t : State) :
    (execAll pre1 t).regs 1 = 40#32 + t.regs 4 ∧
    (∀ r : Reg, r.val ≠ 1 → r.val ≠ 15 → (execAll pre1 t).regs r = t.regs r) ∧
    (execAll pre1 t).mem = t.mem := by
  refine ⟨?_, fun r h1 h15 => execAll_regs_other _ _ r h15 (by simp [pre1, Instr.dsts, Fin.ext_iff]; omega), ?_⟩
  · simp (config := {decide := true}) only [pre1, execAll, regs_movImm, regs_addReg, State.reg,
      ite_true, ite_false]
    try rfl
  · simp (config := {decide := true}) only [pre1, execAll, mem_movImm, mem_addReg]

theorem clr_eff (t : State) :
    (execAll clrUsed t).regs 7 = 0#32 ∧
    (∀ r : Reg, r.val ≠ 7 → r.val ≠ 15 → (execAll clrUsed t).regs r = t.regs r) ∧
    (execAll clrUsed t).mem = t.mem := by
  refine ⟨?_, fun r h1 h15 => execAll_regs_other _ _ r h15 (by simp [clrUsed, Instr.dsts, Fin.ext_iff]; omega), ?_⟩
  · simp (config := {decide := true}) only [clrUsed, execAll, regs_movImm, ite_true, ite_false]
    try rfl
  · simp (config := {decide := true}) only [clrUsed, execAll, mem_movImm]

theorem flush_tl_nosite : ∀ off ∈ allSites,
    off < oFlush + seqSize pre1 + seqSize nfPre + seqSize nfSt ∨
      oFlush + seqSize pre1 + seqSize nfPre + seqSize nfSt + seqSize nfTl ≤ off := by decide +kernel

/-- At the flush site (`used = 64`, input remains): compress the buffer, empty it. -/
theorem flush_reach {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    {t : State} {k : Nat} {st : SState}
    (hpc : t.pc = base + BitVec.ofNat 32 oFlush) (hI : Inv s st0 t k st) (hk : k < nn s)
    (hp : st.pending.length = 64) :
    ReachS base (PNR ldAll (WU base s) (UR s)) t (fun v => v.pc = base + BitVec.ofNat 32 oDT ∧
      ∃ st1, Inv s st0 v k st1 ∧ st1.pending.length < 64) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hcode := code_ag e.code hI.ag e.codeC e.codeF
  refine ReachS.symBlockWNR hb2 [] [] [] pre1 oFlush hpc (by decide) pre1_at (by decide) (by simp) (by simp) (by simp)
    (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨u1, u_o, um⟩ := pre1_eff t
  obtain ⟨t2, ht2⟩ : ∃ x, x = execAll pre1 t := ⟨_, rfl⟩
  rw [← ht2] at u1 u_o um ⊢
  have hpc2 : t2.pc = base + BitVec.ofNat 32 (oFlush + seqSize pre1) := by
    rw [ht2, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
  have r13 : t2.regs 13 = s.regs 13 - 24#32 := by rw [u_o 13 (by decide) (by decide)]; exact hI.r13
  have r4 : t2.regs 4 = s.regs 0 := by rw [u_o 4 (by decide) (by decide)]; exact hI.r4
  have hr1 : t2.regs 1 = s.regs 0 + 40#32 := by rw [u1, hI.r4]; bv_omega
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
  have hblk4 : (t2.regs 1).toNat % 4 = 0 := by rw [hr1, h40]; have := e.c4; omega
  have hcnt64 : st.count + 64 < 2 ^ 64 := by
    have hn : nn s = (s.regs 2).toNat := rfl
    have := hI.tot; have := e.cnt; omega
  have hM : arr16 (wd t.mem (t2.regs 1)) = blockWords st.pending := by
    apply arr16_wd
    rw [hr1, pad_len64 _ hp]
    have := hI.ctx.buf
    rw [hp] at this
    exact this
  have hE := flush_end
  have hcode2 : CodeAt t2.mem base B := by rw [um]; exact hcode
  have cD : Disj (t2.regs 4) 40 (t2.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME := by
    rw [r4, hfr]; exact disj_l hcF (Nat.le_refl _) (by omega)
  refine ReachS.bind (ReachS.monoQ (nf_reachS (W := WU base s) (R := UR s) (t := t2) (oFlush + seqSize pre1) e.base4 hpc2
    (by decide) nfF_at (by rw [hE]; exact flushBl_at) (by rw [hE]; decide) (by rw [hE]; exact blFlush)
    hcode2 hsp4 hspLo hc4 hblk4 (by rw [r4]; exact disj_r e.codeC (Nat.le_refl _) (by omega))
    (by rw [hfr]; exact e.codeF) cD
    (by rw [hr1, hfr]; exact disj_l hcF (by omega) (by omega))
    (by rw [hr1, r4]; exact ⟨by omega, by omega, Or.inr (by omega)⟩)
    (by rw [um, r4, ctx_cnt hI.ctx]; omega)
    (fun k hk j hj => wu_ctx_w s _ _ k r4 (by simp; omega))
    (fun k hk j hj => wu_frame_w s (not_siteAt_range (by decide +kernel) flush_tl_nosite hj) _ _ COMPRESS_FRAME k
      (by rw [r13]; unfold fb; bv_omega) (by omega))
    (fun pc y h => wu_of_cwu hfr r4 h)
    (fun k hk => UR.ctx_at (c := 32) (by rw [r4]) (by omega))
    (fun k hk => UR.ctx_at (c := 40) (by rw [hr1]) (by omega))
    (fun k hk => UR.ctx_at (c := 0) (by rw [r4]; simp) (by omega))) ?_)
  intro v hv
  have hpv : v.pc = base + BitVec.ofNat 32 oClrUsed := by
    rw [hv.pc, hE]; rfl
  obtain ⟨hmc, hmag⟩ := nf_inv (base := base) hI (by rw [um]) r4 r13 hv st.pending hM hcnt64
  refine ReachS.symBlockWNR hb2 [] [] [] clrUsed oClrUsed hpv (by decide) clrUsed_at (by decide) (by simp) (by simp) (by simp)
    (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨w7, wo, wm⟩ := clr_eff v
  have hne : (LL s).drop k ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil, LL, bytesAt_length] at this
    omega
  have hkeep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → v.regs r = t.regs r := fun r h4 h11 => by
    rw [hv.keep r h4 h11]
    by_cases h1 : r.val = 1
    · omega
    · exact u_o r h1 (by omega)
  refine ReachS.done ⟨?_, ⟨compress st.h (blockWords st.pending) (st.count + 64) false, st.count + 64, []⟩, ?_, by simp⟩
  · rw [execAll_pc _ _ (by decide), hpv, ofNat_add_assoc]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hI.kn, ?_, ?_, ?_, ?_⟩
    · rw [wo 4 (by decide) (by decide), hkeep 4 (by decide) (by decide), hI.r4]
    · rw [wo 5 (by decide) (by decide), hkeep 5 (by decide) (by decide), hI.r5]
    · rw [wo 6 (by decide) (by decide), hkeep 6 (by decide) (by decide), hI.r6]
    · rw [w7]; rfl
    · rw [wo 13 (by decide) (by decide), hv.sp, r13]
    · intro r h8 h11
      rw [wo r (by omega) (by omega), hkeep r (by omega) h11, hI.hi r h8 h11]
    · rw [wm]; exact hmc
    · exact Ag.of_mem hmag wm
    · have := hI.tot
      simp only [List.length_nil]
      omega
    · rw [← hI.ab]
      exact (M0Crypto.Spec.Blake2s.absorb_flush st hp _ hne).symm

end M0Crypto.Release.Blake2sUpdate
