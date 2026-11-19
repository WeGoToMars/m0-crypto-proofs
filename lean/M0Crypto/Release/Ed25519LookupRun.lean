import M0Crypto.Release.Ed25519Lookup

set_option linter.unusedSimpArgs false

/-!
# `m0c_ge_lookup`'s call lemma

`lookup_tspec` proves `lookupR` from the pieces of `Ed25519Lookup`: the frame, the header (the
slot values, `hdr_ok`), the block loop (`loopJ` with `Jv`; each pass one block by `ReachFT.sglue`
and the counter step), the identity for digit 0, the masked swap loop, and the calls to `fe_sub`
and `cmov` that negate `2dxy` for a negative digit. Memory facts cross the frames by `keep_simp`.
-/

namespace M0Crypto.Release.Ed25519Lookup

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Artifacts
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Routine
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Ed25519WordLoop (wordR wordPub sel)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

set_option maxHeartbeats 1000000 in
/-- **`m0c_ge_lookup`'s call lemma**, from its callees' and the decided checks. -/
theorem lookup_tspec {o oS szS oC szC oZ : Nat} {cs : List (Nat × Nat)}
    (hS : Routine.TSpec (fun _ : Unit => fieldR oS szS 4 true (· - ·)) (fieldPub true))
    (hC : Routine.TSpec (fun _ : Unit => wordR oC szC 2 true true (fun _ => True) sel [4, 5, 6, 7])
      (wordPub 2))
    (hcode : seqAt B o code = true) (hok : lkOk cs o oS szS oC szC oZ = true) :
    Routine.TSpec (fun _ : Unit => lookupR o cs) lookupPub := by
  simp only [lkOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho4, hcs, hBS, hJ, hL, gH, gP, gC2, gF1, gF2, gF3, gS, g1, hlit, s1, s2, hZ, hZ4, hZ0, hZl⟩ := hok
  have at1 : ∀ {a : Nat} {i : Instr}, sl a 1 = [i] → instrAt B (o + off a) = some i :=
    fun h => instrAt_of_seqAt (h ▸ seqAt_sl hcode _ 1)
  have nx : ∀ {u : State} {a n : Nat} {base : Word} (c : Nat), a + n = c →
      u.pc = base + BitVec.ofNat 32 (o + off a + seqSize (sl a n)) → u.pc = base + BitVec.ofNat 32 (o + off c) :=
    fun c hc h => by rw [h, Nat.add_assoc, off_add, hc]
  have hoB : oBlk % 4 = 0 ∧ oBlk + 4 ≤ 56 := by decide
  have eo : off 0 = 0 ∧ off 1 = 2 ∧ off 2 = 4 ∧ off 213 = off 212 + 2 := by decide +kernel
  trefine Routine.tspec_by (fun _ base s e => ?_) (fun _ _ => ?_)
  generalize hP : lookupPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 13 = P 2 := by subst hP; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h0a, h1a, hdg, hdj⟩ := e.pre
  have F := Caller.of_entry (mask := 0) e
  have i0 := at1 (a := 0) (i := .push 0 true) (by decide +kernel)
  have i1 := at1 (a := 1) (i := .subSp (BitVec.ofNat 7 14)) (by decide +kernel)
  have i212 := at1 (a := 212) (i := .addSp (BitVec.ofNat 7 14)) (by decide +kernel)
  have i213 := at1 (a := 213) (i := .pop 0 true) (by decide +kernel)
  rw [eo.1, Nat.add_zero] at i0; rw [eo.2.1] at i1; rw [eo.2.2.2, ← Nat.add_assoc] at i213
  have : off 212 % 2 = 0 ∧ off 212 + 4 ≤ 432 := by decide +kernel
  trefine ReachFT.frameK (f := lookupR o cs) (mask := 0) (k := 14) (epi := o + off 212) (by decide)
    i0 i1 i212 i213 (by simp only [lookupR]; omega) (by omega) (by omega) (by simp only [lookupR]; omega)
    (rangesSub_trans (ds := [(o, o + 432)]) (by simp [rangesSub, lookupR]; omega) hcs) (by decide)
    (by show 4 * nSaved 0 + 4 * 14 ≤ 64; decide) e q.2.2 ?_
  intro t tpc t13 tr hm hc
  have t13' : t.regs 13 = s.regs 13 - BitVec.ofNat 32 60 := t13
  have hroom := e.room; have hsp4 := e.sp4; have := (s.regs 13).isLt
  have hsC := e.sepCode; have hsW := e.sepWr; have hsR := e.sepRd
  simp only [lookupR, Routine.win, codeR] at hroom hsC hsW hsR
  fp_simp at hsC hsW hsR hdj
  have hlw : lowWin (lookupR o cs) 0 s = ⟨s.regs 13 - BitVec.ofNat 32 64, 60⟩ := by
    simp only [lowWin, lookupR]; rfl
  simp only [hlw] at F ⊢
  have hpcH : t.pc = base + BitVec.ofNat 32 (o + off 2) := by rw [tpc, eo.2.2.1]; rfl
  have tr0 := tr 0 (by decide) (by decide); have tr1 := tr 1 (by decide) (by decide)
  have tr2 := tr 2 (by decide) (by decide)
  -- the header: the slots
  trefine ReachFT.glue F (sl 2 60) _ _ _ (seqAt_sl hcode 2 60) hpcH t13' hc (by glue_tac [t13', lookupR])
    (tr_block [13] hpcH [t13', q.2.2]) (fun hpc1 h131 hc1 hm1 => ?_) gH
  simp only [regions, List.map, t13', BitVec.add_zero] at hm1
  have sv : ∀ (u : State) (j k : Nat) (spec : SExpr), MemEq [⟨s.regs 13 - 60#32 + BitVec.ofNat 32 oBlk, 4⟩,
      ⟨s.regs 0, 16 * j⟩] (execAll (sl 2 60) t).mem u.mem → j ≤ 6 →
      rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS k))) = norm spec →
      k + 4 ≤ 56 → k % 4 = 0 → k ≠ oBlk → read32 u.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 k) = spec.denote t :=
    fun u j k spec hIm hj h hk hk4 hkB => by keep_simp; rw [← t13']; exact sym_rd hdr_ok.1 _ spec h t
  have i174 := at1 (a := 174) (i := .bcond 0 (bcOf 174)) (by decide +kernel)
  have i175 := at1 (a := 175) (i := .b (bOf 175)) (by decide +kernel)
  have e175 : off 175 = off 174 + 2 := by decide +kernel
  rw [show o + off 175 = o + off 174 + 2 by omega] at i175
  trefine loopJ (o := o + off 62) (ob := o + off 174) (ex := o + off 176) (d := 60) F 0 (bcOf 174)
    (bOf 175) i174 i175 6 (Jv (s.regs 13 - 60#32) (s.regs 0) (s.regs 1) (s.regs 2)
      (execAll (sl 2 60) t).mem t.mem) (fun _ _ _ h => Jv_setReg h) ?body
    ?exit hJ 0 (execAll (sl 2 60) t) (by omega) (nx 62 rfl hpc1) ?j0 h131 hc1
  case j0 => exact ⟨MemEq.rfl' _ _, by rw [← t13']; exact sym_rd hdr_ok.1 _ _ hdr_ok.2.2.2.2.2.1 t,
    fun i hi => absurd hi (by omega)⟩
  case body =>
    intro j u hj hpu ⟨hIm, hIc, hIw⟩ h13u hcu
    have sv' := fun k spec h hk hk4 hkB => sv u j k spec hIm (by omega) h hk hk4 hkB
    have hrow : (blkS oRow).denote u = s.regs 1 + BitVec.ofNat 32 (16 * j) := by
      simp only [blkS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13u]
      rw [sv' oRow (.reg0 1) hdr_ok.2.2.1 (by decide) (by decide) (by decide), hIc, shl4]
      simp only [SExpr.denote, tr1]
    have hout : (blkS oOut).denote u = s.regs 0 + BitVec.ofNat 32 (16 * j) := by
      simp only [blkS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13u]
      rw [sv' oOut (.reg0 0) hdr_ok.2.1 (by decide) (by decide) (by decide), hIc, shl4]
      simp only [SExpr.denote, tr0]
    obtain ⟨tP, fC2, zC2, mC2⟩ := pass_ok
    trefine ReachFT.sglue F (sl 62 108) _ _ _ (seqAt_sl hcode 62 108) hpu h13u hcu
      (by glue_tac [h13u, hrow, hout, lookupR]) (traceAll_blockTrE blk_ok.1 tP hpu
        (vs := [P 2 - 60#32, P 1 + BitVec.ofNat 32 (16 * j), P 0 + BitVec.ofNat 32 (16 * j)])
        (by simp only [List.map, hrow, hout]; simp [SExpr.denote, h13u, q])) (fun hpA h13A hcA hmA => ?_) gP
    trefine ReachFT.glue F (sl 170 4) _ _ _ (seqAt_sl hcode 170 4) (nx 170 rfl hpA) h13A hcA
      (by glue_tac [h13A, lookupR]) (tr_block [13] (nx 170 rfl hpA) [h13A, q.2.2]) (fun hpD h13D hcD hmD => ?_) gC2
    simp only [sregions, regions, List.map, hout, h13A] at hmA hmD
    have hcnt : read32 (execAll (sl 62 108) u).mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oBlk) =
        BitVec.ofNat 32 j := by keep_simp; exact hIc
    refine ReachT.done ⟨nx 174 rfl hpD, h13D, hcD, ⟨((hIm.trans hmA).trans hmD).mono
      (by simp only [List.cons_append, List.nil_append]; fp_tac), ?_,
      fun i hi => ?_⟩, ?_⟩
    · have m := sym_rd fC2 _ incS mC2 (execAll (sl 62 108) u)
      simp only [incS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13A, hcnt] at m
      rw [m, ← BitVec.ofNat_add]
    · keep_simp
      by_cases hij : i < 4 * j
      · keep_simp; exact hIw i hij
      obtain ⟨i', rfl⟩ : ∃ i', i = 4 * j + i' := ⟨i - 4 * j, by omega⟩
      have hm : ∀ k < 8, (ldS (oM + 4 * k)).denote u = (maskS (k + 1) (.const (s.regs 2))).denote st0 :=
        fun k hk => by
          simp only [ldS, kS, SExpr.denote, SMem.denote, h13u]
          rw [sv' _ _ (hdr_ok.2.2.2.2.2.2 k hk) (by simp only [oM]; omega) (by simp only [oM]; omega)
            (by simp only [oM, oBlk]; omega), maskS_reg, tr2]
      have w := sym_rd blk_ok.1 _ _ (blk_ok.2 i' (by omega)) u
      simp only [SExpr.denote, kS, hout, ofNat_add_assoc] at w
      rw [show 4 * (4 * j + i') = 16 * j + 4 * i' by omega, w, or_sel hdg hm i' 8 (Nat.le_refl _)]
      by_cases hc : 1 ≤ dIdx (s.regs 2) ∧ dIdx (s.regs 2) ≤ 8
      · simp only [hc, and_self, ↓reduceIte, wS, SExpr.denote, SMem.denote, kS, hrow, ofNat_add_assoc]
        have : 16 * j + (96 * (dIdx (s.regs 2) - 1) + 4 * i') + 4 ≤ 768 := by omega
        keep_simp
        exact congrArg (fun n => read32 t.mem (s.regs 1 + BitVec.ofNat 32 n)) (by omega)
      · simp only [hc, ↓reduceIte]
    · have z := sym_z fC2 _ zC2 (execAll (sl 62 108) u)
      simp only [subS, incS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, sub_flags,
        h13A, hcnt] at z
      rw [show ∀ v : State, condPassed 0 v = v.z from fun _ => rfl, z]
      have : ∀ j < 6, (BitVec.ofNat 32 j + BitVec.ofNat 32 1 - BitVec.ofNat 32 6 == 0#32) =
        decide (j + 1 = 6) := by decide
      exact this j hj
  case exit =>
    rintro w hpw ⟨hWm, -, hWw⟩ h13w hcw
    have ld : ∀ k spec, rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS k))) =
        norm spec → k + 4 ≤ 56 → k % 4 = 0 → k ≠ oBlk → (ldS k).denote w = spec.denote t :=
      fun k spec h hk hk4 hkB => by
        simp only [ldS, kS, SExpr.denote, SMem.denote, h13w]; exact sv w 6 k spec hWm (Nat.le_refl _) h hk hk4 hkB
    have lO : (ldS oOut).denote w = s.regs 0 := by
      rw [ld _ _ hdr_ok.2.1 (by decide) (by decide) (by decide)]; exact tr0
    obtain ⟨fF, tF, mF, rF0, rF1, fF2, mF2, fF3, rF3, rF7⟩ := fix_ok
    -- digit 0: words 0 and 8 receive the zero flag
    trefine ReachFT.sglue F (sl 176 5) _ _ _ (seqAt_sl hcode 176 5) hpw h13w hcw
      (by glue_tac [h13w, lO, lookupR]) (traceAll_blockTrE fF tF hpw (vs := [P 2 - 60#32, P 0])
        (by simp only [List.map, lO]; simp [SExpr.denote, h13w, q])) (fun hp1 h131 hc1 hm1 => ?_) gF1
    have r01 := sym_reg fF _ _ rF0 w; rw [lO] at r01
    trefine ReachFT.glue F (sl 181 3) _ _ _ (seqAt_sl hcode 181 3) (nx 181 rfl hp1) h131 hc1
      (by glue_tac [r01, lookupR]) (tr_block [0] (nx 181 rfl hp1) [r01, q.1]) (fun hp2 h132 hc2 hm2 => ?_) gF2
    trefine ReachFT.glue F (sl 184 2) _ _ _ (seqAt_sl hcode 184 2) (nx 184 rfl hp2) h132 hc2
      (by glue_tac [h132, lookupR, oNeg]) (tr_block [13] (nx 184 rfl hp2) [h132, q.2.2]) (fun hp3 h133 hc3 hm3 => ?_) gF3
    simp only [sregions, regions, List.map, lO, r01, BitVec.add_zero] at hm1 hm2 hm3
    have dg := digit_exit hdg
    have hκ : (sgnS (.reg0 2)).denote t = if dNeg (s.regs 2) then BitVec.allOnes 32 else 0 := by
      rw [← dg.2.1]; simp only [sgnS, rsbS, kS, SExpr.denote, SBool.denote, tr2]
    obtain ⟨κ, hκκ⟩ : ∃ κ, (if dNeg (s.regs 2) then BitVec.allOnes 32 else 0) = κ := ⟨_, rfl⟩
    rw [hκκ] at hκ
    have i197 := at1 (a := 197) (i := .bcond 1 (bcOf 197)) (by decide +kernel)
    trefine ReachFT.loop (o := o + off 186) (ob := o + off 197) (d := 60) F 1 (bcOf 197) i197 8
      (SwI (s.regs 0) κ (execAll (sl 184 2) (execAll (sl 181 3) (execAll (sl 176 5) w))).mem) (fun _ _ _ h => SwI_setReg h)
      ?sbody ?sexit hL 0 _ (by omega) (nx 186 rfl hp3) ?s0 h133 hc3
    case s0 =>
      refine ⟨?_, ?_, ?_, MemEq.rfl' _ _, fun i _ => by simp only [Nat.not_lt_zero, ↓reduceIte, and_self]⟩
      · rw [execAll_regs_other (sl 184 2) _ _ (by decide) (by decide +kernel),
          execAll_regs_other (sl 181 3) _ _ (by decide) (by decide +kernel), r01]; simp
      · rw [sym_reg fF3 _ _ rF3, ← hκ, ← ld _ _ hdr_ok.2.2.2.1 (by decide) (by decide) (by decide)]
        simp only [ldS, kS, SExpr.denote, SMem.denote, h132, h13w, oNeg]; keep_simp
      · rw [sym_reg fF3 _ _ rF7]; rfl
    case sbody =>
      rintro j v hj hpv ⟨r0, r3, r7, hmv, hwv⟩ h13v hcv
      obtain ⟨fS, m0S, m32S, r0S, r3S, r7S, zS'⟩ := swap_ok
      trefine ReachFT.glue F (sl 186 11) _ _ _ (seqAt_sl hcode 186 11) hpv h13v hcv
        (by glue_tac [r0, lookupR]) (tr_block [0] hpv [r0, q.1]) (fun hpe h13e hce hme => ?_) gS
      simp only [regions, List.map, r0, BitVec.add_zero] at hme
      refine ReachT.done ⟨nx 197 rfl hpe, h13e, hce, ⟨?_, ?_, ?_, (hmv.trans hme).mono
        (by simp only [List.cons_append, List.nil_append]; fp_tac), fun i hi => ?_⟩, ?_⟩
      · rw [sym_reg fS _ _ r0S]; simp only [SExpr.denote, SBool.denote, kS, add_flags, r0, ofNat_add_assoc]
        rw [show 4 * j + 4 = 4 * (j + 1) by omega]
      · rw [sym_reg fS _ _ r3S]; exact r3
      · rw [sym_reg fS _ _ r7S]; simp only [subS, SExpr.denote, SBool.denote, sub_flags, r7]
        have : ∀ j < 8, BitVec.ofNat 32 (8 - j) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (8 - (j + 1)) := by decide
        exact this j hj
      · by_cases hij : i = j
        · subst hij
          have e0 := sym_rd fS _ _ m0S v; have e32 := sym_rd fS _ _ m32S v
          simp only [swS, kS, SExpr.denote, SMem.denote, r0, r3, ofNat_add_assoc, Nat.add_zero,
            show 4 * i + 32 = 32 + 4 * i from Nat.add_comm _ _] at e0 e32
          rw [(hwv i hi).1, (hwv i hi).2] at e0 e32; simp only [Nat.lt_irrefl, ↓reduceIte] at e0 e32
          simp only [Nat.lt_succ_self, ↓reduceIte, sel, e0, e32, BitVec.xor_comm (read32 _ (_ + BitVec.ofNat 32 (32 + 4 * i)))]
          exact ⟨trivial, trivial⟩
        · keep_simp only [hme]
          have : (i < j + 1) = (i < j) := by simp only [eq_iff_iff]; omega
          simp only [this]; exact hwv i hi
      · have z := sym_z fS _ zS' v
        simp only [subS, SExpr.denote, SBool.denote, sub_flags, r7] at z
        rw [show ∀ v : State, condPassed 1 v = !v.z from fun _ => rfl, z]
        have : ∀ j < 8, (!(BitVec.ofNat 32 (8 - j) - BitVec.ofNat 32 1 == 0#32)) = decide (j + 1 < 8) := by
          decide
        exact this j hj
    case sexit =>
      rintro x hpx ⟨r0x, r3x, -, hmx, hwx⟩ h13x hcx
      obtain ⟨fN, rN⟩ := neg_ok
      have e1 : off 198 = off 197 + 2 ∧ off 201 = off 200 + 2 ∧ off 212 = off 205 + seqSize (sl 205 6) + 4 := by
        decide +kernel
      have hpx' : x.pc = base + BitVec.ofNat 32 (o + off 198) := by rw [hpx, e1.1, Nat.add_assoc]
      trefine ReachFT.glue F (sl 198 2) _ _ _ (seqAt_sl hcode 198 2) hpx' h13x hcx
        (by glue_tac [h13x, lookupR, oOut]) (tr_block [13] hpx' [h13x, q.2.2]) (fun hp4 h134 hc4 hm4 => ?_) g1
      have lOx : (ldS oOut).denote x = s.regs 0 := by
        rw [← lO]; simp only [ldS, kS, SExpr.denote, SMem.denote, h13x, h13w, oOut]; keep_simp
      have r04 := sym_reg fN _ _ rN x
      simp only [SExpr.denote, SBool.denote, kS, add_flags, lOx] at r04
      simp only [regions, List.map] at hm4
      have i200 := at1 (a := 200) (i := .ldrLit 1 7) (by decide +kernel)
      trefine ReachFT.lit F 1 7 i200 (nx 200 rfl hp4) (Hi.self _) h134 hc4 (by simp only [codeR]; fp_tac)
        (fun y hy hp5 _ h135 hc5 => ?_) hlit
      have hp5' : y.pc = base + BitVec.ofNat 32 (o + off 201) := by rw [hp5, e1.2.1, Nat.add_assoc]
      have i204 := at1 (a := 204) (i := .bl (blOf 204)) (by decide +kernel)
      rw [← (off_add 201 3 : off 201 + seqSize (sl 201 3) = off 204), ← Nat.add_assoc] at i204
      rw [← codeWord_drop] at hZl
      have hz1 : Frame.codeWord (litOff (o + off 200) 7) + (base + BitVec.ofNat 32 (o + off 200 + 2) + 4#32) =
          base + BitVec.ofNat 32 oZ := by
        rw [← hZl, e1.2.1, ← Nat.add_assoc, BitVec.ofNat_add (o + off 200 + 2) 4]
        generalize Frame.codeWord _ = cw; generalize BitVec.ofNat 32 (o + off 200 + 2) = p; ac_rfl
      have y0 : y.regs 0 = s.regs 0 + 96#32 := by
        rw [hy, ← r04]; simp only [litState, State.setReg, M0Crypto.Proofs.toReg_1]; rfl
      have y1 : y.regs 1 + (y.pc + 4#32) = base + BitVec.ofNat 32 oZ := by
        rw [hp5, ← hz1, hy]; rfl
      have ym : y.mem = (execAll (sl 198 2) x).mem := by rw [hy, litState_mem]
      clear hy
      obtain ⟨sF, sR0, sR1, sR2, sR13⟩ := sub_ok
      have a0 := sym_reg sF _ _ sR0 y; have a1 := sym_reg sF _ _ sR1 y
      have a2 := sym_reg sF _ _ sR2 y; have a13 := sym_reg sF _ _ sR13 y
      have xm : (execAll (sl 198 2) x).mem = x.mem := funext fun a =>
        execAll_memEq (wg := []) x fN (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
      simp only [ldS, kS, SExpr.denote, SMem.denote, h13x] at lOx
      simp only [SExpr.denote, SBool.denote, SMem.denote, ldS, kS, add_flags, y0, ym, xm, h135, lOx] at a0 a1 a2 a13
      rw [show y.regs 15 = y.pc from rfl, y1] at a1
      have sp4 := F.sp4; have b4 := F.b4; have c32 := F.code32
      trefine ReachFT.siteK (hS.specT ()) F (sl 201 3) _ _ _ (seqAt_sl hcode 201 3) i204 hp5' (Hi.self _) h135 hc5
        ?ss ?sp (tr_block [13] hp5' [h135, q.2.2])
        (Routine.tr_pub (by simp only [fieldPub, ite_true, atCall, blState_regs (base := base) _ _ _ 0,
          blState_regs (base := base) _ _ _ 1, blState_regs (base := base) _ _ _ 2,
          blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13, q.1, q.2.2] <;> rfl))
        (fun u5 p5 _ s5 c5 m5 q5 => ?_) s1
      case ss =>
        simp only [SiteSides, GlueSides, atCall, Routine.win, fieldR, ite_true, regions, List.map,
          blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
          blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13,
          h135, lookupR, codeR, oOut, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true]
        refine ⟨⟨⟨?_, trivial⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> fp_tac
      case sp =>
        simp only [fieldR, atCall, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
          blState_regs (base := base) _ _ _ 2, a0, a1, a2, ite_true, forall_const, EqOrDisj]
        refine ⟨?_, ?_, ?_, Or.inr ?_, Or.inr ?_⟩ <;> fp_tac
      have ex5 : (execAll (sl 201 3) y).mem = y.mem := funext fun a =>
        execAll_memEq (wg := []) y sF (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
      simp only [regions, List.map, List.nil_append, atCall, Routine.win, fieldR, blState_mem,
        blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
        blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13,
        ex5, ym, xm] at m5 q5
      have e2 : off 205 = off 201 + seqSize (sl 201 3) + 4 := by decide +kernel
      have p5' : u5.pc = base + BitVec.ofNat 32 (o + off 205) := by
        rw [p5, e2, ← Nat.add_assoc, ← Nat.add_assoc]
      have i211 := at1 (a := 211) (i := .bl (blOf 211)) (by decide +kernel)
      rw [← (off_add 205 6 : off 205 + seqSize (sl 205 6) = off 211), ← Nat.add_assoc] at i211
      have l5 : read32 u5.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oOut) = s.regs 0 := by
        rw [← lOx]; simp only [oOut, BitVec.add_zero]; keep_simp
      have κ5 : read32 u5.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oNeg) = κ := by
        rw [← hκ, ← ld _ _ hdr_ok.2.2.2.1 (by decide) (by decide) (by decide)]
        simp only [ldS, kS, SExpr.denote, SMem.denote, h13w, oNeg]; keep_simp
      obtain ⟨cF, cR0, cR1, cR2, cR3, cR13⟩ := cmv_ok
      have b0 := sym_reg cF _ _ cR0 u5; have b1 := sym_reg cF _ _ cR1 u5; have b2 := sym_reg cF _ _ cR2 u5
      have b3 := sym_reg cF _ _ cR3 u5; have b13 := sym_reg cF _ _ cR13 u5
      simp only [SExpr.denote, SBool.denote, SMem.denote, ldS, kS, add_flags, s5, l5, κ5, BitVec.add_zero,
        BitVec.add_assoc, BitVec.reduceAdd] at b0 b1 b2 b3 b13
      trefine ReachFT.siteK (hC.specT ()) F (sl 205 6) _ _ _ (seqAt_sl hcode 205 6) i211 p5' (Hi.self _) s5 c5
        ?cs ?cp (tr_block [13] p5' [s5, q.2.2])
        (Routine.tr_pub (by simp only [wordPub, atCall, blState_regs (base := base) _ _ _ 0,
          blState_regs (base := base) _ _ _ 1, blState_regs (base := base) _ _ _ 2,
          blState_regs (base := base) _ _ _ 13, b0, b1, b2, b13, q.1, q.2.2] <;> rfl))
        (fun u6 p6 _ s6 c6 m6 q6 => ?_) s2
      case cs =>
        simp only [SiteSides, GlueSides, atCall, Routine.win, wordR, ite_true, regions, List.map,
          blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
          blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, b0, b1, b2, b13,
          s5, lookupR, codeR, oOut, oNeg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
          List.cons_append, List.nil_append, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
        refine ⟨⟨⟨?_, trivial⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> fp_tac
      case cp =>
        simp only [wordR, atCall, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
          blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 3, b0, b1, b2, b3, EqOrDisj,
          forall_const, and_true, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
        refine ⟨by simp only [Ed25519WordLoop.WordsOk]; decide, ?_, ?_, Or.inr ?_⟩ <;> fp_tac
      have ex6 : (execAll (sl 205 6) u5).mem = u5.mem := funext fun a =>
        execAll_memEq (wg := []) u5 cF (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
      simp only [regions, List.map, List.nil_append, atCall, Routine.win, wordR, blState_mem,
        blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
        blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 3,
        blState_regs (base := base) _ _ _ 13, b0, b1, b2, b3, b13, ex6, BitVec.toNat_ofNat, Nat.reduceMod,
        Nat.reduceMul] at m6 q6
      refine ReachT.done ⟨by rw [p6, e1.2.2, ← Nat.add_assoc, ← Nat.add_assoc], by rw [s6, t13'],
        fun r h4 h11 _ hK => absurd (mem_hiRegs h4 h11) hK, ?_⟩
      simp only [lookupR]
      have hm' : MemEq [⟨s.regs 13 - BitVec.ofNat 32 4, 4⟩] s.mem t.mem := hm
      have hdA := dg.2.2
      have zw : (ldS Ed25519Lookup.oZ).denote w = if dIdx (s.regs 2) = 0 then 1#32 else 0#32 := by
        rw [ld _ _ hdr_ok.2.2.2.2.1 (by decide) (by decide) (by decide), ← dg.1]
        simp only [zS, subS, absS, sgnS, rsbS, kS, SExpr.denote, SBool.denote, tr2]
      have tw : ∀ i < 24, read32 w.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
          if dIdx (s.regs 2) = 0 then 0
          else read32 s.mem (s.regs 1 + BitVec.ofNat 32 (96 * (dIdx (s.regs 2) - 1) + 4 * i)) := by
        intro i hi
        rw [hWw i (by omega)]
        by_cases h0 : dIdx (s.regs 2) = 0
        · simp [h0]
        · have : 96 * (dIdx (s.regs 2) - 1) + 4 * i + 4 ≤ 768 := by omega
          simp only [h0, ↓reduceIte, show 1 ≤ dIdx (s.regs 2) ∧ dIdx (s.regs 2) ≤ 8 from ⟨by omega, hdA⟩,
            and_self]
          keep_simp
      have M3w : ∀ i < 16, read32 (execAll (sl 184 2) (execAll (sl 181 3) (execAll (sl 176 5) w))).mem
          (s.regs 0 + BitVec.ofNat 32 (4 * i)) = ent s.mem (s.regs 1) (dIdx (s.regs 2)) i := by
        intro i hi
        have ew := tw i (by omega)
        rcases (by omega : i = 0 ∨ i = 8 ∨ (i ≠ 0 ∧ i ≠ 8)) with rfl | rfl | ⟨h0, h8⟩
        · have e := sym_rd fF _ _ mF w
          simp only [SExpr.denote, SMem.denote, kS, lO, zw, Nat.reduceMul, BitVec.add_zero] at e ew ⊢
          keep_simp
          rw [e, ew]; by_cases h : dIdx (s.regs 2) = 0 <;> simp [h, ent]
        · have e := sym_rd fF2 _ _ mF2 (execAll (sl 176 5) w)
          have r1 := sym_reg fF _ _ rF1 w
          simp only [SExpr.denote, SMem.denote, kS, r01, r1, zw] at e
          simp only [Nat.reduceMul] at ew ⊢
          keep_simp; rw [e]; keep_simp; rw [ew]; by_cases h : dIdx (s.regs 2) = 0 <;> simp [h, ent]
        · keep_simp; rw [ew]; by_cases h : dIdx (s.regs 2) = 0 <;> simp [h, ent, h0, h8]
      refine ⟨fun i hi => ?_, ?_⟩
      · have h32 : 32 + 4 * i = 4 * (i + 8) := by omega
        have k0 : read32 u6.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
            read32 x.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) := by keep_simp
        have k8 : read32 u6.mem (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) =
            read32 x.mem (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) := by keep_simp
        rw [k0, k8, (hwx i hi).1, (hwx i hi).2]
        simp only [hi, ↓reduceIte, h32, M3w i (by omega), M3w (i + 8) (by omega), ← hκκ]
        rcases Bool.eq_false_or_eq_true (dNeg (s.regs 2)) with hn | hn <;>
          simp only [hn, ↓reduceIte, Bool.false_eq_true, Ed25519WordLoop.sel_zero, Ed25519WordLoop.sel_ones, and_self]
      · have z0 : feVal x.mem (base + BitVec.ofNat 32 oZ) = 0 := feVal_zeroes fun i hi => by
          rw [ofNat_add_assoc, Frame.read32_code hcx _ (by omega), codeWord_zero hZ0 hi]
        have xw : ∀ i < 8, read32 x.mem (s.regs 0 + 64#32 + BitVec.ofNat 32 (4 * i)) =
            if dIdx (s.regs 2) = 0 then 0
            else read32 s.mem (s.regs 1 + BitVec.ofNat 32 (96 * (dIdx (s.regs 2) - 1) + 64) + BitVec.ofNat 32 (4 * i)) :=
          fun i hi => by
            rw [ofNat_add_assoc, ofNat_add_assoc, show 64 + 4 * i = 4 * (i + 16) by omega]; keep_simp
            rw [tw _ (by omega), show 96 * (dIdx (s.regs 2) - 1) + 64 + 4 * i =
              96 * (dIdx (s.regs 2) - 1) + 4 * (i + 16) by omega]
        have f64 : (feVal x.mem (s.regs 0 + 64#32) : Int) = tdX s.mem (s.regs 1) (dIdx (s.regs 2)) := by
          by_cases h0 : dIdx (s.regs 2) = 0
          · simp only [tdX, h0, ↓reduceIte]
            rw [feVal_zeroes fun i hi => by rw [xw i hi]; simp only [h0, ↓reduceIte]]; rfl
          · simp only [tdX, h0, ↓reduceIte]
            exact congrArg _ (feVal_congr fun i hi => by rw [xw i hi]; simp only [h0, ↓reduceIte])
        rcases Bool.eq_false_or_eq_true (dNeg (s.regs 2)) with hn | hn
        · have f6 : feVal u6.mem (s.regs 0 + 64#32) = feVal u5.mem (s.regs 0 + 96#32) :=
            feVal_congr fun i hi => by rw [q6 i hi, ← hκκ]; simp only [hn, ↓reduceIte, Ed25519WordLoop.sel_ones]
          have q := q5; rw [z0, f64] at q
          simp only [hn, ↓reduceIte, f6]; simpa only [Int.natCast_zero, Int.zero_sub] using q
        · have f6 : feVal u6.mem (s.regs 0 + 64#32) = feVal x.mem (s.regs 0 + 64#32) :=
            feVal_congr fun i hi => by
              rw [q6 i hi, ← hκκ]; simp only [hn, Bool.false_eq_true, ↓reduceIte, Ed25519WordLoop.sel_zero]; keep_simp
          simp only [hn, Bool.false_eq_true, ↓reduceIte, f6, f64]; rfl
  uniq_tac

end

/-- `m0c_ge_lookup` in each build. -/
theorem ge_lookup_tspec (b : Ed25519.Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => lookupR Ed25519Compact.ge_lookup lookupCs) lookupPub :=
  @lookup_tspec _ _ b.codeBytes Ed25519Compact.ge_lookup _ _ _ _ Ed25519Compact.ed_zero lookupCs
    (Ed25519FeAddSub.fe_sub_tspec b) (Ed25519WordLoop.cmov_tspec b) (code_at b) (lk_ok b)

end M0Crypto.Release.Ed25519Lookup
