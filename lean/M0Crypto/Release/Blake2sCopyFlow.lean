import M0Crypto.Release.Blake2sCopyPack

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_copy`: unaligned-source entry, size selection and the alignment loop -/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release (brSize_eq)

section loops
variable {base : Word} {Wr Rd : Word → Prop} {R : Reg → Word} {m0 : Mem} {d s : Word} {n : Nat}

/-- Source not word aligned, at least four bytes left: pack the words, then finish bytewise. -/
theorem unal_entry (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) {k : Nat} (t : State)
    (hpc : t.pc = base + BitVec.ofNat 32 oUnal) (hci : CI R m0 d s n k t) (h4 : 4 ≤ n - k)
    (hr4 : t.regs 4 = 3#32) (hal0 : (t.regs 0).toNat % 4 = 0) :
    ReachNR base Wr Rd t (G base R m0 d s n) := by
  refine ReachNR.symBlock hb2 [] [] [] unalS oUnal hpc (by decide) unal_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨u5, u2, u3, uz, um, ur⟩ := unalS_eff t
  have hkn := hci.kn
  have hlt : n - k < 2 ^ 32 := by omega
  have hpk : PK R m0 d s n k ((n - k) / 4) (execAll unalS t) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [ur 0 (by decide) (by decide) (by decide) (by decide), hci.r0]
    · rw [ur 1 (by decide) (by decide) (by decide) (by decide), hci.r1]
    · rw [u2, hci.r2, hr4, and3 _ hlt]
      congr 1; omega
    · rw [u5, hci.r2, shr2 _ hlt]
    · rw [um]; exact hci.cp
    · intro r h8 h15
      rw [ur r (by omega) (by omega) (by omega) h15]; exact hci.hi r h8 h15
  obtain ⟨c', hc'⟩ : ∃ c', (n - k) / 4 = c' + 1 := ⟨(n - k) / 4 - 1, by omega⟩
  rw [hc'] at hpk
  have hp : (execAll unalS t).pc = base + BitVec.ofNat 32 oUnalBeq := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  have hr0 : (execAll unalS t).regs 0 = t.regs 0 := ur 0 (by decide) (by decide) (by decide) (by decide)
  have hr1 : (execAll unalS t).regs 1 = t.regs 1 := ur 1 (by decide) (by decide) (by decide) (by decide)
  apply ReachNR.bcond hb2 oUnalBeq oPH 0 (brImm8 oUnalBeq oPH) hp (by decide +kernel) unalBeq_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    have hz : (execAll unalS t).z = true := by rw [cp0] at hc; exact hc
    have hev : (t.regs 1).toNat % 2 = 0 := (and1 _).mp (by rw [← uz]; exact hz)
    refine ph_loop hb2 hDj hn hW hR c' k _ (by rw [sr_pc]) (hpk.setPc _) ?_ ?_
    · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), hr0]; exact hal0
    · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), hr1]; exact hev
  · intro hc
    have hz : (execAll unalS t).z = false := by rw [cp0] at hc; exact hc
    have hodd : (t.regs 1).toNat % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (t.regs 1).toNat with h | h
      · have := (and1 _).mpr h
        rw [← uz, hz] at this
        exact absurd this (by decide)
      · exact h
    refine pb_loop hb2 hDj hn hW hR c' k _ (by rw [sr_pc, show oUnalBeq + 2 = oPB by decide]) (hpk.setPc _) ?_ ?_
    · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), hr0]; exact hal0
    · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), hr1]; exact hodd



/-- Destination word aligned: choose bytes, word loops or the packed loops by what remains. -/
theorem sel_entry (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) {k : Nat} (t : State)
    (hpc : t.pc = base + BitVec.ofNat 32 oSel) (hci : CI R m0 d s n k t)
    (hr4 : t.regs 4 = 3#32) (hal0 : (t.regs 0).toNat % 4 = 0) :
    ReachNR base Wr Rd t (G base R m0 d s n) := by
  refine ReachNR.symBlock hb2 [] [] [] cmp4 oSel hpc (by decide) sel_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨cc, cz, cm, cr⟩ := cmp_eff 2 4 t
  rw [← show cmp4 = [Instr.cmpImm 2 4] from rfl] at cc cz cm cr
  have hci' : CI R m0 d s n k (execAll cmp4 t) := hci.same (fun r h => cr r h) cm
  have hc : (execAll cmp4 t).c = decide (4 ≤ n - k) := by
    rw [cc, show (LowReg.toReg 2) = 2 from rfl, hci.r2, r2_nat hn]; rfl
  have hp : (execAll cmp4 t).pc = base + BitVec.ofNat 32 oSelBlo := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  apply ReachNR.bcond hb2 oSelBlo oBytes 3 (brImm8 oSelBlo oBytes) hp (by decide +kernel) selBlo_at
    (by decide +kernel) (by decide +kernel)
  · intro hcp
    exact bytes_entry hb2 hDj hn hW hR _ (by rw [sr_pc]) (hci'.setPc _)
  · intro hcp
    have h4 : 4 ≤ n - k := by
      rw [cp3, hc] at hcp; simpa using hcp
    have hci1 := hci'.setPc (base + BitVec.ofNat 32 (oSelBlo + 2))
    refine ReachNR.symBlock hb2 [] [] [] tstS oSelTst
      (by rw [sr_pc, show oSelBlo + 2 = oSelTst by decide]) (by decide) selTst_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨tz, tm, tr⟩ := tst_eff 1 4 ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))
    rw [← show tstS = [Instr.dp .tst 1 4] from rfl] at tz tm tr
    have hci2 : CI R m0 d s n k (execAll tstS ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))) :=
      hci1.same (fun r h => tr r h) tm
    have hq : ∀ (r : Reg), r.val ≠ 15 → ∀ v,
        ((execAll tstS ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))).setReg 15 v).regs r
          = t.regs r := by
      intro r h v
      have h' : r ≠ 15 := fun e => h (by rw [e]; rfl)
      rw [sr_ne _ _ _ _ h', tr r h, sr_ne _ _ _ _ h', cr r h]
    have hp2 : (execAll tstS ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))).pc =
        base + BitVec.ofNat 32 oSelBne := by
      rw [execAll_pc _ _ (by decide), sr_pc, ofNat_add_assoc, show oSelBlo + 2 = oSelTst by decide]; rfl
    have hz : (execAll tstS ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))).z
        = ((t.regs 1 &&& 3#32) == 0#32) := by
      rw [tz, show (LowReg.toReg 1) = 1 from rfl, show (LowReg.toReg 4) = 4 from rfl]
      rw [sr_ne _ _ (1 : Reg) _ (by decide), sr_ne _ _ (4 : Reg) _ (by decide), cr 1 (by decide),
        cr 4 (by decide), hr4]
    apply ReachNR.bcond hb2 oSelBne oUnal 1 (brImm8 oSelBne oUnal) hp2 (by decide +kernel) selBne_at
      (by decide +kernel) (by decide +kernel)
    · intro hcp
      exact unal_entry hb2 hDj hn hW hR _ (by rw [sr_pc]) (hci2.setPc _) h4
        (hq 4 (by decide) _ |>.trans hr4) (by rw [hq 0 (by decide) _]; exact hal0)
    · intro hcp
      have hz' : (execAll tstS ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oSelBlo + 2)))).z = true := by
        rw [cp1] at hcp; simpa using hcp
      rw [hz] at hz'
      have h1 := and3' _ hz'
      refine w16_loop hb2 hDj hn hW hR k _ (by rw [sr_pc, show oSelBne + 2 = oW16 by decide]) (hci2.setPc _) ?_ ?_
      · rw [hq 0 (by decide) _]; exact hal0
      · rw [hq 1 (by decide) _]; exact h1

/-- The destination-alignment loop: single bytes until `r0` is word aligned or `n` is done. -/
theorem align_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ k : Nat, ∀ t : State, t.pc = base + BitVec.ofNat 32 oTst → CI R m0 d s n k t → k < n →
      t.regs 4 = 3#32 → ReachNR base Wr Rd t (G base R m0 d s n)
  | k, t, hpc, hci, hk, hr4 => by
    refine ReachNR.symBlock hb2 [] [] [] tstD oTst hpc (by decide) tstD_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨tz, tm, tr⟩ := tst_eff 0 4 t
    rw [← show tstD = [Instr.dp .tst 0 4] from rfl] at tz tm tr
    have hci' : CI R m0 d s n k (execAll tstD t) := hci.same (fun r h => tr r h) tm
    have hp : (execAll tstD t).pc = base + BitVec.ofNat 32 oAlBr := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    have hz : (execAll tstD t).z = ((t.regs 0 &&& 3#32) == 0#32) := by
      rw [tz, show (LowReg.toReg 0) = 0 from rfl, show (LowReg.toReg 4) = 4 from rfl, hr4]
    apply ReachNR.bcond hb2 oAlBr oSel 0 (brImm8 oAlBr oSel) hp (by decide +kernel) alBr_at
      (by decide +kernel) (by decide +kernel)
    · intro hcp
      have hz' : (execAll tstD t).z = true := by rw [cp0] at hcp; exact hcp
      rw [hz] at hz'
      exact sel_entry hb2 hDj hn hW hR _ (by rw [sr_pc]) (hci'.setPc _)
        (by rw [sr_ne _ _ _ _ (show (4 : Reg) ≠ 15 by decide), tr 4 (by decide)]; exact hr4)
        (by rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), tr 0 (by decide)]; exact and3' _ hz')
    · intro hcp
      have hci1 := hci'.setPc (base + BitVec.ofNat 32 (oAlBr + 2))
      refine ReachNR.symBlock hb2 [((1 : Reg), 1), ((0 : Reg), 1)] [((0 : Reg), (0#32 : Word), 1)] [((1 : Reg), (0#32 : Word), 1)] byteB oAlBody
        (by rw [sr_pc, show oAlBr + 2 = oAlBody by decide]) (by decide) alBody_at (by decide) ?_ ?_
        ?_ (by decide +kernel) (by decide +kernel) ?_
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact Nat.mod_one _
      · apply Reach.region_one
        intro o ho
        rw [hci1.r0, BitVec.add_zero, ofNat_add_assoc]; exact hW _ (by omega)
      · apply rr_one
        intro o ho
        rw [hci1.r1, BitVec.add_zero, ofNat_add_assoc]; exact hR _ (by omega)
      obtain ⟨hci2, hbz⟩ := byteB_CI hci1 hk hDj hn
      obtain ⟨-, -, -, -, -, ber⟩ := byteB_eff ((execAll tstD t).setReg 15 (base + BitVec.ofNat 32 (oAlBr + 2)))
      have hp2 : (execAll byteB ((execAll tstD t).setReg 15 (base + BitVec.ofNat 32 (oAlBr + 2)))).pc =
          base + BitVec.ofNat 32 oAlDone := by
        rw [execAll_pc _ _ (by decide), sr_pc, ofNat_add_assoc, show oAlBr + 2 = oAlBody by decide]; rfl
      apply ReachNR.bcond hb2 oAlDone oDone 0 (brImm8 oAlDone oDone) hp2 (by decide +kernel) alDone_at
        (by decide +kernel) (by decide +kernel)
      · intro hc
        have hz2 : (execAll byteB ((execAll tstD t).setReg 15 (base + BitVec.ofNat 32 (oAlBr + 2)))).z = true := by
          rw [cp0] at hc; exact hc
        have heq : k + 1 = n := by rw [hbz] at hz2; simpa using hz2
        apply ReachNR.done
        refine ⟨by rw [sr_pc], ?_⟩
        have := hci2.setPc (base + BitVec.ofNat 32 oDone)
        rwa [heq] at this
      · intro hc
        have hz2 : (execAll byteB ((execAll tstD t).setReg 15 (base + BitVec.ofNat 32 (oAlBr + 2)))).z = false := by
          rw [cp0] at hc; exact hc
        have hne : k + 1 ≠ n := by rw [hbz] at hz2; simpa using hz2
        have hp3 : ((execAll byteB ((execAll tstD t).setReg 15 (base + BitVec.ofNat 32 (oAlBr + 2)))).setReg 15
            (base + BitVec.ofNat 32 (oAlDone + 2))).pc = base + BitVec.ofNat 32 oAlBack := by
          rw [sr_pc, show oAlDone + 2 = oAlBack by decide]
        apply ReachNR.b hb2 oAlBack oTst (brImm11 oAlBack oTst) hp3 (by decide +kernel) alBack_at
          (by decide +kernel) (by decide +kernel)
        refine align_loop hb2 hDj hn hW hR (k + 1) _ (by rw [sr_pc]) (hci2.setPc _ |>.setPc _) (by have := hci.kn; omega) ?_
        rw [sr_ne _ _ _ _ (show (4 : Reg) ≠ 15 by decide), sr_ne _ _ _ _ (show (4 : Reg) ≠ 15 by decide),
          ber 4 (by decide) (by decide), sr_ne _ _ _ _ (show (4 : Reg) ≠ 15 by decide), tr 4 (by decide)]
        exact hr4
  termination_by k => n - k
  decreasing_by omega

end loops

end M0Crypto.Release.Blake2sCopy
