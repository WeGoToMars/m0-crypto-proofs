import M0Crypto.Release.Blake2sCopy
import M0Crypto.Release.Blake2sCopyNR

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release (brSize_eq)

/-- Every path ends at the final `pop` with all `n` bytes copied. -/
def G (base : Word) (R : Reg → Word) (m0 : Mem) (d s : Word) (n : Nat) (u : State) : Prop :=
  u.pc = base + BitVec.ofNat 32 oDone ∧ CI R m0 d s n n u

theorem CI.same {R m0 d s n k} {t t' : State} (h : CI R m0 d s n k t)
    (hr : ∀ r : Reg, r.val ≠ 15 → t'.regs r = t.regs r) (hm : t'.mem = t.mem) : CI R m0 d s n k t' :=
  ⟨by rw [hr 0 (by decide)]; exact h.r0, by rw [hr 1 (by decide)]; exact h.r1,
   by rw [hr 2 (by decide)]; exact h.r2, by rw [hm]; exact h.cp,
   fun r h8 h15 => by rw [hr r h15]; exact h.hi r h8 h15, h.kn⟩

/-- A zero-valued count is a finished copy (`n - k < 2^32`). -/
theorem rem_zero {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 32 (n - k) == (0#32 : Word)) = decide (k = n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
    simp at this; omega
  · intro e; subst e; simp

theorem r2_nat {n k : Nat} (hn : n < 2 ^ 31) : (BitVec.ofNat 32 (n - k)).toNat = n - k := by
  simp only [BitVec.toNat_ofNat]; omega

theorem al_add (x : Word) (c : Nat) (hc : c % 4 = 0) (hx : x.toNat % 4 = 0) :
    (x + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem addr4 (x : Word) (j : Nat) : x + BitVec.ofNat 32 j + 4#32 = x + BitVec.ofNat 32 (j + 4) :=
  ofNat_add_assoc x j 4

theorem w4B_CI {R m0 d s n k t} (h : CI R m0 d s n k t) (hk : k + 4 ≤ n) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) : CI R m0 d s n (k + 4) (execAll w4B t) := by
  obtain ⟨e0, e1, e2, em, er⟩ := w4B_eff t
  refine ⟨?_, ?_, ?_, ?_, ?_, hk⟩
  · rw [e0, h.r0, addr4]
  · rw [e1, h.r1, addr4]
  · rw [e2, h.r2]; bv_omega
  · rw [em, h.r0, h.r1]
    exact cp_w32_s h.cp (fun j hj => cp_src h.cp hDj h.kn hj) hk hn
  · intro r h8 h15
    rw [er r (by omega) h15]; exact h.hi r h8 h15

theorem w16B_CI {R m0 d s n k t} (h : CI R m0 d s n k t) (hk : k + 16 ≤ n) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) : CI R m0 d s n (k + 16) (execAll w16B t) := by
  obtain ⟨e0, e1, e2, em, er⟩ := w16B_eff t
  have hs : ∀ j < n, t.mem (s + BitVec.ofNat 32 j) = m0 (s + BitVec.ofNat 32 j) :=
    fun j hj => cp_src h.cp hDj h.kn hj
  refine ⟨?_, ?_, ?_, ?_, ?_, hk⟩
  · rw [e0, h.r0, ofNat_add_assoc]
  · rw [e1, h.r1, ofNat_add_assoc]
  · rw [e2, h.r2]; bv_omega
  · rw [em, h.r0, h.r1]
    have c1 := cp_w32_s h.cp hs (show k + 4 ≤ n by omega) hn
    have c2 := cp_w32_s c1 hs (show k + 4 + 4 ≤ n by omega) hn
    have c3 := cp_w32_s c2 hs (show k + 4 + 4 + 4 ≤ n by omega) hn
    have c4 := cp_w32_s c3 hs (show k + 4 + 4 + 4 + 4 ≤ n by omega) hn
    simp only [storeWords, addr4]
    exact c4
  · intro r h8 h15
    rw [er r (by omega) h15]; exact h.hi r h8 h15

section loops
variable {base : Word} {Wr Rd : Word → Prop} {R : Reg → Word} {m0 : Mem} {d s : Word} {n : Nat}

theorem bl_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ rem k, rem + k = n → ∀ t : State, t.pc = base + BitVec.ofNat 32 oBL →
      CI R m0 d s n k t → 1 ≤ rem → ReachNR base Wr Rd t (G base R m0 d s n)
  | 0, k, h, t, hpc, hci, hr => absurd hr (by omega)
  | rem + 1, k, h, t, hpc, hci, _ => by
    have hk : k < n := by omega
    refine ReachNR.symBlock hb2 [((1 : Reg), 1), ((0 : Reg), 1)] [((0 : Reg), (0#32 : Word), 1)] [((1 : Reg), (0#32 : Word), 1)] byteB oBL hpc (by decide +kernel)
      bl_at (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact Nat.mod_one _
    · apply Reach.region_one
      intro o ho
      rw [hci.r0, BitVec.add_zero, ofNat_add_assoc]; exact hW _ (by omega)
    · apply rr_one
      intro o ho
      rw [hci.r1, BitVec.add_zero, ofNat_add_assoc]; exact hR _ (by omega)
    obtain ⟨hci', hz⟩ := byteB_CI hci hk hDj hn
    have hp : (execAll byteB t).pc = base + BitVec.ofNat 32 oBLBne := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oBLBne oBL 1 (brImm8 oBLBne oBL) hp (by decide +kernel) blBne_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      have hz' : (execAll byteB t).z = false := by
        rw [cp1] at hc; simpa using hc
      have hne : k + 1 ≠ n := by rw [hz] at hz'; simpa using hz'
      exact bl_loop hb2 hDj hn hW hR rem (k + 1) (by omega) _ (by rw [sr_pc]) (hci'.setPc _) (by omega)
    · intro hc
      have hz' : (execAll byteB t).z = true := by rw [cp1] at hc; simpa using hc
      have heq : k + 1 = n := by rw [hz] at hz'; simpa using hz'
      apply ReachNR.done
      refine ⟨by rw [sr_pc, show oBLBne + 2 = oDone by decide], ?_⟩
      have := hci'.setPc (base + BitVec.ofNat 32 (oBLBne + 2))
      rwa [heq] at this
theorem bytes_entry (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) {k : Nat} (t : State)
    (hpc : t.pc = base + BitVec.ofNat 32 oBytes) (hci : CI R m0 d s n k t) :
    ReachNR base Wr Rd t (G base R m0 d s n) := by
  refine ReachNR.symBlock hb2 [] [] [] cmp0 oBytes hpc (by decide +kernel) bytes_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨cc, cz, cm, cr⟩ := cmp_eff 2 0 t
  rw [← show cmp0 = [Instr.cmpImm 2 0] from rfl] at cc cz cm cr
  have hci' : CI R m0 d s n k (execAll cmp0 t) := hci.same (fun r h => cr r h) cm
  have hz : (execAll cmp0 t).z = decide (k = n) := by
    rw [cz, show (LowReg.toReg 2) = 2 from rfl, hci.r2]
    exact rem_zero hci.kn hn
  have hp : (execAll cmp0 t).pc = base + BitVec.ofNat 32 oBytesBeq := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  apply ReachNR.bcond hb2 oBytesBeq oDone 0 (brImm8 oBytesBeq oDone) hp (by decide +kernel) bytesBeq_at
    (by decide +kernel) (by decide +kernel)
  · intro hc
    have hz' : (execAll cmp0 t).z = true := by rw [cp0] at hc; exact hc
    have heq : k = n := by rw [hz] at hz'; simpa using hz'
    apply ReachNR.done
    refine ⟨by rw [sr_pc], ?_⟩
    have := hci'.setPc (base + BitVec.ofNat 32 oDone)
    rwa [heq] at this
  · intro hc
    have hz' : (execAll cmp0 t).z = false := by rw [cp0] at hc; exact hc
    have hne : k ≠ n := by rw [hz] at hz'; simpa using hz'
    exact bl_loop hb2 hDj hn hW hR (n - k) k (by have := hci.kn; omega) _
      (by rw [sr_pc, show oBytesBeq + 2 = oBL by decide]) (hci'.setPc _) (by have := hci.kn; omega)

theorem w4_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ k : Nat, ∀ t : State, t.pc = base + BitVec.ofNat 32 oW4 → CI R m0 d s n k t →
      (t.regs 0).toNat % 4 = 0 → (t.regs 1).toNat % 4 = 0 → ReachNR base Wr Rd t (G base R m0 d s n)
  | k, t, hpc, hci, hal0, hal1 => by
    refine ReachNR.symBlock hb2 [] [] [] cmp4 oW4 hpc (by decide +kernel) w4_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨cc, cz, cm, cr⟩ := cmp_eff 2 4 t
    rw [← show cmp4 = [Instr.cmpImm 2 4] from rfl] at cc cz cm cr
    have hci' : CI R m0 d s n k (execAll cmp4 t) := hci.same (fun r h => cr r h) cm
    have hc : (execAll cmp4 t).c = decide (4 ≤ n - k) := by
      rw [cc, show (LowReg.toReg 2) = 2 from rfl, hci.r2, r2_nat hn]; rfl
    have hp : (execAll cmp4 t).pc = base + BitVec.ofNat 32 oW4Blo := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oW4Blo oBytes 3 (brImm8 oW4Blo oBytes) hp (by decide +kernel) w4Blo_at
      (by decide +kernel) (by decide +kernel)
    · intro hcp
      exact bytes_entry hb2 hDj hn hW hR _ (by rw [sr_pc]) (hci'.setPc _)
    · intro hcp
      have h4 : 4 ≤ n - k := by
        rw [cp3, hc] at hcp; simpa using hcp
      have hk4 : k + 4 ≤ n := by omega
      refine ReachNR.symBlock hb2 [((1 : Reg), 4), ((0 : Reg), 4)] [((0 : Reg), (0#32 : Word), 4)] [((1 : Reg), (0#32 : Word), 4)] w4B oW4Body
        (by rw [sr_pc, show oW4Blo + 2 = oW4Body by decide]) (by decide +kernel) w4Body_at (by decide) ?_ ?_
        ?_ (by decide +kernel) (by decide +kernel) ?_
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · show (((execAll cmp4 t).setReg 15 _).regs 1).toNat % 4 = 0
          rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), cr 1 (by decide)]; exact hal1
        · show (((execAll cmp4 t).setReg 15 _).regs 0).toNat % 4 = 0
          rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), cr 0 (by decide)]; exact hal0
      · apply Reach.region_one
        intro o ho
        rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), hci'.r0, BitVec.add_zero, ofNat_add_assoc]
        exact hW _ (by omega)
      · apply rr_one
        intro o ho
        rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), hci'.r1, BitVec.add_zero, ofNat_add_assoc]
        exact hR _ (by omega)
      have hci2 := w4B_CI (hci'.setPc (base + BitVec.ofNat 32 (oW4Blo + 2))) hk4 hDj hn
      have hp2 : (execAll w4B ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oW4Blo + 2)))).pc =
          base + BitVec.ofNat 32 oW4Back := by
        rw [execAll_pc _ _ (by decide), sr_pc, ofNat_add_assoc, show oW4Blo + 2 = oW4Body by decide]; rfl
      obtain ⟨f0, f1, -⟩ := w4B_eff ((execAll cmp4 t).setReg 15 (base + BitVec.ofNat 32 (oW4Blo + 2)))
      apply ReachNR.b hb2 oW4Back oW4 (brImm11 oW4Back oW4) hp2 (by decide +kernel) w4Back_at
        (by decide +kernel) (by decide +kernel)
      refine w4_loop hb2 hDj hn hW hR (k + 4) _ (by rw [sr_pc]) (hci2.setPc _) ?_ ?_
      · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), f0, sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide),
          cr 0 (by decide)]
        exact al_add _ 4 rfl hal0
      · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), f1, sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide),
          cr 1 (by decide)]
        exact al_add _ 4 rfl hal1
  termination_by k => n - k
  decreasing_by omega
theorem w16_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ k : Nat, ∀ t : State, t.pc = base + BitVec.ofNat 32 oW16 → CI R m0 d s n k t →
      (t.regs 0).toNat % 4 = 0 → (t.regs 1).toNat % 4 = 0 → ReachNR base Wr Rd t (G base R m0 d s n)
  | k, t, hpc, hci, hal0, hal1 => by
    refine ReachNR.symBlock hb2 [] [] [] cmp16 oW16 hpc (by decide +kernel) w16_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    obtain ⟨cc, cz, cm, cr⟩ := cmp_eff 2 16 t
    rw [← show cmp16 = [Instr.cmpImm 2 16] from rfl] at cc cz cm cr
    have hci' : CI R m0 d s n k (execAll cmp16 t) := hci.same (fun r h => cr r h) cm
    have hc : (execAll cmp16 t).c = decide (16 ≤ n - k) := by
      rw [cc, show (LowReg.toReg 2) = 2 from rfl, hci.r2, r2_nat hn]; rfl
    have hp : (execAll cmp16 t).pc = base + BitVec.ofNat 32 oW16Blo := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oW16Blo oW4 3 (brImm8 oW16Blo oW4) hp (by decide +kernel) w16Blo_at
      (by decide +kernel) (by decide +kernel)
    · intro hcp
      exact w4_loop hb2 hDj hn hW hR k _ (by rw [sr_pc]) (hci'.setPc _) (by rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), cr 0 (by decide)]; exact hal0) (by rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), cr 1 (by decide)]; exact hal1)
    · intro hcp
      have h4 : 16 ≤ n - k := by
        rw [cp3, hc] at hcp; simpa using hcp
      have hk4 : k + 16 ≤ n := by omega
      refine ReachNR.symBlock hb2 [((1 : Reg), 4), ((0 : Reg), 4)] [((0 : Reg), (0#32 : Word), 16)] [((1 : Reg), (0#32 : Word), 16)] w16B oW16Body
        (by rw [sr_pc, show oW16Blo + 2 = oW16Body by decide]) (by decide +kernel) w16Body_at (by decide) ?_ ?_
        ?_ (by decide +kernel) (by decide +kernel) ?_
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · show (((execAll cmp16 t).setReg 15 _).regs 1).toNat % 4 = 0
          rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), cr 1 (by decide)]; exact hal1
        · show (((execAll cmp16 t).setReg 15 _).regs 0).toNat % 4 = 0
          rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), cr 0 (by decide)]; exact hal0
      · apply Reach.region_one
        intro o ho
        rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), hci'.r0, BitVec.add_zero, ofNat_add_assoc]
        exact hW _ (by omega)
      · apply rr_one
        intro o ho
        rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), hci'.r1, BitVec.add_zero, ofNat_add_assoc]
        exact hR _ (by omega)
      have hci2 := w16B_CI (hci'.setPc (base + BitVec.ofNat 32 (oW16Blo + 2))) hk4 hDj hn
      have hp2 : (execAll w16B ((execAll cmp16 t).setReg 15 (base + BitVec.ofNat 32 (oW16Blo + 2)))).pc =
          base + BitVec.ofNat 32 oW16Back := by
        rw [execAll_pc _ _ (by decide), sr_pc, ofNat_add_assoc, show oW16Blo + 2 = oW16Body by decide]; rfl
      obtain ⟨f0, f1, -⟩ := w16B_eff ((execAll cmp16 t).setReg 15 (base + BitVec.ofNat 32 (oW16Blo + 2)))
      apply ReachNR.b hb2 oW16Back oW16 (brImm11 oW16Back oW16) hp2 (by decide +kernel) w16Back_at
        (by decide +kernel) (by decide +kernel)
      refine w16_loop hb2 hDj hn hW hR (k + 16) _ (by rw [sr_pc]) (hci2.setPc _) ?_ ?_
      · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), f0, sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide),
          cr 0 (by decide)]
        exact al_add _ 16 rfl hal0
      · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), f1, sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide),
          cr 1 (by decide)]
        exact al_add _ 16 rfl hal1
  termination_by k => n - k
  decreasing_by omega
end loops

end M0Crypto.Release.Blake2sCopy
