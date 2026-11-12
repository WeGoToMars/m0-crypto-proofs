import M0Crypto.Release.Blake2sFinal
import M0Crypto.Release.Blake2sCopy
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final`: the zero-padding loops -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 add_ofNat_inj)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem lsl30 (x : Word) : ((x <<< 30) == 0#32) = decide (x.toNat % 4 = 0) := by
  have h : (x <<< 30).toNat = (x.toNat * 2 ^ 30) % 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  by_cases h4 : x.toNat % 4 = 0
  · have : x <<< 30 = 0#32 := by
      apply BitVec.eq_of_toNat_eq; rw [h]; simp; omega
    simp [this, h4]
  · have : x <<< 30 ≠ 0#32 := by
      intro hh; have := congrArg BitVec.toNat hh; rw [h] at this; simp at this; omega
    simp [this, h4]

theorem wz (m : Mem) (a x : Word) :
    write32 m a 0#32 x = if x = a ∨ x = a + 1#32 ∨ x = a + 2#32 ∨ x = a + 3#32 then 0#8 else m x := by
  by_cases h0 : x = a <;> by_cases h1 : x = a + 1#32 <;> by_cases h2 : x = a + 2#32 <;>
    by_cases h3 : x = a + 3#32 <;> simp [write32, h0, h1, h2, h3] <;> rfl

theorem wz_pass (m : Mem) (a x : Word) (h : m x = 0#8) : write32 m a 0#32 x = 0#8 := by
  rw [wz]; split <;> first | rfl | exact h

theorem wz_hit (m : Mem) (a : Word) (k : Nat) (hk : k < 4) :
    write32 m a 0#32 (a + BitVec.ofNat 32 k) = 0#8 := by
  rw [wz, if_pos]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · left; simp
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl

/-- The zeroed region `[u, k)` of the pad buffer, everything else as in `m1`. -/
def Pz (m1 : Mem) (buf : Word) (u k : Nat) (m : Mem) : Prop :=
  (∀ i, u ≤ i → i < k → m (buf + BitVec.ofNat 32 i) = 0#8) ∧
  ∀ y, (∀ i, u ≤ i → i < k → y ≠ buf + BitVec.ofNat 32 i) → m y = m1 y

theorem pz_w8 {m1 : Mem} {buf : Word} {u k : Nat} {m : Mem} (h : Pz m1 buf u k m) (hu : u ≤ k) (hk : k < 64) :
    Pz m1 buf u (k + 1) (Thumb.write8 m (buf + BitVec.ofNat 32 k) 0#32) := by
  obtain ⟨ha, hb⟩ := h
  have ne : ∀ i, i < k → buf + BitVec.ofNat 32 i ≠ buf + BitVec.ofNat 32 k := fun i hi he =>
    absurd (add_ofNat_inj buf i k (by omega) (by omega) he) (by omega)
  refine ⟨fun i hui hi => ?_, fun y hy => ?_⟩
  · by_cases hik : i = k
    · subst hik; simp [Thumb.write8]
    · rw [Thumb.write8_other _ _ _ _ (ne i (by omega))]; exact ha i hui (by omega)
  · have hyk : y ≠ buf + BitVec.ofNat 32 k := hy k (by omega) (by omega)
    rw [Thumb.write8_other _ _ _ _ hyk]
    exact hb y (fun i hui hi => hy i hui (by omega))

theorem pz_w32 {m1 : Mem} {buf : Word} {u k : Nat} {m : Mem} (h : Pz m1 buf u k m) (hu : u ≤ k) (hk : k + 4 ≤ 64) :
    Pz m1 buf u (k + 4) (write32 m (buf + BitVec.ofNat 32 k) 0#32) := by
  obtain ⟨ha, hb⟩ := h
  have inj : ∀ i j, i < 64 → j < 64 → buf + BitVec.ofNat 32 i = buf + BitVec.ofNat 32 j → i = j :=
    fun i j hi hj he => add_ofNat_inj buf i j (by omega) (by omega) he
  refine ⟨fun i hui hi => ?_, fun y hy => ?_⟩
  · by_cases hik : i < k
    · apply wz_pass; exact ha i hui hik
    · have : buf + BitVec.ofNat 32 i = (buf + BitVec.ofNat 32 k) + BitVec.ofNat 32 (i - k) := by
        rw [ofNat_add_assoc]; congr 2; omega
      rw [this]; exact wz_hit _ _ _ (by omega)
  · rw [M0Crypto.Armv6M.write32_other]
    · exact hb y (fun i hui hi => hy i hui (by omega))
    · intro j hj he
      apply hy (k + j) (by omega) (by omega)
      rw [he, ofNat_add_assoc]

theorem padBStr_at : instrAt B oPadBBody = some (.memReg .strb 0 1 6) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem padBAdd_at : instrAt B (oPadBBody + 2) = some (.addImm8 6 1) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem padWStr_at : instrAt B oPadWBody = some (.memReg .str 0 1 6) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem padWAdd_at : instrAt B (oPadWBody + 2) = some (.addImm8 6 4) := by
  rw [instrAt_eq_scan]; decide +kernel

/-- The loop invariant of the padding loops: `r6 = k`, bytes `[u,k)` of the buffer are zero. -/
def PI (R : Reg → Word) (m1 : Mem) (buf : Word) (u k : Nat) (t : State) : Prop :=
  (∀ r : Reg, r.val ≠ 6 → r.val ≠ 7 → r.val ≠ 15 → t.regs r = R r) ∧ t.regs 6 = BitVec.ofNat 32 k ∧
    u ≤ k ∧ k ≤ 64 ∧ Pz m1 buf u k t.mem ∧ R 0 = 0#32 ∧ R 1 = buf

theorem PI.setPc {R m1 buf u k t} (h : PI R m1 buf u k t) (v : Word) : PI R m1 buf u k (t.setReg 15 v) :=
  ⟨fun r h6 h7 h15 => by rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.1 r h6 h7 h15,
   by rw [sr_ne _ _ _ _ (by decide)]; exact h.2.1, h.2.2.1, h.2.2.2.1,
   by rw [show (t.setReg 15 v).mem = t.mem from rfl]; exact h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem PI.r0 {R m1 buf u k t} (h : PI R m1 buf u k t) : t.regs 0 = 0#32 := by
  rw [h.1 0 (by decide) (by decide) (by decide)]; exact h.2.2.2.2.2.1

theorem PI.r1 {R m1 buf u k t} (h : PI R m1 buf u k t) : t.regs 1 = buf := by
  rw [h.1 1 (by decide) (by decide) (by decide)]; exact h.2.2.2.2.2.2

theorem pi_tst {R m1 buf u k t} (h : PI R m1 buf u k t) :
    PI R m1 buf u k (execAll tstW t) := by
  have e1 : execAll tstW t = (Instr.lslImm 7 6 30).next t := rfl
  refine ⟨fun r h6 h7 h15 => ?_, ?_, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · rw [e1, regs_lsl _ _ _ _ _ (fun h' => h15 (by rw [h']; rfl))]
    refine (if_neg (fun h' => h7 (by rw [h']; rfl))).trans ?_
    exact h.1 r h6 h7 h15
  · rw [e1, regs_lsl _ _ _ _ _ (by decide)]
    refine (if_neg (by decide)).trans ?_
    exact h.2.1
  · rw [e1, mem_lsl]; exact h.2.2.2.2.1

theorem tst_z {R m1 buf u k t} (h : PI R m1 buf u k t) : (execAll tstW t).z = decide (k % 4 = 0) := by
  have e1 : execAll tstW t = (Instr.lslImm 7 6 30).next t := rfl
  rw [e1, z_lsl]
  have h6 : t.reg 6 = BitVec.ofNat 32 k := h.2.1
  rw [h6]
  have := lsl30 (BitVec.ofNat 32 k)
  simp only [lslC] at this ⊢
  rw [show (30 : BitVec 5).toNat = 30 from rfl]
  simp only [show (30 = 0) = False from by decide, if_false]
  have hk : k < 2 ^ 32 := by have := h.2.2.2.1; omega
  rw [this]; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem pi_bodyB {R m1 buf u k t} (h : PI R m1 buf u k t) (hbuf : buf.toNat + 64 ≤ 2 ^ 32) (hk : k < 64) :
    PI R m1 buf u (k + 1) ((Instr.addImm8 6 1).next ((Instr.memReg .strb 0 1 6).next t)) := by
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  have r6 : ((Instr.memReg .strb 0 1 6).next t).regs 6 = BitVec.ofNat 32 k := by
    rw [regs_memReg_st _ _ _ _ _ (Or.inr rfl) _ (by decide)]; exact h.2.1
  refine ⟨fun r h6 h7 h15 => ?_, ?_, by have := h.2.2.1; omega, by omega, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · rw [regs_addImm8 _ _ _ _ (n15 r h15)]
    refine (if_neg (fun h' => h6 (by rw [h']; rfl))).trans ?_
    rw [regs_memReg_st _ _ _ _ _ (Or.inr rfl) _ (n15 r h15)]; exact h.1 r h6 h7 h15
  · rw [regs_addImm8 _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_
    have : ((Instr.memReg .strb 0 1 6).next t).reg 6 = BitVec.ofNat 32 k := r6
    rw [this]; simp; bv_omega
  · rw [mem_addImm8, mem_strb]
    have e0 : t.reg 0 = 0#32 := h.r0
    have e1 : t.reg 1 + t.reg 6 = buf + BitVec.ofNat 32 k := by
      have a : t.reg 1 = buf := h.r1
      have b : t.reg 6 = BitVec.ofNat 32 k := h.2.1
      rw [a, b]
    rw [e0, e1]
    exact pz_w8 h.2.2.2.2.1 h.2.2.1 hk

section loops
variable {base : Word} {W : Word → Word → Prop} {Rd : Word → Prop} {R : Reg → Word} {m1 : Mem} {buf : Word} {u : Nat}

/-- The byte padding loop: zero single bytes until the fill level is a multiple of four. -/
theorem padB_loop (hb2 : base.toNat % 2 = 0) (hbuf : buf.toNat + 64 ≤ 2 ^ 32)
    (hW : ∀ i < 64, W (base + BitVec.ofNat 32 oPadBBody) (buf + BitVec.ofNat 32 i)) {Q : State → Prop}
    (K : ∀ (k : Nat) (t : State), t.pc = base + BitVec.ofNat 32 oPadW → PI R m1 buf u k t →
      k % 4 = 0 → ReachS base (PNR ldAll W Rd) t Q) :
    ∀ (k : Nat) (t : State), t.pc = base + BitVec.ofNat 32 oPadB → PI R m1 buf u k t → ReachS base (PNR ldAll W Rd) t Q
  | k, t, hpc, hpi => by
    refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] tstW oPadB hpc (by decide) tstW_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    have hpi' := pi_tst hpi
    have hz := tst_z hpi
    have hp : (execAll tstW t).pc = base + BitVec.ofNat 32 oPadBBeq := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachS.bcondPcNR hb2 oPadBBeq oPadW 0 (brImm8 oPadBBeq oPadW) hp (by decide +kernel) padBBeq_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      rw [cp0, hz] at hc
      exact K k _ (by rw [sr_pc]) (hpi'.setPc _) (by simpa using hc)
    · intro hc
      rw [cp0, hz] at hc
      have hk4 : ¬ k % 4 = 0 := by simpa using hc
      have hk64 : k < 64 := by have := hpi.2.2.2.1; omega
      obtain ⟨t1, ht1⟩ : ∃ x, x = (execAll tstW t).setReg 15 (base + BitVec.ofNat 32 (oPadBBeq + 2)) := ⟨_, rfl⟩
      have hq : PI R m1 buf u k t1 := by rw [ht1]; exact hpi'.setPc _
      rw [← ht1]
      have hp1 : t1.pc = base + BitVec.ofNat 32 oPadBBody := by
        rw [ht1, sr_pc, show oPadBBeq + 2 = oPadBBody by decide]
      have f1 : (Instr.memReg .strb 0 1 6).falls = true := by decide
      have f2 : (Instr.addImm8 6 1).falls = true := by decide
      have a1 : t1.reg 1 + t1.reg 6 = buf + BitVec.ofNat 32 k := by
        have a : t1.reg 1 = buf := hq.r1
        have b : t1.reg 6 = BitVec.ofNat 32 k := hq.2.1
        rw [a, b]
      refine ReachS.stepWNR hb2 oPadBBody _ hp1 (by decide) padBStr_at (by rw [B_len]; decide)
        (by simp [Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one]) (exec_ok_of_falls f1 _) ?_ ?_
      · intro y ⟨a, ha, hk, j, hj, hy⟩
        simp [Instr.accesses, MemOp.width, MemOp.isLoad] at ha
        subst ha
        simp at hj; subst hj
        simp only [] at hy
        rw [hy, a1, BitVec.add_zero]; exact hW k hk64
      · have hp2 : ((Instr.memReg .strb 0 1 6).next t1).pc = base + BitVec.ofNat 32 (oPadBBody + 2) := by
          rw [pc_next _ f1, hp1, ofNat_add_assoc]; rfl
        refine ReachS.stepWNR hb2 (oPadBBody + 2) _ hp2 (by decide) padBAdd_at (by rw [B_len]; decide)
          (by simp [Instr.accesses]) (exec_ok_of_falls f2 _) ?_ ?_
        · intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha
        · have hp3 : ((Instr.addImm8 6 1).next ((Instr.memReg .strb 0 1 6).next t1)).pc =
              base + BitVec.ofNat 32 oPadBBack := by
            rw [pc_next _ f2, hp2, ofNat_add_assoc, show oPadBBody + 2 + (Instr.addImm8 6 1).size = oPadBBack by decide]
          apply ReachS.bPcNR hb2 oPadBBack oPadB (brImm11 oPadBBack oPadB) hp3 (by decide +kernel) padBBack_at
            (by decide +kernel) (by decide +kernel)
          exact padB_loop hb2 hbuf hW K (k + 1) _ (by rw [sr_pc]) ((pi_bodyB hq hbuf hk64).setPc _)
  termination_by k => 64 - k
  decreasing_by all_goals (simp_wf; omega)


theorem pi_cmp {R m1 buf u k t} (h : PI R m1 buf u k t) : PI R m1 buf u k (execAll cmp64 t) := by
  have e1 : execAll cmp64 t = (Instr.cmpImm 6 0x40).next t := rfl
  refine ⟨fun r h6 h7 h15 => ?_, ?_, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · rw [e1, regs_cmpImm _ _ _ _ (fun h' => h15 (by rw [h']; rfl))]; exact h.1 r h6 h7 h15
  · rw [e1, regs_cmpImm _ _ _ _ (by decide)]; exact h.2.1
  · rw [e1, mem_cmpImm]; exact h.2.2.2.2.1

theorem cmp_z {R m1 buf u k t} (h : PI R m1 buf u k t) : (execAll cmp64 t).z = decide (k = 64) := by
  have e1 : execAll cmp64 t = (Instr.cmpImm 6 0x40).next t := rfl
  rw [e1, z_cmpImm]
  have h6 : t.reg 6 = BitVec.ofNat 32 k := h.2.1
  rw [h6]
  have hk := h.2.2.2.1
  by_cases h64 : k = 64
  · subst h64; decide
  · have : BitVec.ofNat 32 k ≠ (0x40 : BitVec 8).setWidth 32 := by
      intro he; have := congrArg BitVec.toNat he
      simp at this; omega
    rw [show (BitVec.ofNat 32 k == (0x40 : BitVec 8).setWidth 32) = false from beq_false_of_ne this]
    simp [h64]

theorem pi_bodyW {R m1 buf u k t} (h : PI R m1 buf u k t) (hk : k + 4 ≤ 64) :
    PI R m1 buf u (k + 4) ((Instr.addImm8 6 4).next ((Instr.memReg .str 0 1 6).next t)) := by
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  have r6 : ((Instr.memReg .str 0 1 6).next t).regs 6 = BitVec.ofNat 32 k := by
    rw [regs_memReg_st _ _ _ _ _ (Or.inl rfl) _ (by decide)]; exact h.2.1
  refine ⟨fun r h6 h7 h15 => ?_, ?_, by have := h.2.2.1; omega, by omega, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · rw [regs_addImm8 _ _ _ _ (n15 r h15)]
    refine (if_neg (fun h' => h6 (by rw [h']; rfl))).trans ?_
    rw [regs_memReg_st _ _ _ _ _ (Or.inl rfl) _ (n15 r h15)]; exact h.1 r h6 h7 h15
  · rw [regs_addImm8 _ _ _ _ (by decide)]
    refine (if_pos rfl).trans ?_
    have : ((Instr.memReg .str 0 1 6).next t).reg 6 = BitVec.ofNat 32 k := r6
    rw [this]; simp; bv_omega
  · rw [mem_addImm8, mem_strw]
    have e0 : t.reg 0 = 0#32 := h.r0
    have e1 : t.reg 1 + t.reg 6 = buf + BitVec.ofNat 32 k := by
      have a : t.reg 1 = buf := h.r1
      have b : t.reg 6 = BitVec.ofNat 32 k := h.2.1
      rw [a, b]
    rw [e0, e1]
    exact pz_w32 h.2.2.2.2.1 h.2.2.1 hk

/-- The word padding loop: zero words until the buffer is full. -/
theorem padW_loop (hb2 : base.toNat % 2 = 0) (hbuf : buf.toNat + 64 ≤ 2 ^ 32) (hbuf4 : buf.toNat % 4 = 0)
    (hW : ∀ i < 64, W (base + BitVec.ofNat 32 oPadWBody) (buf + BitVec.ofNat 32 i)) {Q : State → Prop}
    (K : ∀ (t : State), t.pc = base + BitVec.ofNat 32 oFComp → PI R m1 buf u 64 t → ReachS base (PNR ldAll W Rd) t Q) :
    ∀ (k : Nat) (t : State), t.pc = base + BitVec.ofNat 32 oPadW → PI R m1 buf u k t → k % 4 = 0 →
      ReachS base (PNR ldAll W Rd) t Q
  | k, t, hpc, hpi, hk4 => by
    refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] cmp64 oPadW hpc (by decide) cmp64_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    have hpi' := pi_cmp hpi
    have hz := cmp_z hpi
    have hp : (execAll cmp64 t).pc = base + BitVec.ofNat 32 oPadWBeq := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachS.bcondPcNR hb2 oPadWBeq oFComp 0 (brImm8 oPadWBeq oFComp) hp (by decide +kernel) padWBeq_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      rw [cp0, hz] at hc
      have : k = 64 := by simpa using hc
      subst this
      exact K _ (by rw [sr_pc]) (hpi'.setPc _)
    · intro hc
      rw [cp0, hz] at hc
      have hk64' : ¬ k = 64 := by simpa using hc
      have hk64 : k + 4 ≤ 64 := by have := hpi.2.2.2.1; omega
      obtain ⟨t1, ht1⟩ : ∃ x, x = (execAll cmp64 t).setReg 15 (base + BitVec.ofNat 32 (oPadWBeq + 2)) := ⟨_, rfl⟩
      have hq : PI R m1 buf u k t1 := by rw [ht1]; exact hpi'.setPc _
      rw [← ht1]
      have hp1 : t1.pc = base + BitVec.ofNat 32 oPadWBody := by
        rw [ht1, sr_pc, show oPadWBeq + 2 = oPadWBody by decide]
      have f1 : (Instr.memReg .str 0 1 6).falls = true := by decide
      have f2 : (Instr.addImm8 6 4).falls = true := by decide
      have a1 : t1.reg 1 + t1.reg 6 = buf + BitVec.ofNat 32 k := by
        have a : t1.reg 1 = buf := hq.r1
        have b : t1.reg 6 = BitVec.ofNat 32 k := hq.2.1
        rw [a, b]
      refine ReachS.stepWNR hb2 oPadWBody _ hp1 (by decide) padWStr_at (by rw [B_len]; decide)
        ?_ (exec_ok_of_falls f1 _) ?_ ?_
      · simp only [Instr.accesses, List.all_cons, List.all_nil, Bool.and_true, Access.aligned, MemOp.width]
        rw [a1]
        have h2 : (buf + BitVec.ofNat 32 k).toNat = buf.toNat + k := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have h3 : (buf + BitVec.ofNat 32 k).toNat % 4 = 0 := by rw [h2]; omega
        simp [h3]; omega
      · intro y ⟨a, ha, hk, j, hj, hy⟩
        simp [Instr.accesses, MemOp.width, MemOp.isLoad] at ha
        subst ha
        simp only [MemOp.width] at hj
        simp only [] at hy
        rw [hy, a1, ofNat_add_assoc]; exact hW _ (by omega)
      · have hp2 : ((Instr.memReg .str 0 1 6).next t1).pc = base + BitVec.ofNat 32 (oPadWBody + 2) := by
          rw [pc_next _ f1, hp1, ofNat_add_assoc]; rfl
        refine ReachS.stepWNR hb2 (oPadWBody + 2) _ hp2 (by decide) padWAdd_at (by rw [B_len]; decide)
          (by simp [Instr.accesses]) (exec_ok_of_falls f2 _) ?_ ?_
        · intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha
        · have hp3 : ((Instr.addImm8 6 4).next ((Instr.memReg .str 0 1 6).next t1)).pc =
              base + BitVec.ofNat 32 oPadWBack := by
            rw [pc_next _ f2, hp2, ofNat_add_assoc, show oPadWBody + 2 + (Instr.addImm8 6 4).size = oPadWBack by decide]
          apply ReachS.bPcNR hb2 oPadWBack oPadW (brImm11 oPadWBack oPadW) hp3 (by decide +kernel) padWBack_at
            (by decide +kernel) (by decide +kernel)
          exact padW_loop hb2 hbuf hbuf4 hW K (k + 4) _ (by rw [sr_pc]) ((pi_bodyW hq hk64).setPc _) (by omega)
  termination_by k => 64 - k
  decreasing_by all_goals (simp_wf; omega)

end loops
