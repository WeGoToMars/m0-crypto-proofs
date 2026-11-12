import M0Crypto.Release.Blake2sFinalCall
import M0Crypto.Release.Blake2sCopy

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final`: the output copy and the return -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2s (regs_movImm mem_movImm)
open M0Crypto.Release.Blake2sPro (regs_stm mem_stm mem_ldm)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 Cp cp_w32_s cp_src cp_zero dj_ne read32_byte read8_low cp_w8 add_ofNat_inj)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem l0F : listRegs 15#8 = [0, 1, 2, 3] := by decide
theorem b0F : bitCount 15#8 = 4 := by decide

theorem ldm_r (s : State) :
    ((Instr.ldm 4 15#8).next s).regs 0 = read32 s.mem (s.regs 4) ∧
    ((Instr.ldm 4 15#8).next s).regs 1 = read32 s.mem (s.regs 4 + 4#32) ∧
    ((Instr.ldm 4 15#8).next s).regs 2 = read32 s.mem (s.regs 4 + 8#32) ∧
    ((Instr.ldm 4 15#8).next s).regs 3 = read32 s.mem (s.regs 4 + 12#32) ∧
    ((Instr.ldm 4 15#8).next s).regs 4 = s.regs 4 + 16#32 := by
  have e4 : s.regs 4 + 4#32 = s.regs 4 + 4#32 := rfl
  have e8 : s.regs 4 + 4#32 + 4#32 = s.regs 4 + 8#32 := by bv_omega
  have e12 : s.regs 4 + 4#32 + 4#32 + 4#32 = s.regs 4 + 12#32 := by bv_omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) [Instr.next, Instr.exec, l0F, b0F, loadRegs, State.setReg, State.reg, LowReg.toReg] <;>
  (congr 1 <;> first | rfl | exact e4 | exact e8 | exact e12)

theorem rd_store_far (m : Mem) (b : Word) (vs : List Word) (x : Word)
    (h : ∀ i k, i < vs.length → k < 4 → ∀ j, j < 4 → x + BitVec.ofNat 32 j ≠ b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :
    read32 (storeWords m b vs) x = read32 m x := by
  apply read32_congr
  intro j hj
  apply storeWords_other
  intro i k hi hk heq
  exact h i k hi hk j hj heq

theorem outW_other (t : State) (r : Reg) (h6 : 6 ≤ r.val) (h15 : r.val ≠ 15) :
    (execAll outW t).regs r = t.regs r := by
  apply execAll_regs_other outW t r h15
  simp [outW, Instr.dsts, l0F]
  omega

theorem l0F0 : listRegs 0xF0#8 = [4, 5, 6, 7] := by decide
theorem b0F0 : bitCount 0xF0#8 = 4 := by decide

theorem b240 : bitCount (240 : BitVec 8) = 4 := by decide
theorem l240 : listRegs (240 : BitVec 8) = [4, 5, 6, 7] := by decide

theorem pop_eff (t : State) (hbit : (read32 t.mem (t.regs 13 + 16#32)).getLsbD 0 = true) :
    ∃ s1, uPop.exec t = .ok s1 ∧ s1.mem = t.mem ∧ s1.regs 13 = t.regs 13 + 20#32 ∧
      s1.regs 4 = read32 t.mem (t.regs 13) ∧
      s1.regs 5 = read32 t.mem (t.regs 13 + 4#32) ∧
      s1.regs 6 = read32 t.mem (t.regs 13 + 8#32) ∧
      s1.regs 7 = read32 t.mem (t.regs 13 + 12#32) ∧
      (∀ r : Reg, r.val < 4 ∨ 8 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → s1.regs r = t.regs r) ∧
      s1.pc = read32 t.mem (t.regs 13 + 16#32) &&& ~~~1#32 := by
  have h1 : (read32 t.mem (t.sp + BitVec.ofNat 32 (4 * 4))).getLsbD 0 = true := by
    simpa [State.sp] using hbit
  unfold uPop
  simp (config := {decide := true}) only [Instr.exec, ite_true, h1, b240]
  refine ⟨_, rfl, ?_⟩
  simp (config := {decide := true}) [l240, b240, l0F0, b0F0, loadRegs, State.setReg, State.sp, State.pc, Fin.ext_iff]
  have e8 : t.regs 13 + 4#32 + 4#32 = t.regs 13 + 8#32 := by bv_omega
  have e12 : t.regs 13 + 8#32 + 4#32 = t.regs 13 + 12#32 := by bv_omega
  rw [e8, e12]
  refine ⟨rfl, rfl, ?_⟩
  intro r h8 h13 h15
  have a15 : ((15 : Reg) : Nat) = 15 := rfl
  have a13 : ((13 : Reg) : Nat) = 13 := rfl
  have a7 : ((LowReg.toReg 7 : Reg) : Nat) = 7 := rfl
  have a6 : ((LowReg.toReg 6 : Reg) : Nat) = 6 := rfl
  have a5 : ((LowReg.toReg 5 : Reg) : Nat) = 5 := rfl
  have a4 : ((LowReg.toReg 4 : Reg) : Nat) = 4 := rfl
  simp only [a15, a13, a7, a6, a5, a4, h15, h13, if_false]
  have : ¬ (r.val = 7) := by omega
  have : ¬ (r.val = 6) := by omega
  have : ¬ (r.val = 5) := by omega
  have : ¬ (r.val = 4) := by omega
  simp [*]

theorem cp_store4 {m0 m ms : Mem} {d s : Word} {n k : Nat} (hc : Cp m0 m d s k)
    (hs : ∀ j < n, ms (s + BitVec.ofNat 32 j) = m0 (s + BitVec.ofNat 32 j)) (hk : k + 16 ≤ n)
    (hn : n < 2 ^ 31) (v0 v1 v2 v3 : Word)
    (h0 : v0 = read32 ms (s + BitVec.ofNat 32 k)) (h1 : v1 = read32 ms (s + BitVec.ofNat 32 (k + 4)))
    (h2 : v2 = read32 ms (s + BitVec.ofNat 32 (k + 8))) (h3 : v3 = read32 ms (s + BitVec.ofNat 32 (k + 12))) :
    Cp m0 (storeWords m (d + BitVec.ofNat 32 k) [v0, v1, v2, v3]) d s (k + 16) := by
  subst h0 h1 h2 h3
  have c1 := cp_w32_s hc hs (by omega : k + 4 ≤ n) hn
  have c2 := cp_w32_s c1 hs (by omega : k + 4 + 4 ≤ n) hn
  have c3 := cp_w32_s c2 hs (by omega : k + 4 + 4 + 4 ≤ n) hn
  have c4 := cp_w32_s c3 hs (by omega : k + 4 + 4 + 4 + 4 ≤ n) hn
  have e1 : d + BitVec.ofNat 32 k + 4#32 = d + BitVec.ofNat 32 (k + 4) := by bv_omega
  have e2 : d + BitVec.ofNat 32 (k + 4) + 4#32 = d + BitVec.ofNat 32 (k + 8) := by bv_omega
  have e3 : d + BitVec.ofNat 32 (k + 8) + 4#32 = d + BitVec.ofNat 32 (k + 12) := by bv_omega
  simp only [storeWords, e1, e2, e3]
  have g2 : k + 4 + 4 = k + 8 := by omega
  have g3 : k + 4 + 4 + 4 = k + 12 := by omega
  have g4 : k + 4 + 4 + 4 + 4 = k + 16 := by omega
  rw [g2] at c2 c3 c4
  rw [g3] at c3 c4
  rw [g4] at c4
  exact c4

theorem ldm_other (s : State) (r : Reg) (h15 : r.val ≠ 15) (h5 : 5 ≤ r.val) :
    ((Instr.ldm 4 15#8).next s).regs r = s.regs r := by
  have := execAll_regs_other [Instr.ldm 4 15#8] s r h15 (by simp [Instr.dsts, l0F]; omega)
  exact this

theorem stm_regs (s : State) (r : Reg) (h15 : r.val ≠ 15) (h5 : r.val ≠ 5) :
    ((Instr.stm 5 15#8).next s).regs r = s.regs r := by
  rw [regs_stm s 5 15#8 r (by intro h; rw [h] at h15; exact h15 rfl)]
  have : r ≠ LowReg.toReg 5 := by
    intro h; apply h5; rw [h]; rfl
  simp [this]

theorem stm_r5 (s : State) :
    ((Instr.stm 5 15#8).next s).regs 5 = s.regs 5 + 16#32 := by
  rw [regs_stm s 5 15#8 5 (by decide)]
  simp [State.reg, b0F, LowReg.toReg]
  rfl

theorem outW_eff (t : State) (hDj : Disj (t.regs 5) 32 (t.regs 4) 32) :
    (execAll outW t).regs 4 = t.regs 4 + 32#32 ∧ (execAll outW t).regs 5 = t.regs 5 + 32#32 ∧
    Cp t.mem (execAll outW t).mem (t.regs 5) (t.regs 4) 32 := by
  have hx : execAll outW t = (Instr.stm 5 15#8).next ((Instr.ldm 4 15#8).next
      ((Instr.stm 5 15#8).next ((Instr.ldm 4 15#8).next t))) := rfl
  obtain ⟨t1, ht1⟩ : ∃ x, x = (Instr.ldm 4 15#8).next t := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ x, x = (Instr.stm 5 15#8).next t1 := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ x, x = (Instr.ldm 4 15#8).next t2 := ⟨_, rfl⟩
  rw [hx, ← ht1, ← ht2, ← ht3]
  have l1 := ldm_r t
  rw [← ht1] at l1
  obtain ⟨a0, a1, a2, a3, a4⟩ := l1
  have a5 : t1.regs 5 = t.regs 5 := by rw [ht1]; exact ldm_other t 5 (by decide) (by decide)
  have am : t1.mem = t.mem := by rw [ht1]; exact mem_ldm t 4 15#8
  have bm := mem_stm t1 5 15#8
  rw [← ht2] at bm
  have b4 : t2.regs 4 = t.regs 4 + 16#32 := by
    rw [ht2, stm_regs _ 4 (by decide) (by decide), a4]
  have b5 : t2.regs 5 = t.regs 5 + 16#32 := by
    have := stm_r5 t1
    rw [← ht2, a5] at this; exact this
  have bm' : t2.mem = storeWords t.mem (t.regs 5) [read32 t.mem (t.regs 4), read32 t.mem (t.regs 4 + 4#32),
      read32 t.mem (t.regs 4 + 8#32), read32 t.mem (t.regs 4 + 12#32)] := by
    rw [bm, am, l0F]
    show storeWords t.mem (t1.regs 5) [t1.regs 0, t1.regs 1, t1.regs 2, t1.regs 3] = _
    rw [a0, a1, a2, a3, a5]
  obtain ⟨g1, g2, g3⟩ := hDj
  have hn : (32 : Nat) < 2 ^ 31 := by omega
  have cp1' : Cp t.mem t2.mem (t.regs 5) (t.regs 4) 16 := by
    have := cp_store4 (cp_zero t.mem (t.regs 5) (t.regs 4)) (n := 32) (k := 0) (ms := t.mem)
      (fun _ _ => rfl) (by omega) hn (read32 t.mem (t.regs 4)) (read32 t.mem (t.regs 4 + 4#32))
      (read32 t.mem (t.regs 4 + 8#32)) (read32 t.mem (t.regs 4 + 12#32))
      (by congr 1; bv_omega) (by congr 1) (by congr 1) (by congr 1)
    rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] at this
    rw [bm']; exact this
  have l3 := ldm_r t2
  rw [← ht3] at l3
  obtain ⟨c0, c1, c2, c3, c4⟩ := l3
  have c5 : t3.regs 5 = t2.regs 5 := by rw [ht3]; exact ldm_other t2 5 (by decide) (by decide)
  have cm : t3.mem = t2.mem := by rw [ht3]; exact mem_ldm t2 4 15#8
  have c4' : t3.regs 4 = t.regs 4 + 32#32 := by rw [c4, b4]; bv_omega
  have dm := mem_stm t3 5 15#8
  have hs2 : ∀ j < 32, t2.mem (t.regs 4 + BitVec.ofNat 32 j) = t.mem (t.regs 4 + BitVec.ofNat 32 j) := by
    intro j hj
    exact cp_src cp1' ⟨g1, g2, by omega⟩ (by omega) hj
  refine ⟨?_, ?_, ?_⟩
  · rw [stm_regs _ 4 (by decide) (by decide), c4']
  · rw [stm_r5, c5, b5]; bv_omega
  · rw [dm, cm, l0F]
    show Cp t.mem (storeWords t2.mem (t3.regs 5) [t3.regs 0, t3.regs 1, t3.regs 2, t3.regs 3]) _ _ 32
    have := cp_store4 cp1' (n := 32) (k := 16) (ms := t2.mem) hs2 (by omega) hn (t3.regs 0) (t3.regs 1)
      (t3.regs 2) (t3.regs 3)
      (by rw [c0, b4]; try (congr 1; try bv_omega)) (by rw [c1, b4]; try (congr 1; try bv_omega))
      (by rw [c2, b4]; try (congr 1; try bv_omega)) (by rw [c3, b4]; try (congr 1; try bv_omega))
    rw [c5, b5, show t.regs 5 + 16#32 = t.regs 5 + BitVec.ofNat 32 16 from rfl]
    exact this

/-! ## The byte output loop -/

structure OI (R : Reg → Word) (m0 : Mem) (c o : Word) (k : Nat) (t : State) : Prop where
  r4 : t.regs 4 = c
  r5 : t.regs 5 = o
  r6 : t.regs 6 = BitVec.ofNat 32 k
  cp : Cp m0 t.mem o c k
  hi : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t.regs r = R r
  kn : k ≤ 32

theorem OI.setPc {R m0 c o k t} (h : OI R m0 c o k t) (v : Word) : OI R m0 c o k (t.setReg 15 v) :=
  ⟨by rw [sr_ne _ _ _ _ (by decide)]; exact h.r4, by rw [sr_ne _ _ _ _ (by decide)]; exact h.r5,
   by rw [sr_ne _ _ _ _ (by decide)]; exact h.r6, h.cp,
   fun r h7 h15 => by rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.hi r h7 h15, h.kn⟩

theorem ob_body {R m0 c o k t} (h : OI R m0 c o k t) (hD : Disj o 32 c 32) (hk : k < 32) :
    OI R m0 c o (k + 1) ((Instr.addImm8 6 1).next ((Instr.memReg .strb 0 5 6).next
      ((Instr.memReg .ldrb 0 4 6).next t))) := by
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  obtain ⟨t1, ht1⟩ : ∃ x, x = (Instr.memReg .ldrb 0 4 6).next t := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ x, x = (Instr.memReg .strb 0 5 6).next t1 := ⟨_, rfl⟩
  rw [← ht1, ← ht2]
  have s1r : ∀ r : Reg, r.val ≠ 15 → r ≠ 0 → t1.regs r = t.regs r := by
    intro r h15 h0
    rw [ht1, regs_ldrb _ _ _ _ _ (n15 r h15)]
    have : r ≠ LowReg.toReg 0 := h0
    simp [this]
  have s1r0 : t1.regs 0 = read8 t.mem (c + BitVec.ofNat 32 k) := by
    rw [ht1, regs_ldrb _ _ _ _ _ (by decide)]
    show read8 t.mem (t.regs 4 + t.regs 6) = _
    rw [h.r4, h.r6]
  have s1m : t1.mem = t.mem := by rw [ht1]; exact mem_ldrb _ _ _ _
  have s2r : ∀ r : Reg, r.val ≠ 15 → t2.regs r = t1.regs r := fun r h15 => by
    rw [ht2]; exact regs_memReg_st _ _ _ _ _ (Or.inr rfl) _ (n15 r h15)
  have s2m : t2.mem = write8 t.mem (o + BitVec.ofNat 32 k) (read8 t.mem (c + BitVec.ofNat 32 k)) := by
    rw [ht2, mem_strb, s1m]
    have e5 : t1.reg 5 = o := by
      show t1.regs 5 = o
      rw [s1r 5 (by decide) (by decide), h.r5]
    have e6 : t1.reg 6 = BitVec.ofNat 32 k := by
      show t1.regs 6 = _
      rw [s1r 6 (by decide) (by decide), h.r6]
    show write8 t.mem (t1.regs 5 + t1.regs 6) (t1.regs 0) = _
    rw [s1r0]
    have := e5; have := e6
    show write8 t.mem (t1.reg 5 + t1.reg 6) _ = _
    rw [e5, e6]
  have hsrc : t.mem (c + BitVec.ofNat 32 k) = m0 (c + BitVec.ofNat 32 k) :=
    cp_src h.cp hD h.kn hk
  have ar6 : ((Instr.addImm8 6 1).next t2).regs 6 = t2.regs 6 + 1#32 := by
    rw [regs_addImm8 _ _ _ _ (by decide)]
    have e6 : (6 : Reg) = LowReg.toReg 6 := rfl
    rw [if_pos e6]
    rfl
  have arn : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 6 → ((Instr.addImm8 6 1).next t2).regs r = t2.regs r := by
    intro r h15 h6
    rw [regs_addImm8 _ _ _ _ (n15 r h15)]
    have : r ≠ LowReg.toReg 6 := fun e => h6 (by rw [e]; rfl)
    simp [this]
  refine ⟨?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [arn 4 (by decide) (by decide), s2r 4 (by decide), s1r 4 (by decide) (by decide), h.r4]
  · rw [arn 5 (by decide) (by decide), s2r 5 (by decide), s1r 5 (by decide) (by decide), h.r5]
  · rw [ar6, s2r 6 (by decide), s1r 6 (by decide) (by decide), h.r6]
    bv_omega
  · rw [mem_addImm8, s2m]
    apply cp_w8 (by omega) h.cp
    rw [read8_low, hsrc]
  · intro r h7 h15
    rw [arn r h15 (by omega), s2r r h15, s1r r h15 (by intro e; rw [e] at h7; exact absurd h7 (by decide))]
    exact h.hi r h7 h15

theorem ob_z {R m0 c o k t} (h : OI R m0 c o k t) :
    ((Instr.cmpImm 6 0x20).next t).z = decide (k = 32) := by
  rw [z_cmpImm]
  show (t.regs 6 == _) = _
  rw [h.r6]
  have hk := h.kn
  by_cases h32 : k = 32
  · subst h32; decide
  · have : BitVec.ofNat 32 k ≠ (0x20 : BitVec 8).setWidth 32 := by
      intro he; have := congrArg BitVec.toNat he
      simp at this; omega
    rw [show (BitVec.ofNat 32 k == (0x20 : BitVec 8).setWidth 32) = false from beq_false_of_ne this]
    simp [h32]

theorem OI.cmp {R m0 c o k t} (h : OI R m0 c o k t) : OI R m0 c o k ((Instr.cmpImm 6 0x20).next t) := by
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  exact ⟨by rw [regs_cmpImm _ _ _ _ (by decide)]; exact h.r4, by rw [regs_cmpImm _ _ _ _ (by decide)]; exact h.r5,
    by rw [regs_cmpImm _ _ _ _ (by decide)]; exact h.r6, by rw [mem_cmpImm]; exact h.cp,
    fun r h7 h15 => by rw [regs_cmpImm _ _ _ _ (n15 r h15)]; exact h.hi r h7 h15, h.kn⟩

theorem outBLd_at : instrAt B oOutB = some (.memReg .ldrb 0 4 6) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem outBSt_at : instrAt B (oOutB + 2) = some (.memReg .strb 0 5 6) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem outBAC_at : seqAt B (oOutB + 4) [Instr.addImm8 6 1, Instr.cmpImm 6 0x20] = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem ld_keep (t : State) (r : Reg) (h15 : r.val ≠ 15) (h0 : r ≠ 0) :
    ((Instr.memReg .ldrb 0 4 6).next t).regs r = t.regs r := by
  have n15 : r ≠ 15 := fun h' => h15 (by rw [h']; rfl)
  rw [regs_ldrb _ _ _ _ _ n15]
  have : r ≠ LowReg.toReg 0 := h0
  simp [this]

section loops
variable {base : Word} {W : Word → Word → Prop} {Rd : Word → Prop} {R : Reg → Word} {m0 : Mem} {c o : Word}

theorem outB_loop (hb2 : base.toNat % 2 = 0) (hD : Disj o 32 c 32)
    (hW : ∀ i < 32, W (base + BitVec.ofNat 32 (oOutB + 2)) (o + BitVec.ofNat 32 i))
    (hR : ∀ i < 32, Rd (c + BitVec.ofNat 32 i)) {Q : State → Prop}
    (K : ∀ t : State, t.pc = base + BitVec.ofNat 32 oFRet → OI R m0 c o 32 t → ReachS base (PNR ldAll W Rd) t Q) :
    ∀ (k : Nat) (t : State), t.pc = base + BitVec.ofNat 32 oOutB → OI R m0 c o k t → k < 32 →
      ReachS base (PNR ldAll W Rd) t Q
  | k, t, hpc, hq, hk => by
    have f1 : (Instr.memReg .ldrb 0 4 6).falls = true := by decide
    have f2 : (Instr.memReg .strb 0 5 6).falls = true := by decide
    have hp2 : ((Instr.memReg .ldrb 0 4 6).next t).pc = base + BitVec.ofNat 32 (oOutB + 2) := by
      rw [pc_next _ f1, hpc, ofNat_add_assoc]; rfl
    have a5 : ((Instr.memReg .ldrb 0 4 6).next t).regs 5 = o := by
      rw [ld_keep _ 5 (by decide) (by decide), hq.r5]
    have a6 : ((Instr.memReg .ldrb 0 4 6).next t).regs 6 = BitVec.ofNat 32 k := by
      rw [ld_keep _ 6 (by decide) (by decide), hq.r6]
    refine ReachS.stepRNR hb2 oOutB _ hpc (by decide) outBLd_at (by rw [B_len]; decide)
      (by simp [Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one]) (exec_ok_of_falls f1 _) ?_ ?_ ?_
    · intro y ⟨a, ha, hk', j, hj, hy⟩
      simp [Instr.accesses, MemOp.width, MemOp.isLoad] at ha
      subst ha
      simp at hk'
    · intro y ⟨a, ha, hk', j, hj, hy⟩
      simp [Instr.accesses, MemOp.width, MemOp.isLoad] at ha
      subst ha
      simp at hj; subst hj
      simp only [] at hy
      have e : t.reg 4 + t.reg 6 = c + BitVec.ofNat 32 k := by
        show t.regs 4 + t.regs 6 = _
        rw [hq.r4, hq.r6]
      rw [hy, e, BitVec.add_zero]; exact hR k hk
    · refine ReachS.stepWNR hb2 (oOutB + 2) _ hp2 (by decide) outBSt_at (by rw [B_len]; decide)
        (by simp [Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one]) (exec_ok_of_falls f2 _) ?_ ?_
      · intro y ⟨a, ha, hk', j, hj, hy⟩
        simp [Instr.accesses, MemOp.width, MemOp.isLoad] at ha
        subst ha
        simp at hj; subst hj
        simp only [] at hy
        have e : ((Instr.memReg .ldrb 0 4 6).next t).reg 5 + ((Instr.memReg .ldrb 0 4 6).next t).reg 6 =
            o + BitVec.ofNat 32 k := by
          show _ + _ = _
          show ((Instr.memReg .ldrb 0 4 6).next t).regs 5 + ((Instr.memReg .ldrb 0 4 6).next t).regs 6 = _
          rw [a5, a6]
        rw [hy, e, BitVec.add_zero]; exact hW k hk
      · have hp3 : ((Instr.memReg .strb 0 5 6).next ((Instr.memReg .ldrb 0 4 6).next t)).pc =
            base + BitVec.ofNat 32 (oOutB + 4) := by
          rw [pc_next _ f2, hp2, ofNat_add_assoc]; rfl
        refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] [Instr.addImm8 6 1, Instr.cmpImm 6 0x20] (oOutB + 4) hp3 (by decide)
          outBAC_at (by decide) (by simp) (by simp) (by simp) (by decide +kernel) (by decide +kernel) ?_
        have hb := ob_body hq hD hk
        have hpA : (execAll [Instr.addImm8 6 1, Instr.cmpImm 6 0x20]
            ((Instr.memReg .strb 0 5 6).next ((Instr.memReg .ldrb 0 4 6).next t))).pc =
            base + BitVec.ofNat 32 oOutBBne := by
          rw [execAll_pc _ _ (by decide), hp3, ofNat_add_assoc]; rfl
        have hz := ob_z hb
        have hcm := hb.cmp
        apply ReachS.bcondPcNR hb2 oOutBBne oOutB 1 (brImm8 oOutBBne oOutB) hpA (by decide +kernel) outBBne_at
          (by decide +kernel) (by decide +kernel)
        · intro hc
          rw [cp1] at hc
          have hnz : k + 1 ≠ 32 := by
            intro e
            have : (execAll [Instr.addImm8 6 1, Instr.cmpImm 6 0x20]
              ((Instr.memReg .strb 0 5 6).next ((Instr.memReg .ldrb 0 4 6).next t))).z = true := by
              show ((Instr.cmpImm 6 0x20).next _).z = true
              rw [hz]; simp [e]
            rw [this] at hc; simp at hc
          have hkn := hcm.kn
          exact outB_loop hb2 hD hW hR K (k + 1) _ (by rw [sr_pc]) (hcm.setPc _) (by omega)
        · intro hc
          rw [cp1] at hc
          have hk32 : k + 1 = 32 := by
            refine Decidable.byContradiction fun hne => ?_
            have : (execAll [Instr.addImm8 6 1, Instr.cmpImm 6 0x20]
              ((Instr.memReg .strb 0 5 6).next ((Instr.memReg .ldrb 0 4 6).next t))).z = false := by
              show ((Instr.cmpImm 6 0x20).next _).z = false
              rw [hz]; simp [hne]
            rw [this] at hc; simp at hc
          rw [hk32] at hcm
          exact K _ (by rw [sr_pc]; rw [show oOutBBne + 2 = oFRet by decide]) (hcm.setPc _)
  termination_by k => 32 - k
  decreasing_by all_goals (simp_wf; omega)

end loops

theorem tstO_z (u : State) : (execAll tstO u).z = decide ((u.regs 5).toNat % 4 = 0) := by
  have e1 : execAll tstO u = (Instr.lslImm 0 5 30).next u := rfl
  rw [e1, z_lsl]
  have h5 : u.reg 5 = u.regs 5 := rfl
  rw [h5]
  have := lsl30 (u.regs 5)
  simp only [lslC] at this ⊢
  rw [show (30 : BitVec 5).toNat = 30 from rfl]
  simp only [show (30 = 0) = False from by decide, if_false]
  rw [this]

theorem tstO_keep (u : State) (r : Reg) (h15 : r.val ≠ 15) (h0 : r.val ≠ 0) :
    (execAll tstO u).regs r = u.regs r := by
  apply execAll_regs_other tstO u r h15
  simp [tstO, Instr.dsts]
  omega

theorem tstO_mem (u : State) : (execAll tstO u).mem = u.mem := execAll_mem _ _ (by decide)

structure KP (u t : State) : Prop where
  regs : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → t.regs r = u.regs r
  mem : t.mem = u.mem

theorem KP.setPc {u t} (h : KP u t) (v : Word) : KP u (t.setReg 15 v) :=
  ⟨fun r h15 h0 => by
    rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.regs r h15 h0, h.mem⟩

theorem KP.tst (u : State) : KP u (execAll tstO u) :=
  ⟨fun r h15 h0 => tstO_keep u r h15 h0, tstO_mem u⟩

/-- What the output stage leaves: at the return code, `r7` and above unchanged, the 32 digest bytes copied. -/
structure OutPost (base : Word) (u v : State) : Prop where
  pc : v.pc = base + BitVec.ofNat 32 oFRet
  hi : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → v.regs r = u.regs r
  cp : Cp u.mem v.mem (u.regs 5) (u.regs 4) 32

theorem out_reach {base : Word} {W : Word → Word → Prop} {Rd : Word → Prop} (hb2 : base.toNat % 2 = 0) {u : State}
    (hD : Disj (u.regs 5) 32 (u.regs 4) 32) (hc4 : (u.regs 4).toNat % 4 = 0)
    (hWw : ∀ j < seqSize outW, ∀ i < 32, W (base + BitVec.ofNat 32 (oOutW + j)) (u.regs 5 + BitVec.ofNat 32 i))
    (hW : ∀ i < 32, W (base + BitVec.ofNat 32 (oOutB + 2)) (u.regs 5 + BitVec.ofNat 32 i))
    (hR : ∀ i < 32, Rd (u.regs 4 + BitVec.ofNat 32 i))
    (hpc : u.pc = base + BitVec.ofNat 32 oTstO) : ReachS base (PNR ldAll W Rd) u (OutPost base u) := by
  refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] tstO oTstO hpc (by decide) tstO_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  have hp : (execAll tstO u).pc = base + BitVec.ofNat 32 oTstOBne := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  have kp := KP.tst u
  have hz := tstO_z u
  apply ReachS.bcondPcNR hb2 oTstOBne oOutB0 1 (brImm8 oTstOBne oOutB0) hp (by decide +kernel) tstOBne_at
    (by decide +kernel) (by decide +kernel)
  · -- unaligned output: byte loop
    intro hc
    rw [cp1, hz] at hc
    obtain ⟨T1, hT1⟩ : ∃ x, x = (execAll tstO u).setReg 15 (base + BitVec.ofNat 32 oOutB0) := ⟨_, rfl⟩
    rw [← hT1]
    have kp1 : KP u T1 := by rw [hT1]; exact kp.setPc _
    have hp1 : T1.pc = base + BitVec.ofNat 32 oOutB0 := by rw [hT1, sr_pc]
    refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] outB0 oOutB0 hp1 (by decide) outB0_at (by decide) (by simp) (by simp)
      (by simp) (by decide +kernel) (by decide +kernel) ?_
    have hw : execAll outB0 T1 = (Instr.movImm 6 0).next T1 := rfl
    have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
    have hpw : (execAll outB0 T1).pc = base + BitVec.ofNat 32 oOutB := by
      rw [execAll_pc _ _ (by decide), hp1, ofNat_add_assoc]; rfl
    have hoi : OI u.regs u.mem (u.regs 4) (u.regs 5) 0 (execAll outB0 T1) := by
      have keep : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 6 → r.val ≠ 0 → (execAll outB0 T1).regs r = u.regs r := by
        intro r h15 h6 h0
        rw [hw, regs_movImm _ _ _ _ (n15 r h15)]
        have : r ≠ LowReg.toReg 6 := fun e => h6 (by rw [e]; rfl)
        rw [if_neg this]
        exact kp1.regs r h15 h0
      refine ⟨keep 4 (by decide) (by decide) (by decide), keep 5 (by decide) (by decide) (by decide), ?_, ?_, ?_, by omega⟩
      · rw [hw, regs_movImm _ _ _ _ (by decide)]
        have e6 : (6 : Reg) = LowReg.toReg 6 := rfl
        rw [if_pos e6]; rfl
      · rw [hw, mem_movImm, kp1.mem]; exact cp_zero _ _ _
      · intro r h7 h15
        exact keep r h15 (by omega) (by omega)
    refine outB_loop hb2 hD hW hR ?_ 0 _ hpw hoi (by omega)
    intro t hpt hot
    exact ReachS.done ⟨hpt, fun r h7 h15 => hot.hi r h7 h15, hot.cp⟩
  · intro hc
    rw [cp1, hz] at hc
    have ha : (u.regs 5).toNat % 4 = 0 := by simpa using hc
    obtain ⟨T2, hT2⟩ : ∃ x, x = (execAll tstO u).setReg 15 (base + BitVec.ofNat 32 (oTstOBne + 2)) := ⟨_, rfl⟩
    rw [← hT2]
    have kp2 : KP u T2 := by rw [hT2]; exact kp.setPc _
    have hp2 : T2.pc = base + BitVec.ofNat 32 oOutW := by
      rw [hT2, sr_pc, show oTstOBne + 2 = oOutW by decide]
    have r4 : T2.regs 4 = u.regs 4 := kp2.regs 4 (by decide) (by decide)
    have r5 : T2.regs 5 = u.regs 5 := kp2.regs 5 (by decide) (by decide)
    refine ReachS.symBlockWNR (Ld := ldAll) hb2 [((4 : Reg), 4), ((5 : Reg), 4)] [((5 : Reg), 0#32, 32)] [((4 : Reg), (0#32 : Word), 32)] outW oOutW hp2
      (by decide) outW_at (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [r4]; exact hc4
      · simp only [r5]; exact ha
    · intro p hp o' ho' j hj
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      subst hp
      simp only [] at ho'
      simp only [r5, BitVec.add_zero]
      exact hWw j hj o' ho'
    · apply rr_one
      intro o' ho'
      simp only [r4, BitVec.add_zero]
      exact hR o' ho'
    · have hD2 : Disj (T2.regs 5) 32 (T2.regs 4) 32 := by rw [r4, r5]; exact hD
      obtain ⟨e4, e5, ecp⟩ := outW_eff T2 hD2
      have hpV : (execAll outW T2).pc = base + BitVec.ofNat 32 oOutWB := by
        rw [execAll_pc _ _ (by decide), hp2, ofNat_add_assoc]; rfl
      apply ReachS.bPcNR hb2 oOutWB oFRet (brImm11 oOutWB oFRet) hpV (by decide +kernel) outWB_at
        (by decide +kernel) (by decide +kernel)
      refine ReachS.done ⟨by rw [sr_pc], fun r h7 h15 => ?_, ?_⟩
      · rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl), outW_other T2 r (by omega) h15]
        exact kp2.regs r h15 (by omega)
      · show Cp u.mem (execAll outW T2).mem (u.regs 5) (u.regs 4) 32
        rw [← r4, ← r5, ← kp2.mem]
        exact ecp

theorem addSp_eff (s : State) :
    ((Instr.addSp 1).next s).regs 13 = s.regs 13 + 4#32 ∧
    (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → ((Instr.addSp 1).next s).regs r = s.regs r) ∧
    ((Instr.addSp 1).next s).mem = s.mem := by
  refine ⟨?_, fun r h13 h15 => ?_, ?_⟩
  · simp [Instr.next, Instr.exec, State.setReg, State.sp]
  · have := execAll_regs_other [Instr.addSp 1] s r h15 (by simp [Instr.dsts]; omega)
    exact this
  · simp [Instr.next, Instr.exec, State.setReg]

/-- `movs r0..r3, #0`: the scratch registers become zero, nothing else changes. -/
theorem zero_eff (s : State) :
    (execAll zeroScratch s).mem = s.mem ∧
    (∀ r : Reg, r.val < 4 → (execAll zeroScratch s).regs r = 0#32) ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → (execAll zeroScratch s).regs r = s.regs r) := by
  have a := Blake2sTail.RA_movImm (Blake2sTail.RA_movImm (Blake2sTail.RA_movImm (Blake2sTail.RA_movImm
    (fun _ _ => rfl : Blake2sPro.RA s s.regs) 0 0) 1 0) 2 0) 3 0
  change Blake2sPro.RA (execAll zeroScratch s) _ at a
  refine ⟨execAll_mem _ s (by decide), fun r h4 => ?_, fun r h4 h15 => ?_⟩
  · have hr : ∀ r : Reg, r.val < 4 → r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by decide
    rcases hr r h4 with rfl | rfl | rfl | rfl <;> rw [a _ (by decide)] <;> rfl
  · rw [a r (fun h => h15 (by rw [h]; rfl))]
    have n : ∀ d : Reg, d.val < 4 → ¬ r = d := fun d hd e => by rw [e] at h4; omega
    show (if r = 3 then _ else if r = 2 then _ else if r = 1 then _ else if r = 0 then _ else _) = _
    rw [if_neg (n 3 (by decide)), if_neg (n 2 (by decide)), if_neg (n 1 (by decide)),
      if_neg (n 0 (by decide))]

/-- The epilogue: `movs r0..r3, #0; add sp, #4; pop {r4-r7, pc}`. -/
structure RetPost (base : Word) (v w : State) : Prop where
  pc : w.pc = read32 v.mem (v.regs 13 + 4#32 + 16#32) &&& ~~~1#32
  sp : w.regs 13 = v.regs 13 + 24#32
  r4 : w.regs 4 = read32 v.mem (v.regs 13 + 4#32)
  r5 : w.regs 5 = read32 v.mem (v.regs 13 + 4#32 + 4#32)
  r6 : w.regs 6 = read32 v.mem (v.regs 13 + 4#32 + 8#32)
  r7 : w.regs 7 = read32 v.mem (v.regs 13 + 4#32 + 12#32)
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → w.regs r = v.regs r
  mem : w.mem = v.mem
  scratch : ∀ r : Reg, r.val < 4 → w.regs r = 0#32

theorem ret_reach {base : Word} {W : Word → Word → Prop} {Rd : Word → Prop} (hb2 : base.toNat % 2 = 0) {v : State}
    (hpc : v.pc = base + BitVec.ofNat 32 oFRet) (hsp4 : (v.regs 13).toNat % 4 = 0)
    (hbit : (read32 v.mem (v.regs 13 + 4#32 + 16#32)).getLsbD 0 = true) :
    ReachS base (PNR ldAll W Rd) v (RetPost base v) := by
  refine ReachS.symBlockWNR (Ld := ldAll) hb2 [] [] [] fRet oFRet hpc (by decide) fRet_at (by decide) (by simp) (by simp)
    (by simp) (by decide +kernel) (by decide +kernel) ?_
  obtain ⟨zm, zz, zo⟩ := zero_eff v
  obtain ⟨v1, hv1⟩ : ∃ x, x = execAll zeroScratch v := ⟨_, rfl⟩
  rw [← hv1] at zm zz zo
  obtain ⟨a13, aoth, am⟩ := addSp_eff v1
  have hx : execAll fRet v = (Instr.addSp 1).next v1 := by rw [hv1]; rfl
  have hpv : (execAll fRet v).pc = base + BitVec.ofNat 32 oFPop := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  have b13 : (execAll fRet v).regs 13 = v.regs 13 + 4#32 := by rw [hx, a13, zo 13 (by decide) (by decide)]
  have bm : (execAll fRet v).mem = v.mem := by rw [hx, am, zm]
  have hbit' : (read32 (execAll fRet v).mem ((execAll fRet v).regs 13 + 16#32)).getLsbD 0 = true := by
    rw [b13, bm]; exact hbit
  obtain ⟨s1, hex, sm, s13, s4, s5, s6, s7, so, spc⟩ := pop_eff _ hbit'
  refine ReachS.stepNWNR hb2 oFPop uPop hpv (by decide) fPop_at (by rw [B_len]; decide) ?_ hex ?_ ?_
  · simp only [uPop, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
      Access.aligned, State.sp]
    rintro x ⟨a, ha, rfl⟩
    rw [b240] at ha
    simp only [Bool.toNat_true] at ha
    have hx13 := hsp4
    simp only [b13, BitVec.toNat_add, BitVec.toNat_ofNat, beq_iff_eq]
    have := (v.regs 13).isLt
    omega
  · intro y ⟨a, ha, hk, _⟩
    simp only [uPop, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp at hk
  · have h13 : (execAll fRet v).regs 13 = v.regs 13 + 4#32 := b13
    refine ReachS.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [spc, b13, bm]
    · rw [s13, b13]; bv_omega
    · rw [s4, b13, bm]
    · rw [s5, b13, bm]
    · rw [s6, b13, bm]
    · rw [s7, b13, bm]
    · intro r h8 h13' h15
      rw [so r (Or.inr h8) h13' h15, hx, aoth r h13' h15]; exact zo r (by omega) h15
    · rw [sm, bm]
    · intro r h4
      rw [so r (Or.inl h4) (by omega) (by omega), hx, aoth r (by omega) (by omega)]; exact zz r h4
