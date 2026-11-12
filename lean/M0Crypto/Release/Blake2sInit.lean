import M0Crypto.Release.Blake2sStreamEff
import M0Crypto.Release.Blake2sStreamBridge

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_init` -/

namespace M0Crypto.Release.Blake2sInit

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sPro (regs_push mem_push regs_ldrLit mem_ldrLit regs_stm mem_stm)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat codeWord read32_code)

open M0Crypto.Release.Blake2sTail (storeWords_append)

theorem w32_other (m : Mem) (a v y : Word) (h : ∀ k < 4, y ≠ a + BitVec.ofNat 32 k) :
    write32 m a v y = m y := by
  have h0 : y ≠ a := by simpa using h 0 (by omega)
  have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [write32]
  simp [h0, h1, h2, h3, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, show (3#32 : Word) = BitVec.ofNat 32 3 from rfl]

theorem pool_h0 (j : Nat) (hj : j < 8) : codeWord (iStart + 32 + 4 * j) = M0Crypto.Spec.Blake2s.h0[j]! := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem disj_ne {a b : Word} {n m : Nat} (h : Disj a n b m) {i j : Nat} (hi : i < n) (hj : j < m) :
    a + BitVec.ofNat 32 i ≠ b + BitVec.ofNat 32 j := by
  obtain ⟨h1, h2, h3⟩ := h
  intro eq
  have := congrArg BitVec.toNat eq
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

def iPool : Nat := iStart + 32

/-- The entry state of `m0c_blake2s_init(c = r0)` for an artifact loaded at `base`. -/
structure InitEntry (base : Word) (s : State) : Prop where
  base4 : base.toNat % 4 = 0
  pc : s.pc = base + BitVec.ofNat 32 iStart
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : 4 ≤ (s.regs 13).toNat
  c4 : (s.regs 0).toNat % 4 = 0
  lr : (s.regs 14).getLsbD 0 = true
  codeC : Disj base Artifacts.Release.size (s.regs 0) 112
  codeF : Disj base Artifacts.Release.size (s.regs 13 - 4#32) 4
  cF : Disj (s.regs 0) 112 (s.regs 13 - 4#32) 4

/-- Everything `init` may write: its 4-byte frame and the 112-byte context. -/
def WrI (s : State) : Word → Prop := fun y =>
  (∃ o < 4, y = s.regs 13 - 4#32 + BitVec.ofNat 32 o) ∨ (∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o)

/-- Agreement with the entry memory outside the write window. -/
def Ag (s : State) (M : Mem) : Prop := ∀ y, ¬ WrI s y → M y = s.mem y

theorem Ag.store {s : State} {M : Mem} (h : Ag s M) (a : Word) (vs : List Word)
    (hw : ∀ i k, i < vs.length → k < 4 → WrI s (a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k)) :
    Ag s (storeWords M a vs) := by
  intro y hy
  rw [storeWords_other _ _ _ _ (fun i k hi hk e => hy (by rw [e]; exact hw i k hi hk))]
  exact h y hy

theorem pool_ok {base : Word} {s : State} (e : InitEntry base s) {M : Mem} (h : Ag s M) (j : Nat) (hj : j < 8) :
    read32 M (base + BitVec.ofNat 32 (iPool + 4 * j)) = M0Crypto.Spec.Blake2s.h0[j]! := by
  have hsz : iPool + 4 * j + 4 ≤ Artifacts.Release.size := by
    have : iPool + 32 ≤ Artifacts.Release.size := by decide
    omega
  have hc := toNat_add_ofNat base (iPool + 4 * j) (by obtain ⟨h1, _, _⟩ := e.codeC; omega)
  rw [show read32 M (base + BitVec.ofNat 32 (iPool + 4 * j)) = read32 s.mem (base + BitVec.ofNat 32 (iPool + 4 * j)) from ?_]
  · rw [read32_code e.code _ hsz]
    exact pool_h0 j hj
  · apply read32_congr
    intro k hk
    apply h
    rintro (⟨o, ho, hy⟩ | ⟨o, ho, hy⟩)
    · rw [ofNat_add_assoc] at hy
      exact disj_ne e.codeF (i := iPool + 4 * j + k) (j := o) (by omega) ho hy
    · rw [ofNat_add_assoc] at hy
      exact disj_ne e.codeC (i := iPool + 4 * j + k) (j := o) (by omega) ho hy

theorem push_eff (s : State) :
    ((Instr.push 0 true).next s).mem = storeWords s.mem (s.regs 13 - 4#32) [s.regs 14] ∧
    ((Instr.push 0 true).next s).regs 13 = s.regs 13 - 4#32 ∧
    (∀ r : Reg, r ≠ 13 → r ≠ 15 → ((Instr.push 0 true).next s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_push]; simp [listRegs, bitCount]; rfl
  · rw [regs_push _ _ _ _ (by decide)]; simp [bitCount]; rfl
  · intro r h13 h15; rw [regs_push _ _ _ _ h15]; simp [h13]

theorem ld_eff (s : State) (t : LowReg) (imm : BitVec 8) (a v : Word)
    (ha : ((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4) = a) (hv : read32 s.mem a = v) :
    ((Instr.ldrLit t imm).next s).regs t.toReg = v ∧
    (∀ r : Reg, r ≠ t.toReg → r ≠ 15 → ((Instr.ldrLit t imm).next s).regs r = s.regs r) ∧
    ((Instr.ldrLit t imm).next s).mem = s.mem ∧
    ((Instr.ldrLit t imm).next s).pc = s.pc + 2#32 := by
  refine ⟨?_, ?_, mem_ldrLit _ _ _, ?_⟩
  · rw [regs_ldrLit _ _ _ _ (M0Crypto.Release.Blake2s.toReg_ne15 t), if_pos rfl, ha, hv]
  · intro r h1 h15; rw [regs_ldrLit _ _ _ _ h15]; simp [h1]
  · exact pc_next _ (by simp [Instr.falls]) s

theorem stm_eff (s : State) (l : BitVec 8) :
    ((Instr.stm 0 l).next s).regs 0 = s.regs 0 + BitVec.ofNat 32 (4 * bitCount l) ∧
    (∀ r : Reg, r ≠ 0 → r ≠ 15 → ((Instr.stm 0 l).next s).regs r = s.regs r) ∧
    ((Instr.stm 0 l).next s).mem = storeWords s.mem (s.regs 0) ((listRegs l).map (fun x => s.regs x.toReg)) ∧
    ((Instr.stm 0 l).next s).pc = s.pc + 2#32 := by
  refine ⟨?_, ?_, mem_stm _ _ _, pc_next _ (by simp [Instr.falls]) s⟩
  · rw [regs_stm _ _ _ _ (by decide)]; simp [State.reg]; rfl
  · intro r h0 h15; rw [regs_stm _ _ _ _ h15]; exact if_neg (fun h => h0 (by rw [h]; rfl))

theorem lit_pc {base : Word} (hb4 : base.toNat % 4 = 0) (t : State) (off imm j : Nat)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hT : (off + 4) / 4 * 4 + imm * 4 = iPool + 4 * j)
    (hlt : off + 4 + imm * 4 < Artifacts.Release.size)
    (hbase : base.toNat + Artifacts.Release.size ≤ 2 ^ 32) :
    ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm * 4) = base + BitVec.ofNat 32 (iPool + 4 * j) := by
  rw [hpc, M0Crypto.Release.Frame.lit_addr base hb4 off imm (by omega), hT]

theorem l123 : listRegs (14 : BitVec 8) = [1, 2, 3] := by decide
theorem b123 : bitCount (14 : BitVec 8) = 3 := by decide

def W8 : List Word := (List.range 8).map fun j => M0Crypto.Spec.Blake2s.h0[j]!

/-- The memory after the straight-line part of `init`. -/
def memB (s : State) : Mem :=
  write32 (storeWords (storeWords s.mem (s.regs 13 - 4#32) [s.regs 14]) (s.regs 0) (W8 ++ [0#32, 0#32]))
    (s.regs 0 + 104#32) 0#32


theorem pc_step {base : Word} (i : Instr) (hf : i.falls = true) (t : State) (off : Nat)
    (h : t.pc = base + BitVec.ofNat 32 off) :
    (i.next t).pc = base + BitVec.ofNat 32 (off + i.size) := by
  rw [pc_next i hf t, h, ofNat_add_assoc]

theorem ag_base {s : State} : Ag s s.mem := fun _ _ => rfl

theorem ag_frame {s : State} {M : Mem} (h : Ag s M) (v : Word) :
    Ag s (storeWords M (s.regs 13 - 4#32) [v]) :=
  h.store _ _ (fun i k hi hk => by
    left
    refine ⟨k, hk, ?_⟩
    simp at hi; subst hi; simp)

theorem ag_ctx {s : State} {M : Mem} (h : Ag s M) (o : Nat) (vs : List Word) (ho : o + 4 * vs.length ≤ 112) :
    Ag s (storeWords M (s.regs 0 + BitVec.ofNat 32 o) vs) :=
  h.store _ _ (fun i k hi hk => by
    right
    refine ⟨o + 4 * i + k, by omega, ?_⟩
    rw [ofNat_add_assoc, ofNat_add_assoc, Nat.add_assoc])

theorem ag_ctx0 {s : State} {M : Mem} (h : Ag s M) (vs : List Word) (ho : 4 * vs.length ≤ 112) :
    Ag s (storeWords M (s.regs 0) vs) := by
  have := ag_ctx h 0 vs (by omega)
  rwa [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] at this

open M0Crypto.Release.Blake2s (regs_movImm mem_movImm)

theorem block_eff {base : Word} {s : State} (e : InitEntry base s) :
    (execAll iA s).regs 13 = s.regs 13 - 4#32 ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → (execAll iA s).regs r = s.regs r) ∧
    (execAll iA s).pc = base + BitVec.ofNat 32 (iStart + 30) ∧
    (execAll iA s).mem = memB s := by
  have hb4 := e.base4
  have hbase : base.toNat + Artifacts.Release.size ≤ 2 ^ 32 := e.codeC.1
  have F : ∀ i : Instr, i.falls = true → i.falls = true := fun _ h => h
  -- states
  obtain ⟨s1, hs1⟩ : ∃ x, x = (Instr.push 0 true).next s := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ x, x = (Instr.ldrLit 1 7).next s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ x, x = (Instr.ldrLit 2 7).next s2 := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ x, x = (Instr.ldrLit 3 8).next s3 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ x, x = (Instr.stm 0 14).next s4 := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ x, x = (Instr.ldrLit 1 8).next s5 := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ x, x = (Instr.ldrLit 2 8).next s6 := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ x, x = (Instr.ldrLit 3 9).next s7 := ⟨_, rfl⟩
  obtain ⟨s9, hs9⟩ : ∃ x, x = (Instr.stm 0 14).next s8 := ⟨_, rfl⟩
  obtain ⟨s10, hs10⟩ : ∃ x, x = (Instr.ldrLit 1 9).next s9 := ⟨_, rfl⟩
  obtain ⟨s11, hs11⟩ : ∃ x, x = (Instr.ldrLit 2 9).next s10 := ⟨_, rfl⟩
  obtain ⟨s12, hs12⟩ : ∃ x, x = (Instr.movImm 3 0).next s11 := ⟨_, rfl⟩
  obtain ⟨s13, hs13⟩ : ∃ x, x = (Instr.stm 0 14).next s12 := ⟨_, rfl⟩
  obtain ⟨s14, hs14⟩ : ∃ x, x = (Instr.memImm .str 3 0 0).next s13 := ⟨_, rfl⟩
  obtain ⟨s15, hs15⟩ : ∃ x, x = (Instr.memImm .str 3 0 17).next s14 := ⟨_, rfl⟩
  have hx : execAll iA s = s15 := by
    rw [hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]; rfl
  have hlt : ∀ (off imm : Nat), off + 4 + imm * 4 < Artifacts.Release.size → True := fun _ _ _ => trivial
  -- step 1: push {lr}
  obtain ⟨m1, r13_1, ro1⟩ := push_eff s
  rw [← hs1] at m1 r13_1 ro1
  have p1 : s1.pc = base + BitVec.ofNat 32 (iStart + 2) := by
    rw [hs1]; exact pc_step _ (by decide) s _ e.pc
  have a1 : Ag s s1.mem := by rw [m1]; exact ag_frame ag_base _
  -- literal loads
  have ld : ∀ (s0 s' : State) (t : LowReg) (imm : BitVec 8) (off j : Nat),
      s' = (Instr.ldrLit t imm).next s0 → s0.pc = base + BitVec.ofNat 32 off →
      (off + 4) / 4 * 4 + imm.toNat * 4 = iPool + 4 * j → off + 4 + imm.toNat * 4 < Artifacts.Release.size →
      j < 8 → Ag s s0.mem →
      s'.regs t.toReg = M0Crypto.Spec.Blake2s.h0[j]! ∧
      (∀ r : Reg, r ≠ t.toReg → r ≠ 15 → s'.regs r = s0.regs r) ∧ s'.mem = s0.mem ∧
      s'.pc = base + BitVec.ofNat 32 (off + 2) := by
    intro s0 s' t imm off j hs hpc hT hl hj ha
    subst hs
    obtain ⟨x1, x2, x3, x4⟩ := ld_eff s0 t imm _ _ (lit_pc hb4 s0 off imm.toNat j hpc hT hl hbase)
      (pool_ok e ha j hj)
    exact ⟨x1, x2, x3, by rw [x4, hpc, ofNat_add_assoc]⟩
  have hlt : True := trivial
  -- s2..s4
  obtain ⟨v2', o2, mm2, p2⟩ := ld s1 s2 1 7 (iStart + 2) 0 hs2 p1 (by decide) (by decide) (by decide) a1
  obtain ⟨v3', o3, mm3, p3⟩ := ld s2 s3 2 7 (iStart + 4) 1 hs3 p2 (by decide) (by decide) (by decide) (by rw [mm2]; exact a1)
  obtain ⟨v4, o4, mm4, p4⟩ := ld s3 s4 3 8 (iStart + 6) 2 hs4 p3 (by decide) (by decide) (by decide) (by rw [mm3, mm2]; exact a1)
  have v2 : s2.regs 1 = M0Crypto.Spec.Blake2s.h0[0]! := v2'
  have v3 : s3.regs 2 = M0Crypto.Spec.Blake2s.h0[1]! := v3'
  have r0_4 : s4.regs 0 = s.regs 0 := by
    rw [o4 0 (by decide) (by decide), o3 0 (by decide) (by decide), o2 0 (by decide) (by decide), ro1 0 (by decide) (by decide)]
  have m4 : s4.mem = s1.mem := by rw [mm4, mm3, mm2]
  -- s5: stm
  obtain ⟨x0, xo, xm, xp⟩ := stm_eff s4 14
  rw [← hs5] at x0 xo xm xp
  rw [l123] at xm
  have r1_4 : s4.regs 1 = M0Crypto.Spec.Blake2s.h0[0]! := by rw [o4 1 (by decide) (by decide), o3 1 (by decide) (by decide), v2]
  have r2_4 : s4.regs 2 = M0Crypto.Spec.Blake2s.h0[1]! := by rw [o4 2 (by decide) (by decide), v3]
  have r3_4 : s4.regs 3 = M0Crypto.Spec.Blake2s.h0[2]! := v4
  have pc5 : s5.pc = base + BitVec.ofNat 32 (iStart + 10) := by
    rw [xp, p4, ofNat_add_assoc]
  have m5 : s5.mem = storeWords s1.mem (s.regs 0) [M0Crypto.Spec.Blake2s.h0[0]!, M0Crypto.Spec.Blake2s.h0[1]!, M0Crypto.Spec.Blake2s.h0[2]!] := by
    rw [xm, m4, r0_4]
    have e1 : s4.regs (LowReg.toReg 1) = _ := r1_4
    have e2 : s4.regs (LowReg.toReg 2) = _ := r2_4
    have e3 : s4.regs (LowReg.toReg 3) = _ := r3_4
    simp [e1, e2, e3]
  have a5 : Ag s s5.mem := by rw [m5]; exact ag_ctx0 a1 _ (by simp)
  have rr5 : ∀ r : Reg, r ≠ 0 → r ≠ 15 → s5.regs r = s4.regs r := xo
  have r0_5 : s5.regs 0 = s.regs 0 + 12#32 := by rw [x0, r0_4]; rfl
  -- s6..s8
  obtain ⟨v6', o6, mm6, p6⟩ := ld s5 s6 1 8 (iStart + 10) 3 hs6 pc5 (by decide) (by decide) (by decide) a5
  obtain ⟨v7', o7, mm7, p7⟩ := ld s6 s7 2 8 (iStart + 12) 4 hs7 p6 (by decide) (by decide) (by decide) (by rw [mm6]; exact a5)
  obtain ⟨v8, o8, mm8, p8⟩ := ld s7 s8 3 9 (iStart + 14) 5 hs8 p7 (by decide) (by decide) (by decide) (by rw [mm7, mm6]; exact a5)
  have v6 : s6.regs 1 = M0Crypto.Spec.Blake2s.h0[3]! := v6'
  have v7 : s7.regs 2 = M0Crypto.Spec.Blake2s.h0[4]! := v7'
  have r0_8 : s8.regs 0 = s.regs 0 + 12#32 := by
    rw [o8 0 (by decide) (by decide), o7 0 (by decide) (by decide), o6 0 (by decide) (by decide), r0_5]
  have m8 : s8.mem = s5.mem := by rw [mm8, mm7, mm6]
  have r1_8 : s8.regs 1 = M0Crypto.Spec.Blake2s.h0[3]! := by rw [o8 1 (by decide) (by decide), o7 1 (by decide) (by decide), v6]
  have r2_8 : s8.regs 2 = M0Crypto.Spec.Blake2s.h0[4]! := by rw [o8 2 (by decide) (by decide), v7]
  have r3_8 : s8.regs 3 = M0Crypto.Spec.Blake2s.h0[5]! := v8
  obtain ⟨y0, yo, ym, yp⟩ := stm_eff s8 14
  rw [← hs9] at y0 yo ym yp
  rw [l123] at ym
  have pc9 : s9.pc = base + BitVec.ofNat 32 (iStart + 18) := by
    rw [yp, p8, ofNat_add_assoc]
  have m9 : s9.mem = storeWords s5.mem (s.regs 0 + 12#32) [M0Crypto.Spec.Blake2s.h0[3]!, M0Crypto.Spec.Blake2s.h0[4]!, M0Crypto.Spec.Blake2s.h0[5]!] := by
    rw [ym, m8, r0_8]
    have e1 : s8.regs (LowReg.toReg 1) = _ := r1_8
    have e2 : s8.regs (LowReg.toReg 2) = _ := r2_8
    have e3 : s8.regs (LowReg.toReg 3) = _ := r3_8
    simp [e1, e2, e3]
  have a9 : Ag s s9.mem := by rw [m9]; exact ag_ctx a5 12 _ (by simp)
  have r0_9 : s9.regs 0 = s.regs 0 + 24#32 := by
    rw [y0, r0_8, BitVec.add_assoc]; rfl
  -- s10..s13
  obtain ⟨v10', o10, mm10, p10⟩ := ld s9 s10 1 9 (iStart + 18) 6 hs10 pc9 (by decide) (by decide) (by decide) a9
  obtain ⟨v11', o11, mm11, p11⟩ := ld s10 s11 2 9 (iStart + 20) 7 hs11 p10 (by decide) (by decide) (by decide) (by rw [mm10]; exact a9)
  have v10 : s10.regs 1 = M0Crypto.Spec.Blake2s.h0[6]! := v10'
  have v11 : s11.regs 2 = M0Crypto.Spec.Blake2s.h0[7]! := v11'
  have p12 : s12.pc = base + BitVec.ofNat 32 (iStart + 24) := by
    rw [hs12]; exact pc_step _ (by decide) s11 _ p11
  have r0_12 : s12.regs 0 = s.regs 0 + 24#32 := by
    rw [hs12, regs_movImm _ _ _ _ (by decide), if_neg (by decide), o11 0 (by decide) (by decide), o10 0 (by decide) (by decide), r0_9]
  have r1_12 : s12.regs 1 = M0Crypto.Spec.Blake2s.h0[6]! := by
    rw [hs12, regs_movImm _ _ _ _ (by decide), if_neg (by decide), o11 1 (by decide) (by decide), v10]
  have r2_12 : s12.regs 2 = M0Crypto.Spec.Blake2s.h0[7]! := by
    rw [hs12, regs_movImm _ _ _ _ (by decide), if_neg (by decide), v11]
  have r3_12 : s12.regs 3 = 0#32 := by
    rw [hs12, regs_movImm _ _ _ _ (by decide), if_pos (by decide)]; rfl
  have m12 : s12.mem = s9.mem := by rw [hs12, mem_movImm, mm11, mm10]
  obtain ⟨z0, zo, zm, zp⟩ := stm_eff s12 14
  rw [← hs13] at z0 zo zm zp
  rw [l123] at zm
  have pc13 : s13.pc = base + BitVec.ofNat 32 (iStart + 26) := by
    rw [zp, p12, ofNat_add_assoc]
  have m13 : s13.mem = storeWords s9.mem (s.regs 0 + 24#32) [M0Crypto.Spec.Blake2s.h0[6]!, M0Crypto.Spec.Blake2s.h0[7]!, 0#32] := by
    rw [zm, m12, r0_12]
    have e1 : s12.regs (LowReg.toReg 1) = _ := r1_12
    have e2 : s12.regs (LowReg.toReg 2) = _ := r2_12
    have e3 : s12.regs (LowReg.toReg 3) = _ := r3_12
    simp [e1, e2, e3]
  have r0_13 : s13.regs 0 = s.regs 0 + 36#32 := by
    rw [z0, r0_12, BitVec.add_assoc]; rfl
  have r3_13 : s13.regs 3 = 0#32 := by rw [zo 3 (by decide) (by decide), r3_12]
  -- s14, s15: str r3
  have q14 := mem_str s13 3 0 0
  rw [← hs14] at q14
  have q15 := mem_str s14 3 0 17
  rw [← hs15] at q15
  have R14 : ∀ r : Reg, r ≠ 15 → s14.regs r = s13.regs r := by
    intro r hr; rw [hs14]; exact regs_str _ _ _ _ _ hr
  have R15 : ∀ r : Reg, r ≠ 15 → s15.regs r = s14.regs r := by
    intro r hr; rw [hs15]; exact regs_str _ _ _ _ _ hr
  have r0_14 : s14.regs 0 = s.regs 0 + 36#32 := by rw [R14 0 (by decide), r0_13]
  have pc15 : s15.pc = base + BitVec.ofNat 32 (iStart + 30) := by
    have h14 : s14.pc = base + BitVec.ofNat 32 (iStart + 28) := by
      rw [hs14]; exact pc_step _ (by decide) s13 _ pc13
    rw [hs15]; exact pc_step _ (by decide) s14 _ h14
  have r3_14 : s14.regs 3 = 0#32 := by rw [R14 3 (by decide), r3_13]
  have hq : ∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → s15.regs r = s1.regs r := by
    intro r h4 h15
    have n15 : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    have n0 : r ≠ 0 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have n1 : r ≠ 1 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have n2 : r ≠ 2 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have n3 : r ≠ 3 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have r12 : s12.regs r = s11.regs r := by
      rw [hs12, regs_movImm _ _ _ _ n15, if_neg (by exact n3)]
    rw [R15 r n15, R14 r n15, zo r n0 n15, r12, o11 r (by exact n2) n15, o10 r (by exact n1) n15,
      yo r n0 n15, o8 r (by exact n3) n15, o7 r (by exact n2) n15, o6 r (by exact n1) n15,
      xo r n0 n15, o4 r (by exact n3) n15, o3 r (by exact n2) n15, o2 r (by exact n1) n15]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hx, hq 13 (by decide) (by decide), r13_1]
  · intro r h4 h13 h15
    rw [hx, hq r h4 h15, ro1 r (fun h => h13 (by rw [h]; rfl)) (fun h => h15 (by rw [h]; rfl))]
  · rw [hx]; exact pc15
  · have e0 : s14.regs (LowReg.toReg 0) = s.regs 0 + 36#32 := r0_14
    have e3 : s14.regs (LowReg.toReg 3) = 0#32 := r3_14
    have f0 : s13.regs (LowReg.toReg 0) = s.regs 0 + 36#32 := r0_13
    have f3 : s13.regs (LowReg.toReg 3) = 0#32 := r3_13
    have mA : s13.mem = storeWords s1.mem (s.regs 0)
        ([M0Crypto.Spec.Blake2s.h0[0]!, M0Crypto.Spec.Blake2s.h0[1]!, M0Crypto.Spec.Blake2s.h0[2]!] ++ [M0Crypto.Spec.Blake2s.h0[3]!, M0Crypto.Spec.Blake2s.h0[4]!, M0Crypto.Spec.Blake2s.h0[5]!] ++ [M0Crypto.Spec.Blake2s.h0[6]!, M0Crypto.Spec.Blake2s.h0[7]!, 0#32]) := by
      rw [m13, m9, m5, storeWords_append, storeWords_append]
      simp
    have hW : W8 ++ [0#32, 0#32] = ([M0Crypto.Spec.Blake2s.h0[0]!, M0Crypto.Spec.Blake2s.h0[1]!, M0Crypto.Spec.Blake2s.h0[2]!] ++ [M0Crypto.Spec.Blake2s.h0[3]!, M0Crypto.Spec.Blake2s.h0[4]!, M0Crypto.Spec.Blake2s.h0[5]!] ++ [M0Crypto.Spec.Blake2s.h0[6]!, M0Crypto.Spec.Blake2s.h0[7]!, 0#32]) ++ [0#32] := by
      simp [W8, List.range, List.range.loop]
    rw [hx, q15, q14, e0, e3, f0, f3, mA, memB, hW, m1]
    have h104 : s.regs 0 + 36#32 + BitVec.ofNat 32 (BitVec.toNat (17 : BitVec 5) * 4) = s.regs 0 + 104#32 := by
      rw [BitVec.add_assoc]; rfl
    have h36 : s.regs 0 + 36#32 + BitVec.ofNat 32 (BitVec.toNat (0 : BitVec 5) * 4) = s.regs 0 + BitVec.ofNat 32 (4 * 9) := by
      rw [BitVec.add_assoc]; rfl
    rw [h104, h36, storeWords_append _ _ [0#32]]
    simp only [storeWords, List.length_append, List.length_cons, List.length_nil]

open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat read32_storeWords_same)

theorem W8_len : (W8 ++ [0#32, 0#32]).length = 10 := by simp [W8]

theorem ctx_memB {base : Word} {s : State} (e : InitEntry base s) :
    Ctx (memB s) (s.regs 0) M0Crypto.Spec.Blake2s.State.init := by
  obtain ⟨h1, h2, h3⟩ := e.codeC
  obtain ⟨g1, g2, g3⟩ := e.cF
  have c112 : (s.regs 0).toNat + 112 ≤ 2 ^ 32 := g1
  -- reading a ctx word below 40 bytes
  have rdA : ∀ i (hi : i < 10), read32 (memB s) (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
      (W8 ++ [0#32, 0#32])[i]'(by rw [W8_len]; exact hi) := by
    intro i hi
    unfold memB
    rw [read32_congr (m := storeWords (storeWords s.mem (s.regs 13 - 4#32) [s.regs 14]) (s.regs 0) (W8 ++ [0#32, 0#32]))]
    · exact read32_storeWords_same _ _ _ i (by rw [W8_len]; exact hi) (by rw [W8_len]; omega)
    · intro k hk
      apply M0Crypto.Armv6M.write32_other
      intro j hj heq
      rw [show (104#32) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc, ofNat_add_assoc] at heq
      have := congrArg BitVec.toNat heq
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
      omega
  have rdU : read32 (memB s) (s.regs 0 + 104#32) = 0#32 := by
    unfold memB
    exact M0Crypto.Armv6M.read32_write32_same _ _ _
  have rdW : ∀ i (hi : i < 8), read32 (memB s) (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
      M0Crypto.Spec.Blake2s.h0[i]! := by
    intro i hi
    rw [rdA i (by omega)]
    have hl : i < W8.length := by simp [W8]; omega
    rw [List.getElem_append_left hl]
    simp [W8, hi]
  refine { hsz := ?_, h := rdW, clo := ?_, chi := ?_, cnt := ?_, plen := ?_, buf := ?_, used := ?_ }
  · simp [M0Crypto.Spec.Blake2s.State.init, M0Crypto.Spec.Blake2s.h0, M0Crypto.Spec.Blake2s.IV]
  · have := rdA 8 (by omega)
    rw [show (s.regs 0 + 32#32) = s.regs 0 + BitVec.ofNat 32 (4 * 8) from rfl, this]
    simp [W8, M0Crypto.Spec.Blake2s.State.init]
  · have := rdA 9 (by omega)
    rw [show (s.regs 0 + 36#32) = s.regs 0 + BitVec.ofNat 32 (4 * 9) from rfl, this]
    simp [W8, M0Crypto.Spec.Blake2s.State.init]
  · simp [M0Crypto.Spec.Blake2s.State.init]
  · simp [M0Crypto.Spec.Blake2s.State.init]
  · simp [M0Crypto.Spec.Blake2s.State.init, bytesAt]
  · rw [rdU]; simp [M0Crypto.Spec.Blake2s.State.init]

theorem pop_pc_exec (t : State) (hbit : (read32 t.mem (t.regs 13)).getLsbD 0 = true) :
    ∃ s1, iPop.exec t = .ok s1 ∧ s1.mem = t.mem ∧ s1.regs 13 = t.regs 13 + 4#32 ∧
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → s1.regs r = t.regs r) ∧
      s1.pc = read32 t.mem (t.regs 13) &&& ~~~1#32 := by
  have hb : bitCount (0#8) = 0 := by decide
  have h1 : (read32 t.mem (t.sp + BitVec.ofNat 32 (4 * bitCount 0))).getLsbD 0 = true := by
    simpa [State.sp, hb] using hbit
  unfold iPop
  simp only [Instr.exec, if_true, h1]
  refine ⟨_, rfl, ?_⟩
  have hl : listRegs (0#8) = [] := by decide
  simp (config := {decide := true}) [hl, hb, loadRegs, State.setReg, State.sp, State.pc, Fin.ext_iff]
  intro r h13 h15
  have a15 : ((15 : Reg) : Nat) = 15 := rfl
  have a13 : ((13 : Reg) : Nat) = 13 := rfl
  simp [a15, a13, h13, h15]

/-- What `init` leaves: returned, `sp` and `r4`-`r11` restored, a fresh context, memory
unchanged outside the frame and the context. -/
structure InitPost (s t : State) : Prop where
  pc : t.pc = s.regs 14 &&& ~~~1#32
  sp : t.regs 13 = s.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → t.regs r = s.regs r
  ctx : Ctx t.mem (s.regs 0) M0Crypto.Spec.Blake2s.State.init
  mem : ∀ y, (∀ o < 4, y ≠ s.regs 13 - 4#32 + BitVec.ofNat 32 o) →
    (∀ o < 112, y ≠ s.regs 0 + BitVec.ofNat 32 o) → t.mem y = s.mem y

theorem memB_other {s : State} (y : Word)
    (h1 : ∀ o < 4, y ≠ s.regs 13 - 4#32 + BitVec.ofNat 32 o)
    (h2 : ∀ o < 112, y ≠ s.regs 0 + BitVec.ofNat 32 o) : memB s y = s.mem y := by
  unfold memB
  rw [M0Crypto.Armv6M.write32_other _ _ _ _ (fun k hk => h2 (104 + k) (by omega)
      |> fun h => by rw [show (104#32) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc]; exact h)]
  rw [storeWords_other _ _ _ _ (fun i k hi hk => by
      have := h2 (4 * i + k) (by simp [W8] at hi; omega)
      rwa [← ofNat_add_assoc] at this)]
  rw [storeWords_other _ _ _ _ (fun i k hi hk => by
      simp at hi; subst hi
      have := h1 k hk
      simpa using this)]

theorem rd_frame {base : Word} {s : State} (e : InitEntry base s) :
    read32 (memB s) (s.regs 13 - 4#32) = s.regs 14 := by
  obtain ⟨g1, g2, g3⟩ := e.cF
  unfold memB
  rw [read32_congr (m := storeWords (storeWords s.mem (s.regs 13 - 4#32) [s.regs 14]) (s.regs 0) (W8 ++ [0#32, 0#32]))]
  · rw [read32_congr (m := storeWords s.mem (s.regs 13 - 4#32) [s.regs 14])]
    · have := read32_storeWords_same s.mem (s.regs 13 - 4#32) [s.regs 14] 0 (by simp) (by simp)
      simpa using this
    · intro k hk
      apply storeWords_other
      intro i j hi hj heq
      simp [W8] at hi
      rw [ofNat_add_assoc] at heq
      have := congrArg BitVec.toNat heq
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
      omega
  · intro k hk
    apply M0Crypto.Armv6M.write32_other
    intro j hj heq
    rw [show (104#32) = BitVec.ofNat 32 104 from rfl, ofNat_add_assoc] at heq
    have := congrArg BitVec.toNat heq
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
    omega

theorem init_reach {base : Word} {s : State} (e : InitEntry base s) :
    Reach base (WrI s) s (InitPost s) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  obtain ⟨b13, bo, bpc, bm⟩ := block_eff e
  refine Reach.symBlock hb2 [((13 : Reg), 4), ((0 : Reg), 4)] [((13 : Reg), (0#32 - 4#32), 4), ((0 : Reg), 0#32, 40), ((0 : Reg), 104#32, 4)]
    iA iStart e.pc (by decide) iA_at (by decide) ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact e.sp4
    · exact e.c4
  · intro p hp o ho
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨o, ho, by bv_omega⟩
    · exact Or.inr ⟨o, by simp at ho; omega, by simp⟩
    · exact Or.inr ⟨104 + o, by simp at ho; omega, by
        rw [ofNat_add_assoc]⟩
  · have hsp4 : (s.regs 13 - 4#32).toNat % 4 = 0 := by
      have := e.sp4; have := e.spLo; have := (s.regs 13).isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hbit : (read32 (execAll iA s).mem ((execAll iA s).regs 13)).getLsbD 0 = true := by
      rw [b13, bm]
      rw [rd_frame e]; exact e.lr
    obtain ⟨s1, hex, sm, s13', so, spc⟩ := pop_pc_exec _ hbit
    refine Reach.step hb2 oIPop iPop (by rw [bpc]; rfl) (by decide) iPop_at (by rw [B_len]; decide) ?_ hex ?_ ?_
    · have hb0 : bitCount (0#8) = 0 := by decide
      simp only [iPop, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
        Access.aligned, State.sp, hb0, b13]
      rintro _ ⟨i, hi, rfl⟩
      simp only [Bool.toNat_true] at hi
      have hz : bitCount (0 : BitVec 8) = 0 := by decide
      simp only [hz] at hi
      have : i = 0 := by omega
      subst this
      simpa using hsp4
    · intro y ⟨a, ha, hk, _⟩
      simp only [iPop, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
      obtain ⟨i, _, rfl⟩ := ha
      simp at hk
    · refine Reach.done ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [spc, b13, bm, rd_frame e]
      · rw [s13', b13]; bv_omega
      · intro r h4 h11
        rw [so r (by omega) (by omega), bo r h4 (by omega) (by omega)]
      · rw [sm, bm]; exact ctx_memB e
      · intro y h1 h2
        rw [sm, bm]; exact memB_other y h1 h2

end M0Crypto.Release.Blake2sInit
