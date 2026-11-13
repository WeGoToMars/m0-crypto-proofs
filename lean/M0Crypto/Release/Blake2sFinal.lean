import M0Crypto.Release.Blake2sFinalEff
import M0Crypto.Release.Blake2sInit
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final` -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sPro (regs_push mem_push)
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat read32_storeWords_same)
open M0Crypto.Release.Blake2s (regs_addReg regs_movImm mem_addReg mem_movImm)

theorem l4567 : listRegs (240 : BitVec 8) = [4, 5, 6, 7] := by decide
theorem b4567 : bitCount (240 : BitVec 8) = 4 := by decide

theorem add64 (lo hi u : BitVec 32) (h : lo.toNat + 2 ^ 32 * hi.toNat + u.toNat < 2 ^ 64) :
    (lo + u).toNat + 2 ^ 32 * (addWithCarry hi 0#32 (addWithCarry lo u false).2.1).1.toNat =
      lo.toNat + 2 ^ 32 * hi.toNat + u.toNat := by
  have hl := lo.isLt; have hh := hi.isLt; have hu := u.isLt
  by_cases hc : lo.toNat + u.toNat < 2 ^ 32
  · have : (addWithCarry lo u false).2.1 = false := by
      simp [addWithCarry, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    rw [this]
    simp [addWithCarry, BitVec.toNat_add, Nat.mod_eq_of_lt hc]
    omega
  · have hs : (lo.toNat + u.toNat) % 2 ^ 32 = lo.toNat + u.toNat - 2 ^ 32 := by omega
    have : (addWithCarry lo u false).2.1 = true := by
      simp [addWithCarry, BitVec.toNat_ofNat, hs]; omega
    rw [this]
    simp [addWithCarry, BitVec.toNat_add, hs, BitVec.toNat_ofNat]
    have : (hi.toNat + 1) % 2 ^ 32 = hi.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- The entry state of `m0c_blake2s_final(c = r0, out = r1)`: a context holding stream `st`. -/
structure FinalEntry (base : Word) (s : State) (st : M0Crypto.Spec.Blake2s.State) : Prop where
  base4 : base.toNat % 4 = 0
  pc : s.pc = base + BitVec.ofNat 32 fStart
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : STREAM_FRAME ≤ (s.regs 13).toNat
  c4 : (s.regs 0).toNat % 4 = 0
  lr : (s.regs 14).getLsbD 0 = true
  ctx : Ctx s.mem (s.regs 0) st
  cnt : st.count + st.pending.length < 2 ^ 64
  codeC : Disj base Artifacts.Release.size (s.regs 0) 112
  codeF : Disj base Artifacts.Release.size (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME
  codeO : Disj base Artifacts.Release.size (s.regs 1) 32
  cF : Disj (s.regs 0) 112 (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME
  oF : Disj (s.regs 1) 32 (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME
  cO : Disj (s.regs 0) 112 (s.regs 1) 32

/-- Everything `final` may write: its frame and the compress frame, the context, the output. -/
def WrF (s : State) : Word → Prop := fun y =>
  (∃ o < STREAM_FRAME, y = s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 o) ∨ (∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o) ∨
    (∃ o < 32, y = s.regs 1 + BitVec.ofNat 32 o)

theorem rd_ctx {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st)
    (k : Nat) (hk : k + 4 ≤ 112) :
    read32 (storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14])
      (s.regs 0 + BitVec.ofNat 32 k) = read32 s.mem (s.regs 0 + BitVec.ofNat 32 k) := by
  obtain ⟨g1, g2, g3⟩ := e.cF
  apply read32_congr
  intro j hj
  apply storeWords_other
  intro i m hi hm heq
  simp at hi
  rw [ofNat_add_assoc, ofNat_add_assoc] at heq
  have h20 : s.regs 13 - 20#32 = (s.regs 13 - STREAM_FRAME_W) + BitVec.ofNat 32 STREAM_LOCALS := by bv_omega
  rw [h20, ofNat_add_assoc] at heq
  have := congrArg BitVec.toNat heq
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

theorem pro_eff {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State} (e : FinalEntry base s st) :
    (execAll fPro s).regs 13 = s.regs 13 - 24#32 ∧ (execAll fPro s).regs 4 = s.regs 0 ∧
    (execAll fPro s).regs 5 = s.regs 1 ∧ (execAll fPro s).regs 6 = BitVec.ofNat 32 st.pending.length ∧
    (execAll fPro s).regs 0 = 0#32 ∧ (execAll fPro s).regs 1 = s.regs 0 + 40#32 ∧
    ((execAll fPro s).regs 2).toNat + 2 ^ 32 * ((execAll fPro s).regs 3).toNat =
      st.count + st.pending.length ∧
    (∀ r : Reg, 7 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → (execAll fPro s).regs r = s.regs r) ∧
    (execAll fPro s).mem = storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] ∧
    (execAll fPro s).pc = base + BitVec.ofNat 32 oPadB := by
  obtain ⟨s1, hs1⟩ : ∃ x, x = (Instr.push 0xF0 true).next s := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ x, x = (Instr.subSp 1).next s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ x, x = (Instr.lslImm 4 0 0).next s2 := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ x, x = (Instr.lslImm 5 1 0).next s3 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ x, x = (Instr.memImm .ldr 6 4 26).next s4 := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ x, x = (Instr.memImm .ldr 2 4 8).next s5 := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ x, x = (Instr.memImm .ldr 3 4 9).next s6 := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ x, x = (Instr.movImm 0 0).next s7 := ⟨_, rfl⟩
  obtain ⟨s9, hs9⟩ : ∃ x, x = (Instr.addReg 2 2 6).next s8 := ⟨_, rfl⟩
  obtain ⟨s10, hs10⟩ : ∃ x, x = (Instr.dp .adcs 3 0).next s9 := ⟨_, rfl⟩
  obtain ⟨s11, hs11⟩ : ∃ x, x = (Instr.movImm 1 0x28).next s10 := ⟨_, rfl⟩
  obtain ⟨s12, hs12⟩ : ∃ x, x = (Instr.addReg 1 1 4).next s11 := ⟨_, rfl⟩
  have hx : execAll fPro s = s12 := by
    rw [hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]; rfl
  have n15 : ∀ r : Reg, r.val ≠ 15 → r ≠ 15 := fun r h h' => h (by rw [h']; rfl)
  -- s1: push {r4-r7,lr}
  have p1r13 : s1.regs 13 = s.regs 13 - 20#32 := by
    rw [hs1, regs_push _ _ _ _ (by decide), if_pos rfl, b4567]; rfl
  have p1o : ∀ r : Reg, r ≠ 13 → r ≠ 15 → s1.regs r = s.regs r := by
    intro r h13 h15; rw [hs1, regs_push _ _ _ _ h15, if_neg h13]
  have p1m : s1.mem = storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] := by
    rw [hs1, mem_push, l4567, b4567]; rfl
  -- s2: sub sp, #4
  have p2r13 : s2.regs 13 = s.regs 13 - 24#32 := by
    rw [hs2, regs_subSp _ _ _ (by decide), if_pos rfl, p1r13]; simp; bv_omega
  have p2o : ∀ r : Reg, r ≠ 13 → r ≠ 15 → s2.regs r = s1.regs r := by
    intro r h13 h15; rw [hs2, regs_subSp _ _ _ h15, if_neg h13]
  have p2m : s2.mem = s1.mem := by rw [hs2, mem_subSp]
  -- s3: r4 = r0
  have p3o : ∀ r : Reg, r ≠ 4 → r ≠ 15 → s3.regs r = s2.regs r := by
    intro r h4 h15; rw [hs3, regs_lsl _ _ _ _ _ h15]; exact if_neg (fun h' => h4 h')
  have p3r4 : s3.regs 4 = s2.regs 0 := by
    rw [hs3, regs_lsl _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; simp [lslC, State.reg]; rfl
  have p3m : s3.mem = s2.mem := by rw [hs3, mem_lsl]
  -- s4: r5 = r1
  have p4o : ∀ r : Reg, r ≠ 5 → r ≠ 15 → s4.regs r = s3.regs r := by
    intro r h5 h15; rw [hs4, regs_lsl _ _ _ _ _ h15]; exact if_neg (fun h' => h5 h')
  have p4r5 : s4.regs 5 = s3.regs 1 := by
    rw [hs4, regs_lsl _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; simp [lslC, State.reg]; rfl
  have p4m : s4.mem = s3.mem := by rw [hs4, mem_lsl]
  have r0_2 : s2.regs 0 = s.regs 0 := by rw [p2o 0 (by decide) (by decide), p1o 0 (by decide) (by decide)]
  have r1_3 : s3.regs 1 = s.regs 1 := by
    rw [p3o 1 (by decide) (by decide), p2o 1 (by decide) (by decide), p1o 1 (by decide) (by decide)]
  have r4_4 : s4.regs 4 = s.regs 0 := by rw [p4o 4 (by decide) (by decide), p3r4, r0_2]
  have m4 : s4.mem = storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] := by
    rw [p4m, p3m, p2m, p1m]
  -- s5..s7: ldr
  have p5o : ∀ r : Reg, r ≠ 6 → r ≠ 15 → s5.regs r = s4.regs r := by
    intro r h h15; rw [hs5, regs_ldr _ _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p5r6 : s5.regs 6 = BitVec.ofNat 32 st.pending.length := by
    rw [hs5, regs_ldr _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_
    have : s4.reg 4 = s.regs 0 := r4_4
    rw [this, m4, show BitVec.ofNat 32 (BitVec.toNat (26 : BitVec 5) * 4) = 104#32 from rfl]
    have h104 : read32 (storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 0 + 104#32) = read32 s.mem (s.regs 0 + 104#32) := rd_ctx e 104 (by omega)
    rw [h104]
    exact e.ctx.used
  have p5m : s5.mem = s4.mem := by rw [hs5, mem_ldr]
  have p6o : ∀ r : Reg, r ≠ 2 → r ≠ 15 → s6.regs r = s5.regs r := by
    intro r h h15; rw [hs6, regs_ldr _ _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p6m : s6.mem = s5.mem := by rw [hs6, mem_ldr]
  have p6r2 : s6.regs 2 = BitVec.ofNat 32 st.count := by
    rw [hs6, regs_ldr _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_
    have : s5.reg 4 = s.regs 0 := by
      show s5.regs 4 = _
      rw [p5o 4 (by decide) (by decide), r4_4]
    rw [this, p5m, m4, show BitVec.ofNat 32 (BitVec.toNat (8 : BitVec 5) * 4) = 32#32 from rfl]
    have h32 : read32 (storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 0 + 32#32) = read32 s.mem (s.regs 0 + 32#32) := rd_ctx e 32 (by omega)
    rw [h32]
    exact e.ctx.clo
  have p7o : ∀ r : Reg, r ≠ 3 → r ≠ 15 → s7.regs r = s6.regs r := by
    intro r h h15; rw [hs7, regs_ldr _ _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p7m : s7.mem = s6.mem := by rw [hs7, mem_ldr]
  have p7r3 : s7.regs 3 = BitVec.ofNat 32 (st.count / 2 ^ 32) := by
    rw [hs7, regs_ldr _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_
    have : s6.reg 4 = s.regs 0 := by
      show s6.regs 4 = _
      rw [p6o 4 (by decide) (by decide), p5o 4 (by decide) (by decide), r4_4]
    rw [this, p6m, p5m, m4, show BitVec.ofNat 32 (BitVec.toNat (9 : BitVec 5) * 4) = 36#32 from rfl]
    have h36 : read32 (storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 0 + 36#32) = read32 s.mem (s.regs 0 + 36#32) := rd_ctx e 36 (by omega)
    rw [h36]
    exact e.ctx.chi
  -- s8: r0 = 0
  have p8o : ∀ r : Reg, r ≠ 0 → r ≠ 15 → s8.regs r = s7.regs r := by
    intro r h h15; rw [hs8, regs_movImm _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p8r0 : s8.regs 0 = 0#32 := by
    rw [hs8, regs_movImm _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; rfl
  have p8m : s8.mem = s7.mem := by rw [hs8, mem_movImm]
  -- s9: r2 = r2 + r6
  have p9o : ∀ r : Reg, r ≠ 2 → r ≠ 15 → s9.regs r = s8.regs r := by
    intro r h h15; rw [hs9, regs_addReg _ _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p9r2 : s9.regs 2 = s8.regs 2 + s8.regs 6 := by
    rw [hs9, regs_addReg _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; rfl
  have p9c : s9.c = (addWithCarry (s8.regs 2) (s8.regs 6) false).2.1 := by
    rw [hs9, c_addReg]; rfl
  have p9m : s9.mem = s8.mem := by rw [hs9, mem_addReg]
  -- s10: r3 = r3 + r0 + C
  have p10o : ∀ r : Reg, r ≠ 3 → r ≠ 15 → s10.regs r = s9.regs r := by
    intro r h h15; rw [hs10, regs_adcs _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p10r3 : s10.regs 3 = (addWithCarry (s9.regs 3) (s9.regs 0) s9.c).1 := by
    rw [hs10, regs_adcs _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; rfl
  have p10m : s10.mem = s9.mem := by rw [hs10, mem_adcs]
  -- s11, s12: r1 = 40 + r4
  have p11o : ∀ r : Reg, r ≠ 1 → r ≠ 15 → s11.regs r = s10.regs r := by
    intro r h h15; rw [hs11, regs_movImm _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p11r1 : s11.regs 1 = 40#32 := by
    rw [hs11, regs_movImm _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; rfl
  have p11m : s11.mem = s10.mem := by rw [hs11, mem_movImm]
  have p12o : ∀ r : Reg, r ≠ 1 → r ≠ 15 → s12.regs r = s11.regs r := by
    intro r h h15; rw [hs12, regs_addReg _ _ _ _ _ h15]; exact if_neg (fun h' => h h')
  have p12r1 : s12.regs 1 = s11.regs 1 + s11.regs 4 := by
    rw [hs12, regs_addReg _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; rfl
  have p12m : s12.mem = s11.mem := by rw [hs12, mem_addReg]
  -- value chain
  have r6_8 : s8.regs 6 = BitVec.ofNat 32 st.pending.length := by
    rw [p8o 6 (by decide) (by decide), p7o 6 (by decide) (by decide), p6o 6 (by decide) (by decide), p5r6]
  have r2_8 : s8.regs 2 = BitVec.ofNat 32 st.count := by
    rw [p8o 2 (by decide) (by decide), p7o 2 (by decide) (by decide), p6r2]
  have r3_9 : s9.regs 3 = BitVec.ofNat 32 (st.count / 2 ^ 32) := by
    rw [p9o 3 (by decide) (by decide), p8o 3 (by decide) (by decide), p7r3]
  have r0_9 : s9.regs 0 = 0#32 := by rw [p9o 0 (by decide) (by decide), p8r0]
  have r4_11 : s11.regs 4 = s.regs 0 := by
    rw [p11o 4 (by decide) (by decide), p10o 4 (by decide) (by decide), p9o 4 (by decide) (by decide),
      p8o 4 (by decide) (by decide), p7o 4 (by decide) (by decide), p6o 4 (by decide) (by decide),
      p5o 4 (by decide) (by decide), r4_4]
  have hcnt := e.cnt
  have hlt : st.count < 2 ^ 64 := e.ctx.cnt
  have hup : st.pending.length ≤ 64 := e.ctx.plen
  have lo_nat : (BitVec.ofNat 32 st.count).toNat = st.count % 2 ^ 32 := BitVec.toNat_ofNat _ _
  have hi_nat : (BitVec.ofNat 32 (st.count / 2 ^ 32)).toNat = st.count / 2 ^ 32 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have u_nat : (BitVec.ofNat 32 st.pending.length).toNat = st.pending.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hT : (s12.regs 2).toNat + 2 ^ 32 * (s12.regs 3).toNat = st.count + st.pending.length := by
    have h2 : s12.regs 2 = s9.regs 2 := by
      rw [p12o 2 (by decide) (by decide), p11o 2 (by decide) (by decide), p10o 2 (by decide) (by decide)]
    have h3 : s12.regs 3 = s10.regs 3 := by
      rw [p12o 3 (by decide) (by decide), p11o 3 (by decide) (by decide)]
    rw [h2, h3, p10r3, r3_9, r0_9, p9r2, r2_8, r6_8, p9c, r2_8, r6_8]
    have := add64 (BitVec.ofNat 32 st.count) (BitVec.ofNat 32 (st.count / 2 ^ 32))
      (BitVec.ofNat 32 st.pending.length) (by rw [lo_nat, hi_nat, u_nat]; omega)
    rw [this, lo_nat, hi_nat, u_nat]; omega
  have hq : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → s12.regs r = s.regs r := by
    intro r h7 h13 h15
    have n15 : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    have n13 : r ≠ 13 := fun h => h13 (by rw [h]; rfl)
    have n0 : r ≠ 0 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n1 : r ≠ 1 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n2 : r ≠ 2 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n3 : r ≠ 3 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n4 : r ≠ 4 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n5 : r ≠ 5 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    have n6 : r ≠ 6 := fun h => by rw [h] at h7; exact absurd h7 (by decide)
    rw [p12o r n1 n15, p11o r n1 n15, p10o r n3 n15, p9o r n2 n15, p8o r n0 n15, p7o r n3 n15,
      p6o r n2 n15, p5o r n6 n15, p4o r n5 n15, p3o r n4 n15, p2o r n13 n15, p1o r n13 n15]
  have hpc : (execAll fPro s).pc = base + BitVec.ofNat 32 oPadB := by
    rw [execAll_pc _ _ (by decide), e.pc, ofNat_add_assoc]; rfl
  rw [hx] at hpc
  rw [hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hT, hq, ?_, ?_⟩
  · rw [p12o 13 (by decide) (by decide), p11o 13 (by decide) (by decide), p10o 13 (by decide) (by decide),
      p9o 13 (by decide) (by decide), p8o 13 (by decide) (by decide), p7o 13 (by decide) (by decide),
      p6o 13 (by decide) (by decide), p5o 13 (by decide) (by decide), p4o 13 (by decide) (by decide),
      p3o 13 (by decide) (by decide), p2r13]
  · rw [p12o 4 (by decide) (by decide), p11o 4 (by decide) (by decide), p10o 4 (by decide) (by decide),
      p9o 4 (by decide) (by decide), p8o 4 (by decide) (by decide), p7o 4 (by decide) (by decide),
      p6o 4 (by decide) (by decide), p5o 4 (by decide) (by decide), r4_4]
  · rw [p12o 5 (by decide) (by decide), p11o 5 (by decide) (by decide), p10o 5 (by decide) (by decide),
      p9o 5 (by decide) (by decide), p8o 5 (by decide) (by decide), p7o 5 (by decide) (by decide),
      p6o 5 (by decide) (by decide), p5o 5 (by decide) (by decide), p4r5, r1_3]
  · rw [p12o 6 (by decide) (by decide), p11o 6 (by decide) (by decide), p10o 6 (by decide) (by decide),
      p9o 6 (by decide) (by decide), r6_8]
  · rw [p12o 0 (by decide) (by decide), p11o 0 (by decide) (by decide), p10o 0 (by decide) (by decide), r0_9]
  · rw [p12r1, r4_11, p11r1]; bv_omega
  · rw [p12m, p11m, p10m, p9m, p8m, p7m, p6m, p5m, m4]
  · exact hpc

end M0Crypto.Release.Blake2sFinal
