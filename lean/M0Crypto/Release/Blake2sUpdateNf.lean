import M0Crypto.Release.Blake2sFinalReach
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.ReachPc
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # The compress call of `update`: `NONFINAL_BLOCK`

`bl_compress` is the generic `bl` to `m0c_blake2s_compress` (its pre-state and result stated on the
state just before the `bl`); `nf_reach` is the whole macro, shared by the flush and the direct
block sites. -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2s (regs_addReg regs_movImm mem_addReg mem_movImm regs_strSp mem_strSp wd arr8 arr16)
open M0Crypto.Release.Blake2sFinal (add64 disj_sub code_w32 arr8_congr arr16_congr rd_w32_far)
open M0Crypto.Release.Blake2sCompress (Entry Post WrOf fpOf Mw compress_reach compress_reachS compress_reachSR)
open M0Crypto.Release.Blake2sInit (disj_ne w32_other)
open M0Crypto.Release.Blake2sCode (SiteAt)
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sCompress (RR)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem c_addImm8 (s : State) (d : LowReg) (i : BitVec 8) :
    ((Instr.addImm8 d i).next s).c = (addWithCarry (s.reg d) (i.setWidth 32) false).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg]

/-- Straight-line effects: unfold `execAll` of a named block and rewrite with the per-instruction
register and memory lemmas. -/
syntax "eff " ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eff $b:ident) => `(tactic| simp (config := {decide := true}) only [$b:ident, execAll,
      regs_ldr, mem_ldr, regs_movImm, mem_movImm, regs_addImm8, mem_addImm8, c_addImm8, regs_adcs, mem_adcs,
      regs_strSp, mem_strSp, regs_str, mem_str, regs_addImm3, mem_addImm3, ite_true, ite_false, State.reg,
      State.sp])
  | `(tactic| eff $b:ident [$hs,*]) => `(tactic| simp (config := {decide := true}) only [$b:ident, execAll,
      regs_ldr, mem_ldr, regs_movImm, mem_movImm, regs_addImm8, mem_addImm8, c_addImm8, regs_adcs, mem_adcs,
      regs_strSp, mem_strSp, regs_str, mem_str, regs_addImm3, mem_addImm3, ite_true, ite_false, State.reg,
      State.sp, $hs,*])

/-- What the call to compress leaves, stated on the state `u` just before the `bl`. -/
structure BlPost (base : Word) (off : Nat) (u v : State) : Prop where
  pc : v.pc = base + BitVec.ofNat 32 (off + 4)
  sp : v.regs 13 = u.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → v.regs r = u.regs r
  hout : ∀ i < 8, read32 v.mem (u.regs 0 + BitVec.ofNat 32 (4 * i)) =
    (M0Crypto.Spec.Blake2s.compress (arr8 (wd u.mem (u.regs 0))) (arr16 (wd u.mem (u.regs 1)))
      ((u.regs 2).toNat + 2 ^ 32 * (u.regs 3).toNat) (decide (read32 u.mem (u.regs 13) ≠ 0#32)))[i]!
  mem : ∀ y, (∀ o < COMPRESS_FRAME, y ≠ u.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) →
    (∀ o < 32, y ≠ u.regs 0 + BitVec.ofNat 32 o) → v.mem y = u.mem y

/-- The writes of a call to compress, seen from the state `u` before the `bl`: the frame and the
chain window, and only the chain window at the compression's store sites. -/
def CWu (base : Word) (u : State) (pc y : Word) : Prop :=
  ((∃ o < COMPRESS_FRAME, y = u.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) ∨ (∃ o < 32, y = u.regs 0 + BitVec.ofNat 32 o)) ∧
  (SiteAt base pc → ∃ o < 32, y = u.regs 0 + BitVec.ofNat 32 o)

theorem bl_compressS {base : Word} {W : Word → Word → Prop} {R : Word → Prop} {u : State} (off : Nat)
    (hb4 : base.toNat % 4 = 0) (hpc : u.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hbl : instrAt B off = some (.bl (blImm off cmpStart))) (hsz : off + 4 < Artifacts.Release.size)
    (ht : Release.blTarget off (blImm off cmpStart) = BitVec.ofNat 32 cmpStart)
    (hcode : CodeAt u.mem base B) (hsp4 : (u.regs 13).toNat % 4 = 0) (hspLo : COMPRESS_FRAME ≤ (u.regs 13).toNat)
    (h04 : (u.regs 0).toNat % 4 = 0) (h14 : (u.regs 1).toNat % 4 = 0)
    (codeF : Disj base Artifacts.Release.size (u.regs 13 - COMPRESS_FRAME_W) COMPRESS_FRAME)
    (codeH : Disj base Artifacts.Release.size (u.regs 0) 32)
    (hpF : Disj (u.regs 0) 32 (u.regs 13 - COMPRESS_FRAME_W) COMPRESS_FRAME)
    (blkF : Disj (u.regs 1) 64 (u.regs 13 - COMPRESS_FRAME_W) COMPRESS_FRAME)
    (hf0 : read32 u.mem (u.regs 13) = 0#32 ∨ read32 u.mem (u.regs 13) = 0xFFFFFFFF#32)
    (hW : ∀ pc y, CWu base u pc y → W pc y) (hRc : ∀ y, RR u y → R y) :
    ReachS base (PNR ldAll W R) u (BlPost base off u) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  apply ReachS.blPcNR hb2 off cmpStart _ hpc ho hbl (by omega) ht
  obtain ⟨sc, hsc⟩ : ∃ x, x = (u.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 cmpStart) := ⟨_, rfl⟩
  rw [← hsc]
  have sr : ∀ r : Reg, r ≠ 14 → r.val ≠ 15 → sc.regs r = u.regs r := by
    intro r h14 h15
    rw [hsc, sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl), sr_ne _ _ _ _ h14]
  have scm : sc.mem = u.mem := by rw [hsc]; rfl
  have scpc : sc.pc = base + BitVec.ofNat 32 cmpStart := by rw [hsc, sr_pc]
  have s13 : sc.regs 13 = u.regs 13 := sr 13 (by decide) (by decide)
  have s0 : sc.regs 0 = u.regs 0 := sr 0 (by decide) (by decide)
  have s1 : sc.regs 1 = u.regs 1 := sr 1 (by decide) (by decide)
  have fp : fpOf sc = u.regs 13 - COMPRESS_FRAME_W := by unfold fpOf; rw [s13]
  have h14' : sc.regs 14 = (base + BitVec.ofNat 32 (off + 4)) ||| 1#32 := by
    rw [hsc, sr_ne _ _ _ _ (by decide)]; simp [State.setReg]
  have e : Entry base sc := by
    refine ⟨hb4, scpc, by rw [scm]; exact hcode, by rw [s13]; exact hsp4, by rw [s13]; omega,
      by rw [s0]; exact h04, by rw [s1]; exact h14, by rw [h14']; exact M0Crypto.Release.lr_odd _,
      by rw [fp]; exact codeF, by rw [s0]; exact codeH, by rw [s0, fp]; exact hpF,
      by rw [s1, fp]; exact blkF, by rw [scm, s13]; exact hf0⟩
  have hq : ∀ v, Post sc v → BlPost base off u v := by
    intro v hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hbs := codeH.1
      rw [hp.pc, h14', M0Crypto.Release.lr_mask]
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    · rw [hp.sp, s13]
    · intro r h4 h11
      have hn14 : r ≠ 14 := fun h => by rw [h] at h11; exact absurd h11 (by decide)
      have hn15 : r.val ≠ 15 := by omega
      have hcases : ∀ q : Reg, 4 ≤ q.val → q.val ≤ 11 → q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by
        decide
      have : v.regs r = sc.regs r := by
        rcases hcases r h4 h11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hp.r4
        · exact hp.r5
        · exact hp.r6
        · exact hp.r7
        · exact hp.r8
        · exact hp.r9
        · exact hp.r10
        · exact hp.r11
      rw [this, sr r hn14 hn15]
    · intro i hi
      have hh := hp.hout i hi
      rw [s0] at hh
      have hM : Mw sc = wd u.mem (u.regs 1) := by unfold Mw; rw [s1, scm]
      rw [hh, hM, scm, s13, sr 2 (by decide) (by decide), sr 3 (by decide) (by decide)]
    · intro y hy1 hy2
      have := hp.mem y (by intro o ho; rw [fp]; exact hy1 o (by omega))
        (by intro o ho; rw [s0]; exact hy2 o ho)
      rw [this, scm]
  refine (compress_reachSR e (BlPost base off u) hq).mono
    (fun _ ev hp => ⟨⟨fun y hy => hW _ _ ?_, hp.1.2⟩, fun hld y hy => hRc y ?_⟩) (fun _ h => h)
  · obtain ⟨hw, hs⟩ := hp.1.1 y hy
    refine ⟨?_, fun hsite => ?_⟩
    · rcases hw with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact Or.inl ⟨o, ho, by rw [fp]⟩
      · exact Or.inr ⟨o, ho, by rw [s0]⟩
    · obtain ⟨o, ho, rfl⟩ := (hs hsite).1
      exact ⟨o, ho, by rw [s0]⟩
  · rcases hp.2 hld y hy with ⟨o, ho, h⟩ | ⟨o, ho, h⟩
    · exact Or.inl ⟨o, ho, by rw [h, s1]⟩
    · exact Or.inr ⟨o, ho, by rw [h, s0]⟩

/-- The body of `NONFINAL_BLOCK` before the `bl`: `count += 64`, `f0 = 0`, `r0 = c`. -/
theorem nf_eff (t : State) :
    (execAll nfBody t).regs 0 = t.regs 4 ∧ (execAll nfBody t).regs 1 = t.regs 1 ∧
    (execAll nfBody t).regs 2 = read32 t.mem (t.regs 4 + 32#32) + 64#32 ∧
    (execAll nfBody t).regs 3 = (addWithCarry (read32 t.mem (t.regs 4 + 36#32)) 0#32
      (addWithCarry (read32 t.mem (t.regs 4 + 32#32)) 64#32 false).2.1).1 ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → (execAll nfBody t).regs r = t.regs r) ∧
    (execAll nfBody t).mem = write32 (write32 (write32 t.mem (t.regs 4 + 32#32)
      (read32 t.mem (t.regs 4 + 32#32) + 64#32)) (t.regs 4 + 36#32)
      (addWithCarry (read32 t.mem (t.regs 4 + 36#32)) 0#32
        (addWithCarry (read32 t.mem (t.regs 4 + 32#32)) 64#32 false).2.1).1) (t.regs 13) 0#32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · eff nfBody; try simp [LowReg.toReg]
    try rfl
  · eff nfBody; try simp [LowReg.toReg]
    try rfl
  · eff nfBody; try simp [LowReg.toReg]
    try rfl
  · eff nfBody; try simp [LowReg.toReg]
    try rfl
  · intro r h4 h15
    have h0 : r ≠ 0 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have h1 : r ≠ 1 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have h2 : r ≠ 2 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have h3 : r ≠ 3 := fun h => by rw [h] at h4; exact absurd h4 (by decide)
    have h15' : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    have n0 : (r = LowReg.toReg 0) = False := eq_false h0
    have n2 : (r = LowReg.toReg 2) = False := eq_false h2
    have n3 : (r = LowReg.toReg 3) = False := eq_false h3
    eff nfBody [regs_ldr _ _ _ _ r h15', regs_movImm _ _ _ r h15', regs_addImm8 _ _ _ r h15',
      regs_adcs _ _ _ r h15', regs_strSp _ _ _ r h15', regs_str _ _ _ _ r h15', regs_addImm3 _ _ _ _ r h15',
      n0, n2, n3]
  · eff nfBody; try simp [LowReg.toReg]
    try rfl

theorem cw {base f a : Word} {n d len : Nat} (h : Disj base Artifacts.Release.size f n)
    (hd : a = f + BitVec.ofNat 32 d) (hdl : d + len ≤ n) :
    ∀ i < B.length, ∀ k < len, base + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 k := by
  intro i hi k hk
  rw [hd, ofNat_add_assoc]
  exact disj_ne h (by rwa [B_len] at hi) (by omega)

/-- What `NONFINAL_BLOCK` leaves, stated on the state `t` before the block. -/
structure NfPost (base : Word) (off : Nat) (t v : State) : Prop where
  pc : v.pc = base + BitVec.ofNat 32 (off + 4)
  sp : v.regs 13 = t.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → v.regs r = t.regs r
  hout : ∀ i < 8, read32 v.mem (t.regs 4 + BitVec.ofNat 32 (4 * i)) =
    (M0Crypto.Spec.Blake2s.compress (arr8 (wd t.mem (t.regs 4))) (arr16 (wd t.mem (t.regs 1)))
      ((read32 t.mem (t.regs 4 + 32#32)).toNat + 2 ^ 32 * (read32 t.mem (t.regs 4 + 36#32)).toNat + 64)
      false)[i]!
  tot : (read32 v.mem (t.regs 4 + 32#32)).toNat + 2 ^ 32 * (read32 v.mem (t.regs 4 + 36#32)).toNat =
    (read32 t.mem (t.regs 4 + 32#32)).toNat + 2 ^ 32 * (read32 t.mem (t.regs 4 + 36#32)).toNat + 64
  mem : ∀ y, (∀ o < STREAM_LOCALS, y ≠ t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) →
    (∀ o < 40, y ≠ t.regs 4 + BitVec.ofNat 32 o) → v.mem y = t.mem y

def nfPre : List Instr := nfBody.take 5
def nfSt : List Instr := (nfBody.drop 5).take 2
def nfTl : List Instr := nfBody.drop 7

theorem nf_split : nfBody = nfPre ++ nfSt ++ nfTl := by decide

open M0Crypto.Sym in
theorem nfPre_regs (t : State) :
    (execAll nfPre t).regs 4 = t.regs 4 ∧ (execAll nfPre t).regs 13 = t.regs 13 := by
  constructor
  · rw [execAll_regs_norm _ (by decide)]
    have : norm ((symExec nfPre SState.init).regs 4) = .reg0 4 := by decide +kernel
    rw [this]; rfl
  · rw [execAll_regs_norm _ (by decide)]
    have : norm ((symExec nfPre SState.init).regs 13) = .reg0 13 := by decide +kernel
    rw [this]; rfl

open M0Crypto.Sym in
theorem nfPreSt_regs (t : State) : (execAll nfSt (execAll nfPre t)).regs 13 = t.regs 13 := by
  rw [← execAll_append, execAll_regs_norm _ (by decide)]
  have : norm ((symExec (nfPre ++ nfSt) SState.init).regs 13) = .reg0 13 := by decide +kernel
  rw [this]; rfl

theorem nf_reachS {base : Word} {W : Word → Word → Prop} {R : Word → Prop} {t : State} (o : Nat)
    (hb4 : base.toNat % 4 = 0) (hpc : t.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0)
    (hseq : seqAt B o nfBody = true)
    (hbl : instrAt B (o + seqSize nfBody) = some (.bl (blImm (o + seqSize nfBody) cmpStart)))
    (hsz : o + seqSize nfBody + 4 < Artifacts.Release.size)
    (ht : Release.blTarget (o + seqSize nfBody) (blImm (o + seqSize nfBody) cmpStart) = BitVec.ofNat 32 cmpStart)
    (hcode : CodeAt t.mem base B) (hsp4 : (t.regs 13).toNat % 4 = 0) (hspLo : COMPRESS_FRAME ≤ (t.regs 13).toNat)
    (hc4 : (t.regs 4).toNat % 4 = 0) (hblk4 : (t.regs 1).toNat % 4 = 0)
    (codeC : Disj base Artifacts.Release.size (t.regs 4) 40)
    (codeF : Disj base Artifacts.Release.size (t.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME)
    (cF : Disj (t.regs 4) 40 (t.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME)
    (blkF : Disj (t.regs 1) 64 (t.regs 13 - COMPRESS_FRAME_W) STREAM_FRAME)
    (blkC : Disj (t.regs 1) 64 (t.regs 4 + 32#32) 8)
    (hcnt : (read32 t.mem (t.regs 4 + 32#32)).toNat + 2 ^ 32 * (read32 t.mem (t.regs 4 + 36#32)).toNat + 64 < 2 ^ 64)
    (hWst : ∀ k < 8, ∀ j < seqSize nfSt,
      W (base + BitVec.ofNat 32 (o + seqSize nfPre + j)) (t.regs 4 + 32#32 + BitVec.ofNat 32 k))
    (hWtl : ∀ k < 4, ∀ j < seqSize nfTl,
      W (base + BitVec.ofNat 32 (o + seqSize nfPre + seqSize nfSt + j)) (t.regs 13 + 0#32 + BitVec.ofNat 32 k))
    (hWc : ∀ pc y, (((∃ i < COMPRESS_FRAME, y = t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 i) ∨
        (∃ i < 32, y = t.regs 4 + BitVec.ofNat 32 i)) ∧
        (SiteAt base pc → ∃ i < 32, y = t.regs 4 + BitVec.ofNat 32 i)) → W pc y)
    (hRa : ∀ k < 8, R (t.regs 4 + 32#32 + BitVec.ofNat 32 k))
    (hRb : ∀ k < 64, R (t.regs 1 + BitVec.ofNat 32 k)) (hRh : ∀ k < 32, R (t.regs 4 + BitVec.ofNat 32 k)) :
    ReachS base (PNR ldAll W R) t (NfPost base (o + seqSize nfBody) t) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have hsn := (t.regs 13).isLt
  have hseq' := hseq
  rw [nf_split, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true, seqSize_append] at hseq'
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hseq'
  obtain ⟨p4, p13⟩ := nfPre_regs t
  have hs1pc : (execAll nfPre t).pc = base + BitVec.ofNat 32 (o + seqSize nfPre) := by
    rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
  have hs2pc : (execAll nfSt (execAll nfPre t)).pc =
      base + BitVec.ofNat 32 (o + seqSize nfPre + seqSize nfSt) := by
    rw [execAll_pc _ _ (by decide), hs1pc, ofNat_add_assoc]
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [] [((4 : Reg), (32#32 : Word), 8)] nfPre o hpc ho hq1 (by decide) ?_ (by simp) ?_
    (by decide +kernel) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp; exact hc4
  · intro p hp k hk
    simp only [List.mem_singleton] at hp; subst hp; exact hRa k hk
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [((4 : Reg), (32#32 : Word), 8)] [] nfSt
    (o + seqSize nfPre) hs1pc (by have : seqSize nfPre % 2 = 0 := by decide
                                  omega) hq2 (by decide) ?_ ?_ (by simp)
    (by decide +kernel) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp; rw [p4]; exact hc4
  · intro p hp k hk j hj
    simp only [List.mem_singleton] at hp; subst hp
    rw [p4]
    exact hWst k hk j hj
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 : Word), 4)] [] nfTl
    (o + seqSize nfPre + seqSize nfSt) hs2pc (by have : seqSize nfPre % 2 = 0 := by decide
                                                 have : seqSize nfSt % 2 = 0 := by decide
                                                 omega) (by rw [Nat.add_assoc, ← seqSize_append]; exact hq3) (by decide) ?_ ?_ (by simp)
    (by decide +kernel) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp; rw [nfPreSt_regs]; exact hsp4
  · intro p hp k hk j hj
    simp only [List.mem_singleton] at hp; subst hp
    rw [nfPreSt_regs]
    exact hWtl k hk j hj
  have hE : execAll nfTl (execAll nfSt (execAll nfPre t)) = execAll nfBody t := by
    rw [nf_split, execAll_append, execAll_append]
  rw [hE]
  obtain ⟨e0, e1, e2, e3, eo, em⟩ := nf_eff t
  obtain ⟨u, hu⟩ : ∃ x, x = execAll nfBody t := ⟨_, rfl⟩
  rw [← hu] at e0 e1 e2 e3 eo em ⊢
  have hup : u.pc = base + BitVec.ofNat 32 (o + seqSize nfBody) := by
    rw [hu, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; try rfl
  have u13 : u.regs 13 = t.regs 13 := eo 13 (by decide) (by decide)
  have u4 : u.regs 4 = t.regs 4 := eo 4 (by decide) (by decide)
  obtain ⟨c1, c2, c3⟩ := cF
  obtain ⟨k1, k2, k3⟩ := codeF
  have hf0 : read32 u.mem (u.regs 13) = 0#32 := by
    rw [em, u13]; exact M0Crypto.Armv6M.read32_write32_same _ _ _
  have hcodeU : CodeAt u.mem base B := by
    rw [em]
    refine code_w32 (code_w32 (code_w32 hcode _ _ (cw codeC (d := 32) (len := 4) rfl (by omega))) _ _
      (cw codeC (d := 36) (len := 4) (by bv_omega) (by omega))) _ _
      (cw (f := t.regs 13 - COMPRESS_FRAME_W) (d := COMPRESS_FRAME) (len := 4) ⟨k1, k2, k3⟩ (by bv_omega) (by omega))
  have hbl2 : (o + seqSize nfBody) % 2 = 0 := by
    have : seqSize nfBody % 2 = 0 := by decide
    omega
  have hcodeF : Disj base Artifacts.Release.size (u.regs 13 - COMPRESS_FRAME_W) COMPRESS_FRAME := by
    rw [u13]; exact disj_sub ⟨k1, k2, k3⟩ (Nat.le_refl _) (by omega)
  refine ReachS.bind (ReachS.monoQ (bl_compressS (W := W) (R := R) (o + seqSize nfBody) hb4 hup hbl2 hbl hsz ht hcodeU
    (by rw [u13]; exact hsp4) (by rw [u13]; exact hspLo) (by rw [e0]; exact hc4) (by rw [e1]; exact hblk4)
    hcodeF (by rw [e0]; exact disj_sub codeC (Nat.le_refl _) (by omega))
    (by rw [e0, u13]; exact disj_sub ⟨c1, c2, c3⟩ (by omega) (by omega))
    (by rw [e1, u13]; exact disj_sub blkF (Nat.le_refl _) (by omega))
    (Or.inl hf0) (fun pc y h => hWc pc y (by simpa [CWu, u13, e0] using h))
    (by rintro y (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩)
        · rw [e1]; exact hRb o ho
        · rw [e0]; exact hRh o ho)) ?_)
  intro v hv
  obtain ⟨b1, b2, b3⟩ := blkF
  obtain ⟨d1, d2, d3⟩ := blkC
  have hcn := (t.regs 4).isLt
  have hA4 : (t.regs 4 + 32#32).toNat = (t.regs 4).toNat + 32 := toNat_add_ofNat _ 32 (by omega)
  have hB4 : (t.regs 4 + 36#32).toNat = (t.regs 4).toNat + 36 := toNat_add_ofNat _ 36 (by omega)
  have htp : (t.regs 13 - COMPRESS_FRAME_W).toNat = (t.regs 13).toNat - COMPRESS_FRAME := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h64 : (64#32).toNat = 64 := rfl
  have hT := add64 (read32 t.mem (t.regs 4 + 32#32)) (read32 t.mem (t.regs 4 + 36#32)) 64#32
    (by rw [h64]; exact hcnt)
  rw [h64] at hT
  have wdw : ∀ (a : Word) (L : Nat), a.toNat + L ≤ 2 ^ 32 →
      (a.toNat + L ≤ (t.regs 4).toNat + 32 ∨ (t.regs 4).toNat + 40 ≤ a.toNat) →
      (a.toNat + L ≤ (t.regs 13).toNat - COMPRESS_FRAME ∨ (t.regs 13).toNat + 24 ≤ a.toNat) →
      ∀ j, 4 * j + 4 ≤ L → wd u.mem a j = wd t.mem a j := by
    intro a L haL hA hS j hj
    unfold wd
    have hx : (a + BitVec.ofNat 32 (4 * j)).toNat = a.toNat + 4 * j := toNat_add_ofNat _ _ (by omega)
    rw [em]
    rw [rd_w32_far, rd_w32_far, rd_w32_far] <;> omega
  have memVT : ∀ y, (∀ o < STREAM_LOCALS, y ≠ t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 o) →
      (∀ o < 40, y ≠ t.regs 4 + BitVec.ofNat 32 o) → u.mem y = t.mem y := by
    intro y h1 h2
    rw [em]
    refine (w32_other _ _ _ _ ?_).trans ((w32_other _ _ _ _ ?_).trans (w32_other _ _ _ _ ?_))
    · intro k hk h
      apply h1 (COMPRESS_FRAME + k) (by omega)
      rw [h, ← ofNat_add_assoc]; bv_omega
    · intro k hk h
      apply h2 (36 + k) (by omega)
      rw [h]; bv_omega
    · intro k hk h
      apply h2 (32 + k) (by omega)
      rw [h]; bv_omega
  have rdv : ∀ d, (d = 32 ∨ d = 36) → read32 v.mem (t.regs 4 + BitVec.ofNat 32 d) =
      read32 u.mem (t.regs 4 + BitVec.ofNat 32 d) := by
    intro d hd
    apply read32_congr
    intro k hk
    apply hv.mem
    · intro o ho h
      rw [u13, ofNat_add_assoc] at h
      have := congrArg BitVec.toNat h
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
      omega
    · intro o ho h
      rw [e0, ofNat_add_assoc] at h
      have := congrArg BitVec.toNat h
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
      omega
  have rA : read32 u.mem (t.regs 4 + 32#32) = read32 t.mem (t.regs 4 + 32#32) + 64#32 := by
    rw [em, rd_w32_far, rd_w32_far, M0Crypto.Armv6M.read32_write32_same] <;> omega
  have rB : read32 u.mem (t.regs 4 + 36#32) = (addWithCarry (read32 t.mem (t.regs 4 + 36#32)) 0#32
      (addWithCarry (read32 t.mem (t.regs 4 + 32#32)) 64#32 false).2.1).1 := by
    rw [em, rd_w32_far, M0Crypto.Armv6M.read32_write32_same] <;> omega
  have hT' : (u.regs 2).toNat + 2 ^ 32 * (u.regs 3).toNat =
      (read32 t.mem (t.regs 4 + 32#32)).toNat + 2 ^ 32 * (read32 t.mem (t.regs 4 + 36#32)).toNat + 64 := by
    rw [e2, e3]; exact hT
  refine ReachS.done ⟨hv.pc, by rw [hv.sp, u13], fun r h4 h11 => ?_, fun i hi => ?_, ?_, fun y h1 h2 => ?_⟩
  · rw [hv.keep r h4 h11, eo r h4 (by omega)]
  · have := hv.hout i hi
    rw [e0, e1, hT', hf0] at this
    rw [this]
    have hd : decide ((0#32) ≠ 0#32) = false := by decide
    rw [hd]
    rw [arr8_congr (g := wd t.mem (t.regs 4)) (fun j hj => wdw (t.regs 4) 32 (by omega) (Or.inl (by omega))
        (by omega) j (by omega)),
      arr16_congr (g := wd t.mem (t.regs 1)) (fun j hj => wdw (t.regs 1) 64 (by omega)
        (by omega) (by omega) j (by omega))]
  · rw [rdv 32 (by omega), rdv 36 (by omega), rA, rB]; exact hT
  · rw [hv.mem y (fun o ho => by rw [u13]; exact h1 o (by omega)) (fun o ho => by rw [e0]; exact h2 o (by omega))]
    exact memVT y h1 h2

end M0Crypto.Release.Blake2sUpdate
