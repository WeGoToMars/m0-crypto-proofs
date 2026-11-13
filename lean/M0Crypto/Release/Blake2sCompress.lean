import M0Crypto.Release.Blake2sTail
import M0Crypto.Release.Blake2sCompressSpec
import M0Crypto.Release.SymReach
import M0Crypto.Release.SymReachW
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# `m0c_blake2s_compress`: the function-level contract

`compress_reach` composes the proved segments (prologue `J_pre`, ten rounds `round_effect`,
tail `tailBody_eff`) into one `Reach` judgment; `compress_correct` states what it computes.
-/

namespace M0Crypto.Release.Blake2sCompress

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode
open M0Crypto.Release.Blake2sPro
open M0Crypto.Release.Blake2s
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem MW_eq {sp : Word} {m1 m2 : Mem} (h : MW sp m1 m2) (y : Word)
    (hy : ∀ i, 1 ≤ i → i < 8 → ∀ k, k < 4 → y ≠ slot sp i + BitVec.ofNat 32 k) : m2 y = m1 y := by
  induction h with
  | refl => rfl
  | store i w hi hj _ ih =>
    rw [M0Crypto.Armv6M.write32_other _ _ _ _ (fun q hq => hy i hi hj q hq), ih]

theorem MW_read {sp : Word} {m1 m2 : Mem} (h : MW sp m1 m2) (a : Word)
    (ha : ∀ i, 1 ≤ i → i < 8 → ∀ k, k < 4 → ∀ j, j < 4 → a + BitVec.ofNat 32 j ≠ slot sp i + BitVec.ofNat 32 k) :
    read32 m2 a = read32 m1 a := by
  apply read32_congr
  intro k hk
  exact MW_eq h _ (fun i hi hj q hq => ha i hi hj q hq k hk)


/-! ## Entry contract -/

/-- Frame base of a call entered in state `s`. -/
def fpOf (s : State) : Word := s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME

/-- The instructions at the compression's load sites: the block and chain-word loads. -/
def cLd (i : Instr) : Bool := M0Crypto.Release.Blake2sLd.ldAll i

/-- The bytes the load sites read: the block (64 bytes) and the chain words (32 bytes). -/
def RR (s : State) (y : Word) : Prop :=
  (∃ o < 64, y = s.regs 1 + BitVec.ofNat 32 o) ∨ (∃ o < 32, y = s.regs 0 + BitVec.ofNat 32 o)

/-- The entry state of `m0c_blake2s_compress(h, block, t0, t1, f0)` for an artifact loaded at
`base`: `r0 = h`, `r1 = block`, `r2 = t0`, `r3 = t1`, `f0` at the stack top. -/
structure Entry (base : Word) (s : State) : Prop where
  base4 : base.toNat % 4 = 0
  pc : s.pc = base + BitVec.ofNat 32 fnStart
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : COMPRESS_FRAME ≤ (s.regs 13).toNat
  hp4 : (s.regs 0).toNat % 4 = 0
  blk4 : (s.regs 1).toNat % 4 = 0
  lr : (s.regs 14).getLsbD 0 = true
  codeF : Disj base Artifacts.Release.size (fpOf s) COMPRESS_FRAME
  codeH : Disj base Artifacts.Release.size (s.regs 0) 32
  hpF : Disj (s.regs 0) 32 (fpOf s) COMPRESS_FRAME
  blkF : Disj (s.regs 1) 64 (fpOf s) COMPRESS_FRAME
  f0 : read32 s.mem (s.regs 13) = 0#32 ∨ read32 s.mem (s.regs 13) = 0xFFFFFFFF#32

theorem litA (base : Word) (hb4 : base.toNat % 4 = 0) (d imm T : Nat)
    (hT : (fnStart + d + 4) / 4 * 4 + imm * 4 = T)
    (h : base.toNat + (fnStart + d) + 4 + imm * 4 < 2 ^ 32) :
    ((base + BitVec.ofNat 32 fnStart + BitVec.ofNat 32 d + 4#32) &&& ~~~3#32) +
      BitVec.ofNat 32 (imm * 4) = base + BitVec.ofNat 32 T := by
  rw [BitVec.add_assoc base, ← BitVec.ofNat_add, ← hT]
  exact M0Crypto.Release.Frame.lit_addr base hb4 (fnStart + d) imm h

theorem pool_word (j : Nat) (hj : j < 8) :
    M0Crypto.Release.Frame.codeWord (poolOff + 4 * j) = (M0Crypto.Spec.Blake2s.IV)[j]! := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel


theorem pool_disj {base : Word} {s : State} (e : Entry base s) (j : Nat) (hj : j < 8) :
    Disj (base + BitVec.ofNat 32 (poolOff + 4 * j)) 4 (fpOf s) COMPRESS_FRAME := by
  obtain ⟨h1, h2, h3⟩ := e.codeF
  have hP : poolOff + 32 ≤ Artifacts.Release.size := by decide
  have := toNat_add_ofNat base (poolOff + 4 * j) (by omega)
  exact ⟨by omega, h2, by omega⟩

theorem compress_pre {base : Word} {s : State} (e : Entry base s) :
    ∃ R F, JI (fpOf s) s (execAll preI s) R F ∧
      PreRF s s.regs (read32 s.mem (s.regs 13))
        (base + BitVec.ofNat 32 (poolOff + 4 * 0)) (base + BitVec.ofNat 32 (poolOff + 4 * 1))
        (base + BitVec.ofNat 32 (poolOff + 4 * 2)) (base + BitVec.ofNat 32 (poolOff + 4 * 3))
        (base + BitVec.ofNat 32 (poolOff + 4 * 4)) (base + BitVec.ofNat 32 (poolOff + 4 * 5))
        (base + BitVec.ofNat 32 (poolOff + 4 * 6)) (base + BitVec.ofNat 32 (poolOff + 4 * 7)) R F := by
  obtain ⟨h1, h2, h3⟩ := e.codeF
  have hL : poolOff + 32 ≤ Artifacts.Release.size ∧ fnStart + 112 < poolOff + 32 := by decide
  have hs : RA s s.regs := fun _ _ => rfl
  exact J_pre s s.regs _ hs rfl _ e.pc _ _ _ _ _ _ _ _
    (litA base e.base4 72 2 _ (by decide) (by omega)) (litA base e.base4 74 3 _ (by decide) (by omega))
    (litA base e.base4 76 3 _ (by decide) (by omega)) (litA base e.base4 78 4 _ (by decide) (by omega))
    (litA base e.base4 16 20 _ (by decide) (by omega)) (litA base e.base4 22 20 _ (by decide) (by omega))
    (litA base e.base4 30 19 _ (by decide) (by omega)) (litA base e.base4 36 18 _ (by decide) (by omega))
    (pool_disj e 0 (by omega)) (pool_disj e 1 (by omega)) (pool_disj e 2 (by omega))
    (pool_disj e 3 (by omega)) (pool_disj e 4 (by omega)) (pool_disj e 5 (by omega))
    (pool_disj e 6 (by omega)) (pool_disj e 7 (by omega)) e.blkF e.hpF


open M0Crypto.Release.Blake2s (wd v0 hv mv)

/-- The initial working vector of a call entered in `s`. -/
def V0 (s : State) : Nat → Word :=
  v0 (wd s.mem (s.regs 0)) (s.regs 2) (s.regs 3) (read32 s.mem (s.regs 13))

/-- The message words of a call entered in `s`. -/
def Mw (s : State) : Nat → Word := wd s.mem (s.regs 1)

theorem pool_read {base : Word} {s : State} (e : Entry base s) (j : Nat) (hj : j < 8) :
    read32 s.mem (base + BitVec.ofNat 32 (poolOff + 4 * j)) = (M0Crypto.Spec.Blake2s.IV)[j]! := by
  have hP : poolOff + 32 ≤ Artifacts.Release.size := by decide
  rw [M0Crypto.Release.Frame.read32_code e.code _ (by omega), pool_word j hj]

theorem pre_inv {base : Word} {s : State} (e : Entry base s) :
    ∃ F, Inv (execAll preI s) (fpOf s) (V0 s) (Mw s) none ∧ FS (fpOf s) F (execAll preI s).mem ∧
      F HPTR_WORDS = some (s.regs 0) ∧ F SLOTW_0 = some (s.regs 8) ∧ F SLOTW_1 = some (s.regs 9) ∧
      F SLOTW_2 = some (s.regs 10) ∧ F SLOTW_3 = some (s.regs 11) ∧ F SLOTW_4 = some (s.regs 4) ∧
      F SLOTW_5 = some (s.regs 5) ∧ F SLOTW_6 = some (s.regs 6) ∧ F SLOTW_7 = some (s.regs 7) ∧
      F SLOTW_8 = some (s.regs 14) ∧ Out (fpOf s) s.mem (execAll preI s).mem := by
  obtain ⟨R, F, ⟨hRA, hFS, hOut⟩, r13, r8, r2, r5, r6, r7, r9, r10, r11, r12, f1, f2, f24, f34,
    f25, f26, f27, f28, f29, f30, f31, f32, f33⟩ := compress_pre e
  have p0 := pool_read e 0 (by omega); have p1 := pool_read e 1 (by omega)
  have p2 := pool_read e 2 (by omega); have p3 := pool_read e 3 (by omega)
  have p4 := pool_read e 4 (by omega); have p5 := pool_read e 5 (by omega)
  have p6 := pool_read e 6 (by omega); have p7 := pool_read e 7 (by omega)
  refine ⟨F, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hFS, f24, f25, f26, f27, f28, f29, f30,
    f31, f32, f33, hOut⟩
  · exact (hRA 13 (by decide)).trans r13
  · rw [hRA 8 (by decide), r8]; simp [V0, v0, wd]
  · intro i hi1 hi2 _
    have := hFS i (by omega) _ (f1 i hi1 hi2)
    rw [this]; simp [V0, v0, wd, hi2]
  · intro i h; cases h
  · rw [hRA 2 (by decide), r2, p0]; rfl
  · rw [hRA 5 (by decide), r5, p1]; rfl
  · rw [hRA 6 (by decide), r6, p2]; rfl
  · rw [hRA 7 (by decide), r7, p3]; rfl
  · rw [hRA 9 (by decide), r9, p4]; rfl
  · rw [hRA 10 (by decide), r10, p5]; rfl
  · rw [hRA 11 (by decide), r11, p6]; rfl
  · rw [hRA 12 (by decide), r12, p7]; rfl
  · intro i hi
    have := hFS (8 + i) (by omega) _ (f2 i hi)
    rw [this]; rfl


/-! ## Ten rounds -/

theorem round_facts : ∀ n, n < 10 → (roundInstrs n).all Instr.falls = true ∧
    M0Crypto.Sym.alignChk [((13 : Reg), 4)] (roundInstrs n) = true ∧
    M0Crypto.Sym.writeChk [((13 : Reg), (4#32 : Word), 28)] (roundInstrs n) = true ∧
    roundOff n % 2 = 0 ∧ roundOff (n + 1) = roundOff n + seqSize (roundInstrs n) := by
  decide +kernel

theorem round_at (n : Nat) (hn : n < 10) : seqAt B (roundOff n) (roundInstrs n) = true := by
  have := checkBlocks_get allRounds B roundsOff rounds_check n (by simp [allRounds]; omega)
  simpa [roundOff, allRounds] using this

/-- Every round lies before the tail. -/
theorem round_end : ∀ n, n < 10 → roundOff n + seqSize (roundInstrs n) ≤ tailOff := by
  decide +kernel

theorem rounds_rd : ∀ n, n < 10 → M0Crypto.Sym.readChk cLd [] (roundInstrs n) = true := by
  decide +kernel

theorem rounds_noldr : ∀ n, n < 10 → NoLdrBlock (roundInstrs n) = true := by decide +kernel

theorem rounds_reach {base : Word} {W : Word → Word → Prop} {R : Word → Prop} (hb2 : base.toNat % 2 = 0) (sp : Word)
    (hsp4 : sp.toNat % 4 = 0)
    (hWr : ∀ o < 28, ∀ j < tailOff, W (base + BitVec.ofNat 32 j) (sp + 4#32 + BitVec.ofNat 32 o))
    (V M : Nat → Word) :
    ∀ k n, n + k = 10 → ∀ s : State,
      Inv s sp (Vr V M n) M (if (n == 0) = true then none else some 2) →
      s.pc = base + BitVec.ofNat 32 (roundOff n) → ∀ Q : State → Prop,
      (∀ t : State, Inv t sp (Vr V M 10) M (some 2) → MW sp s.mem t.mem →
        t.pc = base + BitVec.ofNat 32 (roundOff 10) → ReachS base (PNR cLd W R) t Q) →
      ReachS base (PNR cLd W R) s Q := by
  intro k
  induction k with
  | zero =>
    intro n hn s hI hpc Q hQ
    have : n = 10 := by omega
    subst this
    exact hQ s (by simpa using hI) (MW.refl _) hpc
  | succ k ih =>
    intro n hn s hI hpc Q hQ
    have hn10 : n < 10 := by omega
    obtain ⟨hf, ha, hw, ho, hoff⟩ := round_facts n hn10
    have hsch : ∀ i, i < 16 → sg n i < 16 := by
      have : ∀ n : Fin 10, ∀ i : Fin 16, sg n i < 16 := by decide +kernel
      intro i hi; exact this ⟨n, hn10⟩ ⟨i, hi⟩
    obtain ⟨I', W', R'⟩ := round_effect s sp (Vr V M n) M (sg n) (n == 0) hsch hI
    have hend := round_end n hn10
    refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [((13 : Reg), (4#32 : Word), 28)] []
      (roundInstrs n) (roundOff n) hpc ho (round_at n hn10) hf ?_ ?_ (fun p hp => by simp at hp) ha hw ?_
      (rounds_noldr n hn10) (rounds_rd n hn10)
    · intro p hp; rw [List.mem_singleton] at hp; subst hp
      simp only [hI.spR]; exact hsp4
    · intro p hp o ho' j hj; rw [List.mem_singleton] at hp; subst hp
      simp only [hI.spR]; exact hWr o ho' _ (by omega)
    · refine ih (n + 1) (by omega) _ ?_ ?_ Q ?_
      · exact I'
      · rw [execAll_pc _ _ hf, hpc, hoff, BitVec.add_assoc, BitVec.ofNat_add]
      · intro t hT hMW hpc'
        exact hQ t hT (MW_trans W' hMW) hpc'

/-! ## Tail -/

theorem pc_adv (s : State) (is : List Instr) (base : Word) (off : Nat)
    (hf : is.all Instr.falls = true) (h : s.pc = base + BitVec.ofNat 32 off) :
    (execAll is s).pc = base + BitVec.ofNat 32 (off + seqSize is) := by
  rw [execAll_pc _ _ hf, h, BitVec.add_assoc, BitVec.ofNat_add]

open M0Crypto.Release.Blake2sTail

/-- Code offset of the frame clear. -/
def clearOff : Nat := tailOff + seqSize S1 + seqSize S2a + seqSize S2b + seqSize S3a + seqSize S3b

theorem tail_checks :
    (S1.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((13 : Reg), 4)] S1 = true ∧
      M0Crypto.Sym.writeChk [] S1 = true ∧ seqAt B tailOff S1 = true ∧ tailOff % 2 = 0) ∧
    (S2a.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((4 : Reg), 4)] S2a = true ∧
      M0Crypto.Sym.writeChk [] S2a = true ∧ seqAt B (tailOff + seqSize S1) S2a = true ∧
      (tailOff + seqSize S1) % 2 = 0) ∧
    (S2b.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((4 : Reg), 4)] S2b = true ∧
      M0Crypto.Sym.writeChk [((4 : Reg), (0#32 : Word), 16)] S2b = true ∧
      seqAt B (tailOff + seqSize S1 + seqSize S2a) S2b = true ∧
      (tailOff + seqSize S1 + seqSize S2a) % 2 = 0) ∧
    (S3a.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((13 : Reg), 4)] S3a = true ∧
      M0Crypto.Sym.writeChk [] S3a = true ∧
      seqAt B (tailOff + seqSize S1 + seqSize S2a + seqSize S2b) S3a = true ∧
      (tailOff + seqSize S1 + seqSize S2a + seqSize S2b) % 2 = 0) ∧
    (S3b.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((4 : Reg), 4)] S3b = true ∧
      M0Crypto.Sym.writeChk [((4 : Reg), (0#32 : Word), 16)] S3b = true ∧
      seqAt B (tailOff + seqSize S1 + seqSize S2a + seqSize S2b + seqSize S3a) S3b = true ∧
      (tailOff + seqSize S1 + seqSize S2a + seqSize S2b + seqSize S3a) % 2 = 0) ∧
    (S3c.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((13 : Reg), 4)] S3c = true ∧
      M0Crypto.Sym.writeChk [((13 : Reg), (0#32 : Word), LOCALS_BYTES)] S3c = true ∧
      seqAt B clearOff S3c = true ∧ clearOff % 2 = 0) ∧
    (S4.all Instr.falls = true ∧ M0Crypto.Sym.alignChk [((13 : Reg), 4)] S4 = true ∧
      M0Crypto.Sym.writeChk [] S4 = true ∧
      seqAt B (clearOff + seqSize S3c) S4 = true ∧ (clearOff + seqSize S3c) % 2 = 0) ∧
    (instrAt B (clearOff + seqSize S3c + seqSize S4) = some (.pop 0xF0 true) ∧
      (clearOff + seqSize S3c + seqSize S4) % 2 = 0 ∧
      clearOff + seqSize S3c + seqSize S4 + 2 ≤ Artifacts.Release.size ∧
      seqSize S1 + seqSize S2a + seqSize S2b + seqSize S3a + seqSize S3b + seqSize S3c + seqSize S4 =
        seqSize tailBody) := by
  decide +kernel

theorem pop_exec (t : State)
    (hbit : (read32 t.mem (t.regs 13 + 16#32)).getLsbD 0 = true) :
    ∃ s1, (Instr.pop 0xF0 true).exec t = .ok s1 ∧ s1.mem = t.mem ∧ s1.regs 13 = t.regs 13 + 20#32 ∧
      s1.regs 4 = read32 t.mem (t.regs 13) ∧ s1.regs 5 = read32 t.mem (t.regs 13 + 4#32) ∧
      s1.regs 6 = read32 t.mem (t.regs 13 + 8#32) ∧ s1.regs 7 = read32 t.mem (t.regs 13 + 12#32) ∧
      (∀ r : Reg, r.val < 4 ∨ (8 ≤ r.val ∧ r.val ≤ 12) → s1.regs r = t.regs r) ∧
      s1.pc = read32 t.mem (t.regs 13 + 16#32) &&& ~~~1#32 := by
  have hb : bitCount (0xF0#8) = 4 := by decide
  have h1 : (read32 t.mem (t.sp + BitVec.ofNat 32 (4 * bitCount 240))).getLsbD 0 = true := by
    simpa [State.sp, hb] using hbit
  simp only [Instr.exec, if_true, h1]
  refine ⟨_, rfl, ?_⟩
  have hl : listRegs (0xF0#8) = [4, 5, 6, 7] := by decide
  have e8 : t.regs 13 + 4#32 + 4#32 = t.regs 13 + 8#32 := by bv_omega
  have e12 : t.regs 13 + 4#32 + 4#32 + 4#32 = t.regs 13 + 12#32 := by bv_omega
  simp (config := {decide := true}) [hl, hb, loadRegs, State.setReg, State.sp, State.pc, LowReg.toReg,
    Fin.ext_iff, e8, e12]
  have e12' : t.regs 13 + 8#32 + 4#32 = t.regs 13 + 12#32 := by bv_omega
  rw [e12']
  refine ⟨rfl, ?_⟩
  intro r hr
  obtain ⟨rv, hrv⟩ := r
  simp (config := {decide := true}) [Fin.ext_iff] at hr ⊢
  repeat' split
  all_goals first | rfl | (exfalso; omega)

/-- The memory after the feed-forward stores. -/
def tailMem (m : Mem) (V : Nat → Word) (hp : Word) : Mem :=
  storeWords (storeWords m hp
    [read32 m hp ^^^ V 0 ^^^ V 8, read32 m (hp + 4#32) ^^^ V 1 ^^^ V 9,
     read32 m (hp + 8#32) ^^^ V 2 ^^^ V 10, read32 m (hp + 12#32) ^^^ V 3 ^^^ V 11])
    (hp + 16#32)
    [read32 m (hp + 16#32) ^^^ V 4 ^^^ V 12, read32 m (hp + 20#32) ^^^ V 5 ^^^ V 13,
     read32 m (hp + 24#32) ^^^ V 6 ^^^ V 14, read32 m (hp + 28#32) ^^^ V 7 ^^^ V 15]

/-- The memory at return: the feed-forward stores, then the locals cleared. -/
def retMem (m : Mem) (V : Nat → Word) (hp sp : Word) : Mem :=
  storeWords (tailMem m V hp) sp (List.replicate LOCALS_WORDS 0#32)

theorem retMem_read (m : Mem) (V : Nat → Word) (hp sp a : Word) (h : Disj sp LOCALS_BYTES a 4) :
    read32 (retMem m V hp sp) a = read32 (tailMem m V hp) a := by
  unfold retMem
  exact read32_storeWords_ne _ _ _ _ (by simpa using h)

theorem retMem_other (m : Mem) (V : Nat → Word) (hp sp y : Word)
    (hy : ∀ o < LOCALS_BYTES, y ≠ sp + BitVec.ofNat 32 o) : retMem m V hp sp y = tailMem m V hp y := by
  unfold retMem
  apply storeWords_other
  intro i k hi hk e
  simp only [List.length_replicate] at hi
  apply hy (4 * i + k) (by omega)
  rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem retMem_wipe (m : Mem) (V : Nat → Word) (hp sp : Word) (i : Nat) (hi : i < LOCALS_WORDS) :
    read32 (retMem m V hp sp) (slot sp i) = 0#32 := by
  unfold retMem slot
  rw [M0Crypto.Release.Frame.read32_storeWords_same _ sp _ i (by simpa using hi) (by simp)]
  exact List.getElem_replicate ..

theorem tail_reach {base : Word} {W : Word → Word → Prop} {R : Word → Prop} (hb2 : base.toNat % 2 = 0)
    (t0 : State) (V : Nat → Word) (sp hp : Word)
    (h13 : t0.regs 13 = sp) (r0 : t0.regs 0 = V 2) (r2 : t0.regs 2 = V 8) (r5 : t0.regs 5 = V 9)
    (r6 : t0.regs 6 = V 10) (r7 : t0.regs 7 = V 11) (r8 : t0.regs 8 = V 0)
    (r9 : t0.regs 9 = V 12) (r10 : t0.regs 10 = V 13) (r11 : t0.regs 11 = V 14)
    (r12 : t0.regs 12 = V 15)
    (mV : ∀ i, 1 ≤ i → i < 8 → i ≠ 2 → read32 t0.mem (sp + BitVec.ofNat 32 (4 * i)) = V i)
    (hH : read32 t0.mem (sp + BitVec.ofNat 32 HPTR_SLOT) = hp)
    (dj : Disj hp 32 sp COMPRESS_FRAME)
    (hsp4 : sp.toNat % 4 = 0) (hhp4 : hp.toNat % 4 = 0)
    (hWh : ∀ x, tailOff ≤ x → x < tailOff + seqSize tailBody → ∀ o < 32,
      W (base + BitVec.ofNat 32 x) (hp + BitVec.ofNat 32 o))
    (hWf : ∀ j < seqSize S3c, ∀ o < LOCALS_BYTES,
      W (base + BitVec.ofNat 32 (clearOff + j)) (sp + BitVec.ofNat 32 o))
    (hRh : ∀ o < 32, R (hp + BitVec.ofNat 32 o))
    (hpc : t0.pc = base + BitVec.ofNat 32 tailOff)
    (hbit : (read32 t0.mem (sp + BitVec.ofNat 32 SAVED_8)).getLsbD 0 = true)
    (Q : State → Prop)
    (hQ : ∀ t : State, t.mem = retMem t0.mem V hp sp → t.regs 13 = sp + COMPRESS_FRAME_W →
      t.regs 4 = read32 t0.mem (sp + SAVED_4_W) → t.regs 5 = read32 t0.mem (sp + SAVED_5_W) →
      t.regs 6 = read32 t0.mem (sp + SAVED_6_W) → t.regs 7 = read32 t0.mem (sp + SAVED_7_W) →
      t.regs 8 = read32 t0.mem (sp + SAVED_0_W) → t.regs 9 = read32 t0.mem (sp + SAVED_1_W) →
      t.regs 10 = read32 t0.mem (sp + SAVED_2_W) → t.regs 11 = read32 t0.mem (sp + SAVED_3_W) →
      t.pc = read32 t0.mem (sp + SAVED_8_W) &&& ~~~1#32 →
      (∀ r : Reg, r.val < 4 → t.regs r = 0#32) → t.regs 12 = 0#32 → Q t) :
    ReachS base (PNR cLd W R) t0 Q := by
  obtain ⟨R1, hRA1, hmem, hR13, hR8, hR9, hR10, hR11, hRz, hR12⟩ :=
    tailBody_eff t0 V sp hp h13 r0 r2 r5 r6 r7 r8 r9 r10 r11 r12 mV hH dj
  obtain ⟨g1, g1', g2, g3, g4, g4', g5, g6⟩ := tail_regs t0 sp hp h13 hH
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := tail_checks
  have p1 := pc_adv t0 S1 base tailOff c1.1 hpc
  have p2 := pc_adv _ S2a base _ c2.1 p1
  have p3 := pc_adv _ S2b base _ c3.1 p2
  have p4 := pc_adv _ S3a base _ c4.1 p3
  have p5 := pc_adv _ S3b base _ c5.1 p4
  have p6 := pc_adv _ S3c base _ c6.1 p5
  have p7 := pc_adv _ S4 base _ c7.1 p6
  have e7 : execAll tailBody t0 = execAll S4 (execAll S3c (execAll S3b (execAll S3a (execAll S2b
      (execAll S2a (execAll S1 t0)))))) := by simp [tailBody, execAll_append]
  have szs : seqSize S1 + seqSize S2a + seqSize S2b + seqSize S3a + seqSize S3b ≤ seqSize tailBody := by decide
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [] [] S1 tailOff hpc c1.2.2.2.2 c1.2.2.2.1 c1.1
    (Reach.aligned_one (by rw [h13]; exact hsp4)) (fun p hp => by simp at hp)
    (fun p hp => by simp at hp)
    c1.2.1 c1.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [] [((4 : Reg), (0#32 : Word), 16)] S2a _ p1 c2.2.2.2.2
    c2.2.2.2.1 c2.1
    (Reach.aligned_one (by rw [g1]; exact hhp4)) (fun p hp => by simp at hp)
    (rr_one (fun o ho => by rw [g1, BitVec.add_zero]; exact hRh o (by omega)))
    c2.2.1 c2.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [((4 : Reg), (0#32 : Word), 16)]
    [((4 : Reg), (16#32 : Word), 16)] S2b _ p2 c3.2.2.2.2
    c3.2.2.2.1 c3.1 (Reach.aligned_one (by rw [g2]; exact hhp4))
    (ReachS.regionW_one (fun o ho j hj => by rw [g2, BitVec.add_zero]; exact hWh _ (by omega) (by omega) o (by omega)))
    (rr_one (fun o ho => by
      rw [g2]
      have : hp + 16#32 + BitVec.ofNat 32 o = hp + BitVec.ofNat 32 (16 + o) := by bv_omega
      rw [this]; exact hRh (16 + o) (by omega)))
    c3.2.1 c3.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [] [] S3a _ p3 c4.2.2.2.2 c4.2.2.2.1 c4.1
    (Reach.aligned_one (by rw [g3]; exact hsp4)) (fun p hp => by simp at hp)
    (fun p hp => by simp at hp)
    c4.2.1 c4.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((4 : Reg), 4)] [((4 : Reg), (0#32 : Word), 16)] [] S3b _ p4 c5.2.2.2.2
    c5.2.2.2.1 c5.1 (Reach.aligned_one (by rw [g4]; bv_omega))
    (ReachS.regionW_one (fun o ho j hj => by
      rw [g4, BitVec.add_zero]
      have : hp + 16#32 + BitVec.ofNat 32 o = hp + BitVec.ofNat 32 (16 + o) := by bv_omega
      rw [this]; exact hWh _ (by omega) (by omega) _ (by omega)))
    (fun p hp => by simp at hp)
    c5.2.1 c5.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 : Word), LOCALS_BYTES)] [] S3c _ p5
    c6.2.2.2.2 c6.2.2.2.1 c6.1 (Reach.aligned_one (by rw [g5]; exact hsp4))
    (ReachS.regionW_one (fun o ho j hj => by rw [g5, BitVec.add_zero]; exact hWf j hj o ho))
    (fun p hp => by simp at hp)
    c6.2.1 c6.2.2.1 ?_
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [] [] S4 _ p6 c7.2.2.2.2 c7.2.2.2.1 c7.1
    (Reach.aligned_one (by rw [g6]; exact hsp4)) (fun p hp => by simp at hp)
    (fun p hp => by simp at hp)
    c7.2.1 c7.2.2.1 ?_
  rw [← e7] at p7 ⊢
  have hm6 : (execAll tailBody t0).mem = retMem t0.mem V hp sp := hmem
  have s13 : (execAll tailBody t0).regs 13 = sp + SAVED_4_W := (hRA1 13 (by decide)).trans hR13
  have rdT : ∀ a, Disj hp 32 a 4 → read32 (tailMem t0.mem V hp) a = read32 t0.mem a := by
    intro a h
    unfold tailMem
    obtain ⟨h1, h2, h3⟩ := h
    have e16 : (hp + 16#32).toNat = hp.toNat + 16 := by simp [BitVec.toNat_add]; omega
    rw [read32_storeWords_ne _ _ _ _ (by simp only [List.length_cons, List.length_nil]; exact ⟨by omega, h2, by omega⟩),
      read32_storeWords_ne _ _ _ _ (by simp only [List.length_cons, List.length_nil]; exact ⟨by omega, h2, by omega⟩)]
  have hd : ∀ o, o + 4 ≤ COMPRESS_FRAME → Disj hp 32 (sp + BitVec.ofNat 32 o) 4 := fun o ho =>
    disj_frame hp sp dj 32 (by omega) o ho
  have rd : ∀ o, LOCALS_BYTES ≤ o → o + 4 ≤ COMPRESS_FRAME →
      read32 (retMem t0.mem V hp sp) (sp + BitVec.ofNat 32 o) = read32 t0.mem (sp + BitVec.ofNat 32 o) := by
    intro o h1 h2
    unfold retMem
    rw [rd_clear _ sp dj.2.1 o h1 h2]
    exact rdT _ (hd o h2)
  have a116 := rd SAVED_4 (by omega) (by omega); have a120 := rd SAVED_5 (by omega) (by omega)
  have a124 := rd SAVED_6 (by omega) (by omega); have a128 := rd SAVED_7 (by omega) (by omega)
  have a132 := rd SAVED_8 (by omega) (by omega)
  have hbit' : (read32 (execAll tailBody t0).mem ((execAll tailBody t0).regs 13 + 16#32)).getLsbD 0 = true := by
    rw [hm6, s13, show sp + SAVED_4_W + 16#32 = sp + BitVec.ofNat 32 SAVED_8 by bv_omega, a132]; exact hbit
  obtain ⟨s1, hex, sm, s13', s4, s5, s6, s7, so, spc⟩ := pop_exec (execAll tailBody t0) hbit'
  have hb4 : bitCount (0xF0#8) = 4 := by decide
  refine ReachS.stepNWNR hb2 _ (.pop 0xF0 true) p7 c8.2.1 c8.1 c8.2.2.1 ?_ hex ?_ ?_
  · simp only [Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
      Access.aligned, State.sp, hb4, s13]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Bool.toNat_true] at hi
    have : (sp + SAVED_4_W + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simpa using this
  · intro y ⟨a, ha, hk, _⟩
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp at hk
  · refine ReachS.done (hQ s1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [sm, hm6]
    · rw [s13', s13]; bv_omega
    · rw [s4, s13, hm6, a116]
    · rw [s5, s13, hm6, show sp + SAVED_4_W + 4#32 = sp + SAVED_5_W by bv_omega, a120]
    · rw [s6, s13, hm6, show sp + SAVED_4_W + 8#32 = sp + SAVED_6_W by bv_omega, a124]
    · rw [s7, s13, hm6, show sp + SAVED_4_W + 12#32 = sp + SAVED_7_W by bv_omega, a128]
    · rw [so 8 (Or.inr ⟨by decide, by decide⟩), (hRA1 8 (by decide)).trans hR8]
    · rw [so 9 (Or.inr ⟨by decide, by decide⟩), (hRA1 9 (by decide)).trans hR9]
    · rw [so 10 (Or.inr ⟨by decide, by decide⟩), (hRA1 10 (by decide)).trans hR10]
    · rw [so 11 (Or.inr ⟨by decide, by decide⟩), (hRA1 11 (by decide)).trans hR11]
    · rw [spc, s13, hm6, show sp + SAVED_4_W + 16#32 = sp + SAVED_8_W by bv_omega, a132]
    · intro r h4
      rw [so r (Or.inl h4), hRA1 r (by rintro rfl; exact absurd h4 (by decide)), hRz r h4]
    · rw [so 12 (Or.inr ⟨by decide, by decide⟩), hRA1 12 (by decide), hR12]

/-! ## Whole function -/

/-- Everything the call may write: the 136-byte frame and the 32-byte chain window. -/
def WrOf (s : State) : Word → Prop := fun y =>
  (∃ o < COMPRESS_FRAME, y = fpOf s + BitVec.ofNat 32 o) ∨ (∃ o < 32, y = s.regs 0 + BitVec.ofNat 32 o)

/-- The chain window of the call. -/
def HOf (s : State) : Word → Prop := fun y => ∃ o < 32, y = s.regs 0 + BitVec.ofNat 32 o

/-- Write bound by program counter: the frame or the chain window, and only the chain window at
the two untracked output `stm`s. -/
def CW (base : Word) (s : State) : Word → Word → Prop := fun pc y =>
  WrOf s y ∧ (SiteAt base pc → HOf s y ∧ ∃ off ∈ compressSites, pc = base + BitVec.ofNat 32 off)

theorem CW_frame {base : Word} {s : State} {j : Nat} (hj : j < tailOff) {y : Word}
    (hy : ∃ o < COMPRESS_FRAME, y = fpOf s + BitVec.ofNat 32 o) : CW base s (base + BitVec.ofNat 32 j) y :=
  ⟨Or.inl hy, fun h => absurd h (not_siteAt hj)⟩

theorem off_eq {base : Word} {x y : Nat} (hx : x < Artifacts.Release.size) (hy : y < Artifacts.Release.size)
    (h : base + BitVec.ofNat 32 x = base + BitVec.ofNat 32 y) : x = y := by
  have h4 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h4
  have hb := base.isLt
  have : Artifacts.Release.size < 2 ^ 32 := by decide
  omega

/-- The only sites in the tail are the two untracked `stm`s of the compression. -/
theorem tail_sites : ∀ off ∈ allSites, tailOff ≤ off → off < tailOff + seqSize tailBody →
    off ∈ compressSites := by decide +kernel

theorem CW_h {base : Word} {s : State} {x : Nat} {y : Word} (h1 : tailOff ≤ x)
    (h2 : x < tailOff + seqSize tailBody) (hy : HOf s y) : CW base s (base + BitVec.ofNat 32 x) y := by
  refine ⟨Or.inr hy, ?_⟩
  rintro ⟨off, hm, he⟩
  have hlt := allSites_lt off hm
  have hx : x < Artifacts.Release.size := by
    have : tailOff + seqSize tailBody ≤ Artifacts.Release.size := by decide +kernel
    omega
  have := off_eq hx hlt he
  subst this
  exact ⟨hy, x, tail_sites x hm h1 h2, rfl⟩

/-- No untracked store lies in the frame clear. -/
theorem clear_nosite : ∀ off ∈ allSites, off < clearOff ∨ clearOff + seqSize S3c ≤ off := by
  decide +kernel

theorem CW_clear {base : Word} {s : State} {j : Nat} (hj : j < seqSize S3c) {y : Word}
    (hy : ∃ o < COMPRESS_FRAME, y = fpOf s + BitVec.ofNat 32 o) :
    CW base s (base + BitVec.ofNat 32 (clearOff + j)) y :=
  ⟨Or.inl hy, fun h => absurd h (not_siteAt_range (by decide +kernel) clear_nosite hj)⟩

theorem pre_end : bOff + 2 ≤ tailOff := by decide +kernel

/-- The saved values the prologue leaves in the frame. -/
def FFacts (s : State) (F : Nat → Option Word) : Prop :=
  F HPTR_WORDS = some (s.regs 0) ∧ F SLOTW_0 = some (s.regs 8) ∧ F SLOTW_1 = some (s.regs 9) ∧
    F SLOTW_2 = some (s.regs 10) ∧ F SLOTW_3 = some (s.regs 11) ∧ F SLOTW_4 = some (s.regs 4) ∧
    F SLOTW_5 = some (s.regs 5) ∧ F SLOTW_6 = some (s.regs 6) ∧ F SLOTW_7 = some (s.regs 7) ∧
    F SLOTW_8 = some (s.regs 14)

theorem Inv_setPc {s : State} {sp : Word} {v m : Nat → Word} {c : Option Nat} (h : Inv s sp v m c)
    (x : Word) : Inv (s.setReg 15 x) sp v m c := by
  have e : ∀ r : Reg, r ≠ 15 → (s.setReg 15 x).regs r = s.regs r := by
    intro r hr; simp [State.setReg, hr]
  have em : (s.setReg 15 x).mem = s.mem := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 13 (by decide)]; exact h.spR
  · rw [e 8 (by decide)]; exact h.r8
  · rw [em]; exact h.memV
  · intro i hi; rw [e 0 (by decide)]; exact h.r0 i hi
  · rw [e 2 (by decide)]; exact h.r2
  · rw [e 5 (by decide)]; exact h.r5
  · rw [e 6 (by decide)]; exact h.r6
  · rw [e 7 (by decide)]; exact h.r7
  · rw [e 9 (by decide)]; exact h.r9
  · rw [e 10 (by decide)]; exact h.r10
  · rw [e 11 (by decide)]; exact h.r11
  · rw [e 12 (by decide)]; exact h.r12
  · rw [em]; exact h.memM

theorem pre_checks :
    (pre.take 30).all Instr.falls = true ∧ (pre.drop 30).all Instr.falls = true ∧
    M0Crypto.Sym.alignChk [((13 : Reg), 4), ((1 : Reg), 4)] (pre.take 30) = true ∧
    M0Crypto.Sym.writeChk [((13 : Reg), (0#32 - COMPRESS_FRAME_W), COMPRESS_FRAME)] (pre.take 30) = true ∧
    M0Crypto.Sym.alignChk [((13 : Reg), 4), ((1 : Reg), 4)] (pre.drop 30) = true ∧
    M0Crypto.Sym.writeChk [((13 : Reg), (0#32), COMPRESS_FRAME)] (pre.drop 30) = true ∧
    seqAt B fnStart (pre.take 30) = true ∧
    seqAt B (fnStart + seqSize (pre.take 30)) (pre.drop 30) = true ∧
    fnStart % 2 = 0 ∧ (fnStart + seqSize (pre.take 30)) % 2 = 0 ∧
    fnStart + seqSize (pre.take 30) + seqSize (pre.drop 30) = bOff ∧
    bOff % 2 = 0 ∧ bOff + 2 ≤ Artifacts.Release.size ∧
    BitVec.ofNat 32 bOff + 4#32 + (brImm11 bOff roundsOff ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 roundsOff ∧
    roundsOff = roundOff 0 := by
  decide +kernel

open M0Crypto.Sym in
theorem pre_regs (s : State) :
    (execAll (pre.take 30) s).regs 13 = s.regs 13 - 20#32 - 16#32 - SAVED_0_W ∧
    (execAll (pre.take 30) s).regs 1 = s.regs 0 := by
  constructor
  · rw [execAll_regs_norm _ (by decide)]
    have : norm ((symExec (pre.take 30) SState.init).regs 13) =
        .sub (.sub (.sub (.reg0 13) (.const 20#32)) (.const 16#32)) (.const SAVED_0_W) := by decide +kernel
    rw [this]; rfl
  · rw [execAll_regs_norm _ (by decide)]
    have : norm ((symExec (pre.take 30) SState.init).regs 1) = .reg0 0 := by decide +kernel
    rw [this]; rfl

theorem pre_reach {base : Word} {s : State} (e : Entry base s) (Q : State → Prop)
    (hQ : ∀ (t : State) (F : Nat → Option Word),
      Inv t (fpOf s) (V0 s) (Mw s) none → FS (fpOf s) F t.mem → FFacts s F →
      Out (fpOf s) s.mem t.mem → t.pc = base + BitVec.ofNat 32 roundsOff →
      ReachS base (PNR cLd (CW base s) (RR s)) t Q) :
    ReachS base (PNR cLd (CW base s) (RR s)) s Q := by
  obtain ⟨F, hI, hFS, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, hOut⟩ := pre_inv e
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := pre_checks
  obtain ⟨g13, g1⟩ := pre_regs s
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have eP : execAll preI s = execAll (pre.drop 30) (execAll (pre.take 30) s) := by
    rw [← execAll_append, List.take_append_drop]
  have p1 := pc_adv s (pre.take 30) base fnStart k1 e.pc
  have p2 := pc_adv _ (pre.drop 30) base _ k2 p1
  rw [k11] at p2
  have r13 : (execAll (pre.take 30) s).regs 13 = fpOf s := by
    rw [g13]; unfold fpOf; bv_omega
  have hpe := pre_end
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4), ((1 : Reg), 4)] [((13 : Reg), (0#32 - COMPRESS_FRAME_W), COMPRESS_FRAME)]
    [((1 : Reg), (0#32 : Word), 64)]
    (pre.take 30) fnStart e.pc k9 k7 k1 ?_ (ReachS.regionW_one (fun o ho j hj => ?_))
    (rr_one (fun o ho => Or.inl ⟨o, ho, by rw [BitVec.add_zero]⟩)) k3 k4 ?_
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact e.sp4
    · exact e.blk4
  · refine CW_frame (by omega) ⟨o, ho, by unfold fpOf; bv_omega⟩
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4), ((1 : Reg), 4)] [((13 : Reg), (0#32), COMPRESS_FRAME)]
    [((1 : Reg), (0#32 : Word), 32)]
    (pre.drop 30) (fnStart + seqSize (pre.take 30)) p1 k10 k8 k2 ?_
    (ReachS.regionW_one (fun o ho j hj => ?_))
    (rr_one (fun o ho => Or.inr ⟨o, ho, by rw [g1, BitVec.add_zero]⟩)) k5 k6 ?_
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · show ((execAll (pre.take 30) s).regs 13).toNat % 4 = 0
      rw [r13]; unfold fpOf; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := e.sp4; have := e.spLo; omega
    · show ((execAll (pre.take 30) s).regs 1).toNat % 4 = 0
      rw [g1]; exact e.hp4
  · refine CW_frame (by omega) ⟨o, ho, by rw [r13, BitVec.add_zero]⟩
  refine ReachS.bPcNR hb2 bOff roundsOff _ (by rw [← eP] at p2; exact p2) k12 b_at k13 k14 ?_
  rw [← eP] at *
  rw [k15]
  exact hQ _ F (Inv_setPc hI _) hFS ⟨f24, f25, f26, f27, f28, f29, f30, f31, f32, f33⟩ hOut rfl

/-! ## Glue -/

theorem MW_read_hi {fp : Word} {m1 m2 : Mem} (hMW : MW fp m1 m2)
    (n : Nat) (hn : 8 ≤ n) (hn2 : n + 1 ≤ SLOTW_9) :
    read32 m2 (fp + BitVec.ofNat 32 (4 * n)) = read32 m1 (fp + BitVec.ofNat 32 (4 * n)) := by
  apply MW_read hMW
  intro i hi hj k hk j hj'
  intro e
  have := congrArg BitVec.toNat e
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem read_out {fp : Word} {m0 m1 m2 : Mem} (hO : Out fp m0 m1) (hM : MW fp m1 m2) (a : Word)
    (h : Disj a 4 fp COMPRESS_FRAME) : read32 m2 a = read32 m0 a := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr : read32 m2 a = read32 m1 a := by
    apply MW_read hM
    intro i hi hj k hk j hj' e
    have := congrArg BitVec.toNat e
    simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  rw [hr]
  apply read32_congr
  intro k hk
  apply hO
  intro o ho e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem tailMem_lo (m : Mem) (V : Nat → Word) (hp : Word) (hh : hp.toNat + 32 ≤ 2 ^ 32)
    (i : Nat) (hi : i < 4) :
    read32 (tailMem m V hp) (hp + BitVec.ofNat 32 (4 * i)) =
      read32 m (hp + BitVec.ofNat 32 (4 * i)) ^^^ V i ^^^ V (i + 8) := by
  unfold tailMem
  have hd : Disj (hp + 16#32) (4 * 4) (hp + BitVec.ofNat 32 (4 * i)) 4 := by
    have e16 : (hp + 16#32).toNat = hp.toNat + 16 := by simp [BitVec.toNat_add]; omega
    have ei := toNat_add_ofNat hp (4 * i) (by omega)
    exact ⟨by omega, by omega, by omega⟩
  rw [read32_storeWords_ne _ _ _ _ (by simpa using hd)]
  rw [M0Crypto.Release.Frame.read32_storeWords_same _ hp _ i (by simp; omega) (by simp)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> first | rfl | simp

theorem tailMem_hi (m : Mem) (V : Nat → Word) (hp : Word)
    (i : Nat) (hi : 4 ≤ i) (hi2 : i < 8) :
    read32 (tailMem m V hp) (hp + BitVec.ofNat 32 (4 * i)) =
      read32 m (hp + BitVec.ofNat 32 (4 * i)) ^^^ V i ^^^ V (i + 8) := by
  unfold tailMem
  have e16 : hp + BitVec.ofNat 32 (4 * i) = hp + 16#32 + BitVec.ofNat 32 (4 * (i - 4)) := by
    rw [BitVec.add_assoc, show (16#32 : Word) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
    congr 2; omega
  rw [e16, M0Crypto.Release.Frame.read32_storeWords_same _ (hp + 16#32) _ (i - 4) (by simp; omega) (by simp)]
  rw [← e16]
  rcases (by omega : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl <;> rfl

theorem tailMem_other (m : Mem) (V : Nat → Word) (hp : Word) (y : Word)
    (hy : ∀ o < 32, y ≠ hp + BitVec.ofNat 32 o) : tailMem m V hp y = m y := by
  unfold tailMem
  have key : ∀ (a : Word) (b : Nat) (vs : List Word) (m : Mem), a = hp + BitVec.ofNat 32 b →
      b + 4 * vs.length ≤ 32 → storeWords m a vs y = m y := by
    intro a b vs m ha hb
    apply storeWords_other
    intro i k hi hk e
    apply hy (b + 4 * i + k) (by omega)
    rw [e, ha, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; omega
  rw [key (hp + 16#32) 16 _ _ rfl (by simp), key hp 0 _ _ (by simp) (by simp)]

/-- What a call computes: the chain words are the RFC 7693 compression result, `r4`-`r11` and `sp`
are restored, control returns to `lr`, and memory changes only in the frame and the chain window.
The call leaves no working value behind: `r0`-`r3` and `r12` are zero and so is every word of the
locals (`wipe`). The saved-register words above the locals keep the caller's `r4`-`r11` and `lr`. -/
structure Post (s t : State) : Prop where
  pc : t.pc = s.regs 14 &&& ~~~1#32
  sp : t.regs 13 = s.regs 13
  r4 : t.regs 4 = s.regs 4
  r5 : t.regs 5 = s.regs 5
  r6 : t.regs 6 = s.regs 6
  r7 : t.regs 7 = s.regs 7
  r8 : t.regs 8 = s.regs 8
  r9 : t.regs 9 = s.regs 9
  r10 : t.regs 10 = s.regs 10
  r11 : t.regs 11 = s.regs 11
  hout : ∀ i < 8, read32 t.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
    (M0Crypto.Spec.Blake2s.compress (arr8 (wd s.mem (s.regs 0))) (arr16 (Mw s))
      ((s.regs 2).toNat + 2 ^ 32 * (s.regs 3).toNat) (decide (read32 s.mem (s.regs 13) ≠ 0#32)))[i]!
  mem : ∀ y, (∀ o < COMPRESS_FRAME, y ≠ fpOf s + BitVec.ofNat 32 o) → (∀ o < 32, y ≠ s.regs 0 + BitVec.ofNat 32 o) →
    t.mem y = s.mem y
  scratch : ∀ r : Reg, r.val < 4 → t.regs r = 0#32
  r12 : t.regs 12 = 0#32
  wipe : ∀ i < LOCALS_WORDS, read32 t.mem (slot (fpOf s) i) = 0#32

theorem ofNat_T (a b : Word) :
    BitVec.ofNat 32 (a.toNat + 2 ^ 32 * b.toNat) = a ∧
    BitVec.ofNat 32 ((a.toNat + 2 ^ 32 * b.toNat) / 2 ^ 32) = b := by
  have ha := a.isLt; have hb := b.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega

/-- The internal-entry form of `compress_correct`: from the function start, a run reaches the
returned-to address with `Post`, writing only `WrOf s`. Unlike `compress_correct` it does not
require the return address to lie outside the code, so the in-library callers (`update`,
`final`) apply it at their call sites. -/
theorem compress_reachSR {base : Word} {s : State} (e : Entry base s) (Q : State → Prop)
    (hQ : ∀ t, Post s t → Q t) : ReachS base (PNR cLd (CW base s) (RR s)) s Q := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hfp := e.codeF.2.1
  have hfpv : (fpOf s).toNat = (s.regs 13).toNat - COMPRESS_FRAME := by
    unfold fpOf; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := e.spLo; have := (s.regs 13).isLt; omega
  have hsp4 : (fpOf s).toNat % 4 = 0 := by have := e.sp4; have := e.spLo; omega
  have hWr : ∀ o < 28, ∀ j < tailOff, CW base s (base + BitVec.ofNat 32 j) (fpOf s + 4#32 + BitVec.ofNat 32 o) :=
    fun o ho j hj => CW_frame hj ⟨4 + o, by omega, by bv_omega⟩
  have hWh : ∀ x, tailOff ≤ x → x < tailOff + seqSize tailBody → ∀ o < 32,
      CW base s (base + BitVec.ofNat 32 x) (s.regs 0 + BitVec.ofNat 32 o) := fun x h1 h2 o ho =>
    CW_h h1 h2 ⟨o, ho, rfl⟩
  have hWf : ∀ j < seqSize S3c, ∀ o < LOCALS_BYTES,
      CW base s (base + BitVec.ofNat 32 (clearOff + j)) (fpOf s + BitVec.ofNat 32 o) := fun j hj o ho =>
    CW_clear hj ⟨o, by omega, rfl⟩
  have hRh : ∀ o < 32, RR s (s.regs 0 + BitVec.ofNat 32 o) := fun o ho => Or.inr ⟨o, ho, rfl⟩
  refine pre_reach e Q ?_
  intro t1 F hI hFS hFF hOut hpc
  obtain ⟨f24, f25, f26, f27, f28, f29, f30, f31, f32, f33⟩ := hFF
  refine rounds_reach hb2 (fpOf s) hsp4 hWr (V0 s) (Mw s) 10 0 (by omega) t1 hI
    (by rw [hpc]; rfl) Q ?_
  intro t0 hI0 hMW hpc0
  have rdF : ∀ k, 8 ≤ k → k < SLOTW_9 → ∀ w, F k = some w →
      read32 t0.mem (fpOf s + BitVec.ofNat 32 (4 * k)) = w := by
    intro k hk hk2 w hw
    rw [MW_read_hi hMW k hk (by omega)]
    exact hFS k (by omega) w hw
  have hbit : (read32 t0.mem (fpOf s + BitVec.ofNat 32 SAVED_8)).getLsbD 0 = true := by
    rw [show BitVec.ofNat 32 SAVED_8 = BitVec.ofNat 32 (4 * SLOTW_8) from rfl, rdF SLOTW_8 (by omega) (by omega) _ f33]
    exact e.lr
  refine tail_reach hb2 t0 (Vr (V0 s) (Mw s) 10) (fpOf s) (s.regs 0) hI0.spR (hI0.r0 2 rfl)
    hI0.r2 hI0.r5 hI0.r6 hI0.r7 hI0.r8 hI0.r9 hI0.r10 hI0.r11 hI0.r12
    (fun i h1 h2 h3 => hI0.memV i h1 h2 (by intro h; cases h; exact h3 rfl))
    (rdF HPTR_WORDS (by omega) (by omega) _ f24) e.hpF hsp4 e.hp4 hWh hWf hRh hpc0 hbit Q ?_
  intro t hm h13 r4 r5 r6 r7 r8 r9 r10 r11 hpcT hz h12
  refine hQ t ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz, h12, ?_⟩
  · rw [hpcT, show SAVED_8 = 4 * SLOTW_8 from rfl, show (SAVED_8_W : Word) = BitVec.ofNat 32 (4 * SLOTW_8) from rfl,
      rdF SLOTW_8 (by omega) (by omega) _ f33]
  · rw [h13]; unfold fpOf; bv_omega
  · rw [r4, show (SAVED_4_W : Word) = BitVec.ofNat 32 (4 * SLOTW_4) from rfl, rdF SLOTW_4 (by omega) (by omega) _ f29]
  · rw [r5, show (SAVED_5_W : Word) = BitVec.ofNat 32 (4 * SLOTW_5) from rfl, rdF SLOTW_5 (by omega) (by omega) _ f30]
  · rw [r6, show (SAVED_6_W : Word) = BitVec.ofNat 32 (4 * SLOTW_6) from rfl, rdF SLOTW_6 (by omega) (by omega) _ f31]
  · rw [r7, show (SAVED_7_W : Word) = BitVec.ofNat 32 (4 * SLOTW_7) from rfl, rdF SLOTW_7 (by omega) (by omega) _ f32]
  · rw [r8, show (SAVED_0_W : Word) = BitVec.ofNat 32 (4 * SLOTW_0) from rfl, rdF SLOTW_0 (by omega) (by omega) _ f25]
  · rw [r9, show (SAVED_1_W : Word) = BitVec.ofNat 32 (4 * SLOTW_1) from rfl, rdF SLOTW_1 (by omega) (by omega) _ f26]
  · rw [r10, show (SAVED_2_W : Word) = BitVec.ofNat 32 (4 * SLOTW_2) from rfl, rdF SLOTW_2 (by omega) (by omega) _ f27]
  · rw [r11, show (SAVED_3_W : Word) = BitVec.ofNat 32 (4 * SLOTW_3) from rfl, rdF SLOTW_3 (by omega) (by omega) _ f28]
  · intro i hi
    have hh := e.hpF
    have hd : Disj (s.regs 0 + BitVec.ofNat 32 (4 * i)) 4 (fpOf s) COMPRESS_FRAME := by
      obtain ⟨h1, h2, h3⟩ := hh
      have := toNat_add_ofNat (s.regs 0) (4 * i) (by omega)
      exact ⟨by omega, h2, by omega⟩
    have hrd := read_out hOut hMW _ hd
    have hcl : ∀ i < 8, read32 t.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
        read32 s.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) ^^^ Vr (V0 s) (Mw s) 10 i ^^^
          Vr (V0 s) (Mw s) 10 (i + 8) := by
      intro i hi
      have hd : Disj (s.regs 0 + BitVec.ofNat 32 (4 * i)) 4 (fpOf s) COMPRESS_FRAME := by
        obtain ⟨h1, h2, h3⟩ := hh
        have := toNat_add_ofNat (s.regs 0) (4 * i) (by omega)
        exact ⟨by omega, h2, by omega⟩
      rw [hm, retMem_read _ _ _ _ _ (by obtain ⟨h1, h2, h3⟩ := hd; exact ⟨by omega, h1, by omega⟩)]
      rw [← read_out hOut hMW _ hd]
      by_cases h4 : i < 4
      · exact tailMem_lo _ _ _ (by have := hh.1; omega) i h4
      · exact tailMem_hi _ _ _ i (by omega) hi
    rw [hcl i hi]
    obtain ⟨hT0, hT1⟩ := ofNat_T (s.regs 2) (s.regs 3)
    have hF : (if decide (read32 s.mem (s.regs 13) ≠ 0#32) = true then 0xFFFFFFFF#32 else 0#32) =
        read32 s.mem (s.regs 13) := by
      rcases e.f0 with h | h <;> simp [h]
    rw [compress_get _ _ _ _ i hi, hT0, hT1, hF]
    rfl
  · intro y hy1 hy2
    rw [hm, retMem_other _ _ _ _ _ (fun o ho => hy1 o (by omega)), tailMem_other _ _ _ _ hy2]
    rw [MW_eq hMW y]
    · exact hOut y hy1
    · intro i hi hj k hk e'
      apply hy1 (4 * i + k) (by omega)
      rw [e']
      simp only [slot]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · intro i hi
    rw [hm]; exact retMem_wipe _ _ _ _ i hi

/-- The same judgment with only the write bound. -/
theorem compress_reachS {base : Word} {s : State} (e : Entry base s) (Q : State → Prop)
    (hQ : ∀ t, Post s t → Q t) : ReachS base (PN (CW base s)) s Q :=
  (compress_reachSR e Q hQ).mono (fun _ _ h => h.1) (fun _ h => h)

/-- The `Reach` form of `compress_reachS`: every write is in the frame or the chain window. -/
theorem compress_reach {base : Word} {s : State} (e : Entry base s) (Q : State → Prop)
    (hQ : ∀ t, Post s t → Q t) : Reach base (WrOf s) s Q :=
  ((compress_reachS e Q hQ).mono (P' := PcWr (CW base s)) (fun _ _ h => h.1) (fun _ h => h)).pcWr_mono
    (fun _ _ h => h.1)

/-- **`m0c_blake2s_compress` is correct.** Entered at the function start with the stated
alignment and disjointness, returning to an address outside the code, the run returns with `Post`
(the RFC 7693 compression of the chain, callee-saved registers and `sp` restored) after enough
steps, writing only the frame and the chain window. -/
theorem compress_correct {base : Word} {s : State} (e : Entry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      Post s t ∧ WritesTo (WrOf s) tr := by
  obtain ⟨n, h⟩ := Reach.runUntil (P := Post s) e.code
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := e.codeF
        intro eq
        have := congrArg BitVec.toNat eq
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
        omega
      · obtain ⟨h1, h2, h3⟩ := e.codeH
        intro eq
        have := congrArg BitVec.toNat eq
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
        omega)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((compress_reach e _ (fun t ht => ⟨ht.pc, ht⟩)))
  exact ⟨n, h⟩

end M0Crypto.Release.Blake2sCompress
