import M0Crypto.Release.Ed25519Routines
import M0Crypto.Release.Ed25519FieldRoutines
import M0Crypto.Release.SegEffect

set_option linter.unusedSimpArgs false

/-!
# `m0c_copy`, `m0c_zero`, `m0c_cmov`: word loops

Each is `push {lr}`, a straight-line `pre`, a loop `body; bne` over `n / 2` pairs of words, and
`pop {pc}`. A pass stores two words at `r0`, from the words at `r0` and at `r1` through a word
function `G κ` (`κ` the entry `r3`), and advances `r0` (and `r1`) by 8 and the counter by −2.
`wloop_tspec` proves the call lemma of any such routine (`wordR`) from the effect of one pass
(`Step`) and decided checks (`wOk`); `copy_tspec`, `zero_tspec`, `cmov_tspec` apply it to the
three loops of each build.
-/

namespace M0Crypto.Release.Ed25519WordLoop

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Frame (Disj)

/-- The number of words `n`: even, nonzero, and its bytes fit. -/
def WordsOk (n : Word) : Prop := n.toNat % 2 = 0 ∧ 0 < n.toNat ∧ 4 * n.toNat < 2 ^ 32

/-- **A word loop** at `o`, `size` bytes: `n = regs cnt` words at `dst = r0` become
`G κ dst[i] src[i]` (`src = r1`, `κ = r3`). It reads `dst` when `rdD` and `src` when `rdS`; `dst` and
`src` are equal or apart. `Pre'` constrains `κ`. -/
def wordR (o size : Nat) (cnt : Reg) (rdD rdS : Bool) (Pre' : Word → Prop)
    (G : Word → Word → Word → Word) (clob : List Reg) : Routine where
  entry := o
  code := [(o, o + size)]
  stack := 4
  Pre := fun _ s => WordsOk (s.regs cnt) ∧ (s.regs 0).toNat % 4 = 0 ∧
    (rdS = true → (s.regs 1).toNat % 4 = 0 ∧ EqOrDisj (s.regs 0) (s.regs 1) (4 * (s.regs cnt).toNat)) ∧
    Pre' (s.regs 3)
  wr := fun s => [⟨s.regs 0, 4 * (s.regs cnt).toNat⟩]
  rd := fun s => (if rdD then [⟨s.regs 0, 4 * (s.regs cnt).toNat⟩] else []) ++
    (if rdS then [⟨s.regs 1, 4 * (s.regs cnt).toNat⟩] else [])
  Post := fun s m _ => ∀ i < (s.regs cnt).toNat, read32 m (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
    G (s.regs 3) (read32 s.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)))
      (read32 s.mem (s.regs 1 + BitVec.ofNat 32 (4 * i)))
  clob := clob

/-- The public values of a word loop: `r0`, `r1`, the counter and `sp` (not the mask `r3`). -/
def wordPub (cnt : Reg) (_ : Word) (s : State) : Nat → Word :=
  pubOf [s.regs 0, s.regs 1, s.regs cnt, s.regs 13]

/-- `push {lr}`, `pre`, `body`, `bne` back to `body`, `pop {pc}`. -/
def wloop (pre body : List Instr) (imm : BitVec 8) : List Instr :=
  .push 0 true :: pre ++ body ++ [.bcond 1 imm, .pop 0 true]

/-- The regions a pass reads first, from its address registers. -/
def iniW (rdD rdS : Bool) : List (M0Crypto.Sym.SExpr × Nat) :=
  (if rdD then [(.reg0 0, 8)] else []) ++ (if rdS then [(.reg0 1, 8)] else [])

/-- The registers a pass reads addresses from. -/
def adrRegs (rdS : Bool) : List Reg := if rdS then [0, 1] else [0]

/-- The aligned registers of a pass. -/
def alOf (rdS : Bool) : List (Reg × Nat) := if rdS then [(0, 4), (1, 4)] else [(0, 4)]

/-- The read regions of a pass. -/
def rgOf (rdD rdS : Bool) : List (Reg × Word × Nat) :=
  (if rdD then [((0 : Reg), 0#32, 8)] else []) ++ (if rdS then [((1 : Reg), 0#32, 8)] else [])

/-- The decided checks: `pre` and `body` fall through and keep `sp`; `pre` accesses no memory and
keeps `r0`, `r1` and the counter; `body` stores the 8 bytes at `r0`, reads within `rgOf`, and
its trace reads `adrRegs`; registers among `r4`-`r11` outside `clob` are kept; the `bne` returns to
`body`. -/
def wOk (pre body : List Instr) (imm : BitVec 8) (cnt : Reg) (rdD rdS : Bool) (clob : List Reg) :
    Bool :=
  (pre ++ body).all Instr.falls && keepsSp (pre ++ body) && Sym.alignChk [] pre &&
  Sym.writeChk [] pre && Sym.readChk (fun _ => true) [] pre && traceOk pre [] &&
  [(0 : Reg), 1, cnt].all (fun r => pre.all fun i => !(i.dsts.contains r.val)) &&
  Sym.alignChk (alOf rdS) body && Sym.writeChk [((0 : Reg), 0#32, 8)] body &&
  Sym.readChk (fun _ => true) (rgOf rdD rdS) body && traceOk body (adrRegs rdS) &&
  ([4, 5, 6, 7, 8, 9, 10, 11] : List Reg).all
    (fun r => clob.contains r || (pre ++ body).all fun i => !(i.dsts.contains r.val)) &&
  (BitVec.ofNat 32 (seqSize body) + 4#32 + (imm ++ 0#1).signExtend 32 == 0#32) &&
  seqSize pre % 2 == 0 && seqSize body % 2 == 0

/-- The effect of one pass on a state where `Keep κ` holds. -/
def Step (body : List Instr) (cnt : Reg) (rdS : Bool) (Keep : Word → State → Prop)
    (G : Word → Word → Word → Word) : Prop :=
  ∀ κ u, Keep κ u → (execAll body u).regs 0 = u.regs 0 + 8#32 ∧
    (rdS = true → (execAll body u).regs 1 = u.regs 1 + 8#32) ∧
    (execAll body u).regs cnt = u.regs cnt - 2#32 ∧
    (execAll body u).z = ((execAll body u).regs cnt == 0#32) ∧ Keep κ (execAll body u) ∧
    (execAll body u).mem = write32 (write32 u.mem (u.regs 0)
      (G κ (read32 u.mem (u.regs 0)) (read32 u.mem (u.regs 1)))) (u.regs 0 + 4#32)
      (G κ (read32 u.mem (u.regs 0 + 4#32)) (read32 u.mem (u.regs 1 + 4#32)))

theorem memEq_write32 (m : Mem) (a v : Word) : MemEq [⟨a, 4⟩] m (write32 m a v) := fun _ hy =>
  M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => hy ⟨_, List.mem_singleton_self _, k, hk, he⟩

/-- The loop state after `j` passes, over the memory `m1` the push left: `dst` and `src` from the
entry state `s` advanced by `8 j`, the counter down by `2 j`, the first `2 j` words done and the
rest of the memory as `m1`. -/
structure Inv (cnt : Reg) (rdS : Bool) (Keep : Word → State → Prop) (G : Word → Word → Word → Word)
    (clob : List Reg) (s : State) (m1 : Mem) (j : Nat) (u : State) : Prop where
  r0 : u.regs 0 = s.regs 0 + BitVec.ofNat 32 (8 * j)
  r1 : rdS = true → u.regs 1 = s.regs 1 + BitVec.ofNat 32 (8 * j)
  rc : u.regs cnt = BitVec.ofNat 32 ((s.regs cnt).toNat - 2 * j)
  kp : Keep (s.regs 3) u
  sp : u.regs 13 = s.regs 13 - 4#32
  hi : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → r ∉ clob → u.regs r = s.regs r
  fr : MemEq [⟨s.regs 0, 8 * j⟩] m1 u.mem
  wd : ∀ i < 2 * j, read32 u.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
    G (s.regs 3) (read32 m1 (s.regs 0 + BitVec.ofNat 32 (4 * i)))
      (read32 m1 (s.regs 1 + BitVec.ofNat 32 (4 * i)))

theorem Inv.setPc {cnt : Reg} {rdS : Bool} {Keep : Word → State → Prop} {G : Word → Word → Word → Word}
    {clob : List Reg} {s : State} {m1 : Mem} {j : Nat} {u : State}
    (hK : ∀ κ u v, Keep κ u → Keep κ (u.setReg 15 v)) (hc : cnt.val ≠ 15)
    (h : Inv cnt rdS Keep G clob s m1 j u) (v : Word) : Inv cnt rdS Keep G clob s m1 j (u.setReg 15 v) := by
  have e : ∀ r : Reg, r.val ≠ 15 → (u.setReg 15 v).regs r = u.regs r := fun r hr => by
    simp [State.setReg, show r ≠ 15 from fun h => hr (h ▸ rfl)]
  exact ⟨by rw [e 0 (by decide)]; exact h.r0, fun hs => by rw [e 1 (by decide)]; exact h.r1 hs,
    by rw [e cnt hc]; exact h.rc, hK _ _ _ h.kp, by rw [e 13 (by decide)]; exact h.sp,
    fun r h4 h11 hr => by rw [e r (by omega)]; exact h.hi r h4 h11 hr, h.fr, h.wd⟩

/-- The `src` word `i ≥ 2 j` is still the one in `m1`: `dst` and `src` equal or apart. -/
theorem src_word {m1 m : Mem} {d0 s0 : Word} {n j i : Nat} (hfr : MemEq [⟨d0, 8 * j⟩] m1 m)
    (hd : EqOrDisj d0 s0 (4 * n)) (hfit : d0.toNat + 4 * n ≤ 2 ^ 32) (hi : 2 * j ≤ i) (hin : i < n) :
    read32 m (s0 + BitVec.ofNat 32 (4 * i)) = read32 m1 (s0 + BitVec.ofNat 32 (4 * i)) := by
  refine hfr.read32 fun r hr q hq => ?_
  rw [List.mem_singleton.mp hr, List.mem_singleton.mp hq]
  rcases hd with rfl | ⟨h1, h2, h3⟩ <;>
    simp only [Frame.Disj, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem add_ofNat_add (a : Word) (x y : Nat) :
    a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- **One pass**: from `Inv j` with two words left, `Inv (j + 1)`, and `Z` set exactly on the last
pass. -/
theorem inv_step {body : List Instr} {cnt : Reg} {rdS : Bool} {Keep : Word → State → Prop}
    {G : Word → Word → Word → Word} {clob : List Reg} {s : State} {m1 : Mem} {j n : Nat} {u : State}
    (hst : Step body cnt rdS Keep G)
    (hhi : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → r ∉ clob →
      body.all (fun i => !(i.dsts.contains r.val)) = true)
    (hsp : keepsSp body = true) (hG : rdS = false → ∀ κ a b b', G κ a b = G κ a b')
    (hd : rdS = true → EqOrDisj (s.regs 0) (s.regs 1) (4 * n))
    (hfit : (s.regs 0).toNat + 4 * n ≤ 2 ^ 32) (hn : n = (s.regs cnt).toNat) (hj : 2 * j + 2 ≤ n)
    (h : Inv cnt rdS Keep G clob s m1 j u) :
    Inv cnt rdS Keep G clob s m1 (j + 1) (execAll body u) ∧
      (execAll body u).z = decide (2 * j + 2 = n) := by
  obtain ⟨e0, e1, ec, ez, ek, em⟩ := hst _ u h.kp
  have hc := (s.regs cnt).isLt
  have r4 : u.regs 0 + 4#32 = s.regs 0 + BitVec.ofNat 32 (8 * j + 4) := by
    rw [h.r0, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]
  have W : MemEq ([⟨u.regs 0, 4⟩] ++ [⟨u.regs 0 + 4#32, 4⟩]) u.mem (execAll body u).mem := by
    rw [em]; exact (memEq_write32 _ _ _).trans (memEq_write32 _ _ _)
  rw [r4, h.r0] at W
  have rc' : (execAll body u).regs cnt = BitVec.ofNat 32 ((s.regs cnt).toNat - 2 * (j + 1)) := by
    rw [ec, h.rc]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the word `i` of `dst` (`k = 0`) or `src` (`k = 1`) read by the pass is still `m1`'s
  have rd0 : ∀ x, x = 8 * j ∨ x = 8 * j + 4 →
      read32 u.mem (s.regs 0 + BitVec.ofNat 32 x) = read32 m1 (s.regs 0 + BitVec.ofNat 32 x) :=
    fun x hx => h.fr.read32 (by fp_tac)
  refine ⟨⟨?_, fun hs => ?_, rc', ek, ?_, fun r h4 h11 hr => ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [e0, h.r0, show (8#32 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · rw [e1 hs, h.r1 hs, show (8#32 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · rw [execAll_regs_other _ _ 13 (by decide) hsp, h.sp]
  · rw [execAll_regs_other _ _ r (by omega) (hhi r h4 h11 hr)]; exact h.hi r h4 h11 hr
  · exact (h.fr.trans W).mono (by simp only [List.cons_append, List.nil_append]; fp_tac)
  · have e4 : (4#32 : Word) = BitVec.ofNat 32 4 := rfl
    -- the source word `2 j + k` the pass reads is `m1`'s
    have sw : ∀ k, k < 2 → ∀ a, G (s.regs 3) a (read32 u.mem (u.regs 1 + BitVec.ofNat 32 (4 * k))) =
        G (s.regs 3) a (read32 m1 (s.regs 1 + BitVec.ofNat 32 (4 * (2 * j + k)))) := by
      intro k hk a
      cases rdS
      · exact hG rfl _ _ _ _
      · rw [h.r1 rfl, add_ofNat_add, show 8 * j + 4 * k = 4 * (2 * j + k) by omega,
          src_word h.fr (hd rfl) hfit (by omega) (by omega)]
    rcases (show i < 2 * j ∨ i = 2 * j ∨ i = 2 * j + 1 by omega) with hi' | rfl | rfl
    · rw [W.read32 (by simp only [List.cons_append, List.nil_append]; fp_tac)]; exact h.wd i hi'
    · have s0 := sw 0 (by decide)
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at s0
      rw [show 4 * (2 * j) = 8 * j by omega, ← h.r0, em,
        MemEq.read32 (a := u.regs 0) (memEq_write32 _ _ _) (by rw [r4, h.r0]; fp_tac),
        M0Crypto.Armv6M.read32_write32_same, h.r0, rd0 _ (Or.inl rfl), s0,
        show 4 * (2 * j) = 8 * j by omega]
    · rw [show 4 * (2 * j + 1) = 8 * j + 4 by omega, ← r4, em, M0Crypto.Armv6M.read32_write32_same,
        r4, rd0 _ (Or.inr rfl), e4, sw 1 (by decide), show 4 * (2 * j + 1) = 8 * j + 4 by omega]
  · rw [ez, rc']; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    · intro e; rw [show (s.regs cnt).toNat - 2 * (j + 1) = 0 by omega]

/-- The addresses a pass reads its trace from, as public values. -/
def vsOf (rdS : Bool) (P : Nat → Word) (j : Nat) : List Word :=
  if rdS then [P 0 + BitVec.ofNat 32 (8 * j), P 1 + BitVec.ofNat 32 (8 * j)] else [P 0 + BitVec.ofNat 32 (8 * j)]

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **The effect of a word loop** at public values `P`: it accesses the `4 · P 2` bytes at `P 0`
and, when it reads the source, at `P 1`; it reads first those it reads; it writes those at `P 0`. -/
def wloopE (rdD rdS : Bool) (_ : Word) (P : Nat → Word) : TrP :=
  StackEffect.EffT 4 (fun y => Region (P 0) (8 * ((P 2).toNat / 2)) y ∨ rdS = true ∧ Region (P 1) (8 * ((P 2).toNat / 2)) y)
    (fun y => rdD = true ∧ Region (P 0) (8 * ((P 2).toNat / 2)) y ∨ rdS = true ∧ Region (P 1) (8 * ((P 2).toNat / 2)) y)
    (Region (P 0) (8 * ((P 2).toNat / 2))) (P 3)

section eff
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
open M0Crypto.Sym (SExpr)
variable {sp0 : Word} {n : Nat}

theorem reg_in8 {a y : Word} {c w N : Nat} (h : Region (a + BitVec.ofNat 32 c) w y) (hc : c + w ≤ N) :
    Region a N y := by
  simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢
  have := a.isLt; have := y.isLt; omega

theorem reg_lt8 {a : Word} {o w : Nat} (h : o < w) : Region a w (a + BitVec.ofNat 32 o) := by
  simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp only [BitVec.toNat_ofNat]; omega

/-- The regions a pass accesses. -/
theorem inR_fp {t : State} {rdD rdS : Bool} {y : Word} (h : InR t ((.reg0 0, 8) :: iniW rdD rdS) y) :
    Region ((SExpr.reg0 0).denote t) 8 y ∨ rdS = true ∧ Region ((SExpr.reg0 1).denote t) 8 y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  rcases List.mem_cons.1 hr with rfl | hr
  · exact .inl (reg_lt8 ho)
  rcases List.mem_append.1 hr with hr | hr <;> split at hr <;>
    simp only [List.mem_singleton, List.not_mem_nil] at hr <;> subst hr
  · exact .inl (reg_lt8 ho)
  · exact .inr ⟨‹_›, reg_lt8 ho⟩

/-- The regions a pass reads first. -/
theorem inR_ini {t : State} {rdD rdS : Bool} {y : Word} (h : InR t (iniW rdD rdS) y) :
    rdD = true ∧ Region ((SExpr.reg0 0).denote t) 8 y ∨ rdS = true ∧ Region ((SExpr.reg0 1).denote t) 8 y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  rcases List.mem_append.1 hr with hr | hr <;> split at hr <;>
    simp only [List.mem_singleton, List.not_mem_nil] at hr <;> subst hr
  · exact .inl ⟨‹_›, reg_lt8 ho⟩
  · exact .inr ⟨‹_›, reg_lt8 ho⟩

theorem den_vs (rdS : Bool) (pc : Word) (P : Nat → Word) (j : Nat) :
    (SExpr.reg0 0).denote (regState pc (adrRegs rdS) (vsOf rdS P j)) = P 0 + BitVec.ofNat 32 (8 * j) ∧
    (rdS = true → (SExpr.reg0 1).denote (regState pc (adrRegs rdS) (vsOf rdS P j)) = P 1 + BitVec.ofNat 32 (8 * j)) := by
  cases rdS <;> exact ⟨rfl, by first | (intro; rfl) | (intro h; cases h)⟩

/-- **A routine `push {mask, lr}`, a body at the lowered SP that keeps the saved words, then
`pop {mask, pc}`**: `frameK_gp` without a frame. -/
theorem pushK_gp {mask : BitVec 8} {sp pc1 pc4 : Word} {U R2 R' : Word → Prop} {Ψ : TrP}
    (hroom : (sp0 - sp).toNat + 4 * nSaved mask < 2 ^ 32)
    (hB : GP sp0 n (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask))
      (fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)) Ψ
      (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) R2))
    (hS : ∀ y, Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y → R2 y)
    (hR' : ∀ y, R' y → U y ∨ AtOrAboveSp sp0 sp y ∧ R2 y) (hUR : ∀ y, U y → R2 y) :
    GP sp0 n (SIR sp0 sp U)
      (Tr.cat (Tr.is [⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat Ψ (Tr.is [⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])))
      (SIR sp0 sp R') := fun q hq => by
  have hU : ∀ y, U y → AtOrAboveSp sp0 sp y := fun y hy => hq.ab y (hq.r y hy)
  have h4 : 4 * nSaved mask < 2 ^ 32 := by omega
  have a1 : ∀ y, (U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) →
      AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y :=
    fun y hy => hy.elim (fun h => above_sub (hU y h) hroom) fun h => reg_sub_above h (Nat.le_refl _) hroom
  have s1 : spAfter (.push mask true) sp = sp - BitVec.ofNat 32 (4 * nSaved mask) := by
    simp only [spAfter, nSaved, Bool.toNat_true]
  have s4 : spAfter (.pop mask true) (sp - BitVec.ofNat 32 (4 * nSaved mask)) = sp := by
    show _ + BitVec.ofNat 32 (4 * nSaved mask) = sp; exact BitVec.sub_add_cancel _ _
  have e1 := sir_ev (sp0 := sp0) (n := n) (R := U)
    (e := ⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩)
    (R' := fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) rfl s1
    (fun y hy => .inr (hy.elim (fun h => absurd h no_reads)
      fun h => reg_sub_above (writes_words h4 h) (Nat.le_refl _) hroom)) (fun y h => absurd h no_reads)
    (fun y hy => ⟨a1 y hy, hy.imp_right words_of⟩)
  have e4 := sir_ev (sp0 := sp0) (n := n) (R' := R')
    (R := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y ∧ R2 y)
    (e := ⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩) rfl s4
    (fun y hy => .inl (hy.elim (fun h => reg_sub_above (reads_words h4 h) (Nat.le_refl _) hroom)
      fun h => absurd h no_writes))
    (fun y h => ⟨reg_sub_above (reads_words h4 h) (Nat.le_refl _) hroom, hS y (reads_words h4 h)⟩)
    fun y hy => (hR' y hy).elim (fun h => ⟨hU y h, .inl ⟨above_sub (hU y h) hroom, hUR y h⟩⟩)
      fun h => ⟨h.1, .inl ⟨above_sub h.1 hroom, h.2⟩⟩
  exact GP.cat e1 (GP.cat (GP.post hB fun q hq => ⟨hq.hs, fun y hy => hq.r y hy.2, hq.ab⟩) e4) q hq

end eff

/-- **A word loop's call lemma with its effect**, from the effect of one pass and the decided
checks. -/
noncomputable def wloop_te {pre body : List Instr} {imm : BitVec 8} {o : Nat} {cnt : Reg} {rdD rdS : Bool}
    {Pre' : Word → Prop} {G : Word → Word → Word → Word} {clob : List Reg}
    {Keep : Word → State → Prop} (hK : ∀ κ u v, Keep κ u → Keep κ (u.setReg 15 v))
    (hpre : ∀ u, Pre' (u.regs 3) → Keep (u.regs 3) (execAll pre u))
    (hst : Step body cnt rdS Keep G) (hG : rdS = false → ∀ κ a b b', G κ a b = G κ a b')
    (hcnt : cnt = 1 ∨ cnt = 2) (hok : wOk pre body imm cnt rdD rdS clob = true)
    (hblk : StackEffect.blkChk [] [] [] pre && StackEffect.blkChk (iniW rdD rdS) [(.reg0 0, 8)]
      ((.reg0 0, 8) :: iniW rdD rdS) body = true)
    (hseq : seqAt B o (wloop pre body imm) = true) (ho : o % 2 = 0) :
    (wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob).TE (wordPub cnt) (wloopE rdD rdS) := by
  simp only [wOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hk⟩, pa⟩, pw⟩, pr⟩, pt⟩, pregs⟩, ba⟩, bw⟩, br⟩, bt⟩, bhi⟩, bimm⟩, pev⟩,
    bev⟩ := hok
  simp only [keepsSp, List.all_append, Bool.and_eq_true] at hf hk
  have keepPre : ∀ r : Reg, r ∈ [(0 : Reg), 1, cnt] → ∀ u, (execAll pre u).regs r = u.regs r :=
    fun r hr u => execAll_regs_other _ _ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> first | decide | (rcases hcnt with rfl | rfl <;> decide))
      (List.all_eq_true.mp pregs r hr)
  have keepHi : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → r ∉ clob →
      (pre ++ body).all (fun i => !(i.dsts.contains r.val)) = true := fun r h4 h11 hr => by
    have := List.all_eq_true.mp bhi r (mem_hiRegs h4 h11)
    simpa [hr] using this
  -- the code: `push` at `o`, `pre`, `body` at `L`, `bne` at `ob`, `pop` at `ob + 2`
  have e2 : seqSize [Instr.push 0 true] = 2 := rfl
  have hw : wloop pre body imm = [Instr.push 0 true] ++ pre ++ body ++ [.bcond 1 imm] ++ [.pop 0 true] := by
    simp [wloop]
  have hs := hseq
  rw [hw, seqAt_append, seqAt_append, seqAt_append, seqAt_append, seqSize_append, seqSize_append,
    seqSize_append, e2] at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨hpush, hpreS⟩, hbodyS⟩, hbne⟩, hpop⟩ := hs
  have e1 : seqSize [Instr.bcond 1 imm] = 2 := rfl
  rw [show o + (2 + seqSize pre) = o + 2 + seqSize pre by omega] at hbodyS
  rw [show o + (2 + seqSize pre + seqSize body) = o + 2 + seqSize pre + seqSize body by omega] at hbne
  rw [seqSize_append, seqSize_append, seqSize_append, e2, e1,
    show o + (2 + seqSize pre + seqSize body + 2) = o + 2 + seqSize pre + seqSize body + 2 by omega] at hpop
  have hsz : seqSize (wloop pre body imm) = seqSize pre + seqSize body + 6 := by
    rw [hw]; simp [seqSize_append, seqSize, Instr.size]; omega
  have hlen : o + seqSize (wloop pre body imm) ≤ BS := by
    have := seqAt_size B o _ hseq
    rw [B_len] at this
    exact this.resolve_right (by simp [wloop])
  rw [hsz] at hlen
  have hc15 : cnt.val ≠ 15 := by rcases hcnt with rfl | rfl <;> decide
  have hcode : rangesSub [(o, o + 2), (o + 2 + seqSize pre + seqSize body + 2,
      o + 2 + seqSize pre + seqSize body + 2 + 2)] [(o, o + (seqSize pre + seqSize body + 6))] = true := by
    simp only [rangesSub, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  trefine Routine.te_by (fun base s e => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun b P tr h => ?_)
  generalize hP : wordPub cnt base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs cnt = P 2 ∧ s.regs 13 = P 3 := by
    subst hP; exact ⟨rfl, rfl, rfl, rfl⟩
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  obtain ⟨⟨hn2, hn0, hn4⟩, h0a, hsrc, hpre'⟩ := e.pre
  have hsW := e.sepWr
  have hsR := e.sepRd
  simp only [wordR] at hsW hsR
  trefine ReachFT.push_popK (f := wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob)
    (mask := 0) (epi := o + 2 + seqSize pre + seqSize body + 2) (by decide)
    (instrAt_of_seqAt hpush) (instrAt_of_seqAt hpop) ho (by omega) (by simp only [wordR]; omega)
    (by omega) (by rw [show (wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob).code =
      [(o, o + (seqSize pre + seqSize body + 6))] by simp [wordR, hsz]]; exact hcode)
    (by show 4 * nSaved 0 ≤ 4; decide) e q.2.2.2 ?_
  intro t tpc t13 tr hm hc
  trefine ReachFT.block hb2 pre (o + 2) tpc (by omega) hpreS hf.1 hk.1
    (PcIn.region (cs := [(o, o + seqSize (wloop pre body imm))]) (List.mem_singleton_self _) (by omega)
      (by rw [hsz]; omega)) [] [] [] pa pw pr (by simp) (by simp [regions, Has]) (by simp [regions, Has])
    ⟨4, by simp [wordR], t13⟩ (traceAll_blockTr (L := []) (vs := []) hf.1 pt tpc rfl) ?_
  -- after `pre`
  have tr' : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r := tr
  have sp1 : t.regs 13 = s.regs 13 - 4#32 := t13
  have m2 : (execAll pre t).mem = t.mem := funext fun y =>
    execAll_memEq t hf.1 pw y (by simp [regions, Has])
  have kp : ∀ r : Reg, r ∈ [(0 : Reg), 1, cnt] → (execAll pre t).regs r = s.regs r := fun r hr => by
    rw [keepPre r hr, tr' r (by simp at hr; rcases hr with rfl | rfl | rfl <;>
      first | decide | (rcases hcnt with rfl | rfl <;> decide))
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> first | decide | exact hc15)]
  have hn := (s.regs cnt).isLt
  have hfit : (s.regs 0).toNat + 4 * (s.regs cnt).toNat ≤ 2 ^ 32 :=
    (hsW _ List.mem_cons_self _ List.mem_cons_self).1
  have init : Inv cnt rdS Keep G clob s t.mem 0 (execAll pre t) :=
    ⟨by rw [kp 0 (by simp)]; simp, fun _ => by rw [kp 1 (by simp)]; simp,
      by rw [kp cnt (by simp)]; simp, by have := hpre t (by rw [tr' 3 (by decide) (by decide)]; exact hpre'); rwa [tr' 3 (by decide) (by decide)] at this,
      by rw [execAll_regs_other _ _ 13 (by decide) hk.1, sp1],
      fun r h4 h11 hr => by
        rw [execAll_regs_other _ _ r (by omega) (by have := keepHi r h4 h11 hr; simp only [List.all_append, Bool.and_eq_true] at this; exact this.1),
          tr' r (by omega) (by omega)],
      by rw [m2]; exact MemEq.rfl' _ _, fun i hi => absurd hi (by omega)⟩
  have hnP : (P 2).toNat = (s.regs cnt).toNat := by rw [q.2.2.1]
  have hpc2 : (execAll pre t).pc = base + BitVec.ofNat 32 (o + 2 + seqSize pre) := by
    rw [execAll_pc _ _ hf.1, tpc, ofNat_add_assoc]; rfl
  have h1a : rdS = true → (s.regs 1).toNat % 4 = 0 := fun h => (hsrc h).1
  have hwin : Sep [⟨s.regs 0, 4 * (s.regs cnt).toNat⟩] [saved 0 s] := by
    rw [saved0_eq (f := wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob) rfl]; exact hsW
  trefine ReachFT.loop (o := o + 2 + seqSize pre) (ob := o + 2 + seqSize pre + seqSize body) (d := 4)
    (Caller.of_entry (mask := 0) e) 1 imm (instrAt_of_seqAt hbne) ((P 2).toNat / 2)
    (fun j u => Inv cnt rdS Keep G clob s t.mem j u) (fun _ _ _ h => h.setPc hK hc15 _)
    (fun j u hj hpc hI h13 hcu => ?_) (fun u hpu hI h13 hcu => ?_) ?_ 0 _ (by omega) hpc2 init
    (by rw [execAll_regs_other _ _ 13 (by decide) hk.1, sp1]) (by rw [m2]; exact hc)
  · -- one pass
    have hj2 : 2 * j + 2 ≤ (s.regs cnt).toNat := by rw [hnP] at hj; omega
    obtain ⟨hI', hz⟩ := inv_step hst (fun r h4 h11 hr => by
      have := keepHi r h4 h11 hr; simp only [List.all_append, Bool.and_eq_true] at this; exact this.2)
      hk.2 hG (fun h => (hsrc h).2) hfit rfl hj2 hI
    have hw : ∀ y, Has (regions u [((0 : Reg), 0#32, 8)]) y →
        Has (lowWin (wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob) 0 s ::
          (wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob).wr s) y := by
      rintro y ⟨r, hr, k, hk8, rfl⟩
      simp only [regions, List.map, List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 8 * j + k,
        by simp only [wordR] at hk8 ⊢; omega,
        by simp only [hI.r0, BitVec.add_zero, add_ofNat_add]⟩
    trefine ReachFT.block hb2 body (o + 2 + seqSize pre) hpc (by omega) hbodyS hf.2 hk.2
      (PcIn.region (cs := [(o, o + seqSize (wloop pre body imm))]) (List.mem_singleton_self _) (by omega)
        (by rw [hsz]; omega))
      (alOf rdS) [((0 : Reg), 0#32, 8)] (rgOf rdD rdS) ba bw br ?_ hw ?_ ⟨4, by simp [wordR], h13⟩
      (traceAll_blockTr (L := adrRegs rdS) (vs := vsOf rdS P j) hf.2 bt hpc ?_)
      (ReachT.done ⟨?_, ?_, codeAt_execAll_has (Caller.of_entry (mask := 0) e).codeW hw hf.2 bw hcu, hI', ?_⟩)
    · intro p hp
      have a0 : (u.regs 0).toNat % 4 = 0 := by
        simp only [hI.r0, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      cases hS : rdS <;> simp only [alOf, hS, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, Bool.false_eq_true, ite_false, ite_true] at hp
      · subst hp; exact a0
      · rcases hp with rfl | rfl
        · exact a0
        · have := h1a hS; simp only [hI.r1 hS, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rintro y ⟨r, hr, k, hk8, rfl⟩
      simp only [regions, rgOf, List.map_append, List.mem_append] at hr
      rcases hr with hr | hr
      · cases hD : rdD <;> simp only [hD, List.map_nil, List.not_mem_nil, Bool.false_eq_true, ite_false,
          ite_true, List.map_cons, List.mem_singleton] at hr
        subst hr
        exact ⟨⟨s.regs 0, 4 * (s.regs cnt).toNat⟩, by simp [wordR, hD], 8 * j + k,
          by simp only at hk8 ⊢; omega,
          by simp only [hI.r0, BitVec.add_zero, add_ofNat_add]⟩
      · cases hS : rdS <;> simp only [hS, List.map_nil, List.not_mem_nil, Bool.false_eq_true, ite_false,
          ite_true, List.map_cons, List.mem_singleton] at hr
        subst hr
        exact ⟨⟨s.regs 1, 4 * (s.regs cnt).toNat⟩, by simp [wordR, hS], 8 * j + k,
          by simp only at hk8 ⊢; omega,
          by simp only [hI.r1 hS, BitVec.add_zero, add_ofNat_add]⟩
    · cases hS : rdS <;> simp [adrRegs, vsOf, hI.r0, q.1, hS, hI.r1, q.2.1]
    · rw [execAll_pc _ _ hf.2, hpc, ofNat_add_assoc]
    · rw [execAll_regs_other _ _ 13 (by decide) hk.2, h13]
    · rw [M0Crypto.Release.RoutineBranch.cond_ne, hz, hnP]
      by_cases h : 2 * j + 2 = (s.regs cnt).toNat <;> simp [h] <;> omega
  · -- the exit
    refine ReachT.done ⟨by rw [hpu], by rw [h13, t13]; rfl, fun r h4 h11 _ hr => hI.hi r h4 h11 hr,
      fun i hi => ?_⟩
    have hi' : i < 2 * ((P 2).toNat / 2) := by rw [hnP]; omega
    rw [hI.wd i hi', hm.read32 (a := s.regs 0 + BitVec.ofNat 32 (4 * i)) (Sub.sep (by fp_tac) hwin)]
    cases hS : rdS
    · exact hG hS _ _ _ _
    · have hsrcw : Sep [⟨s.regs 1, 4 * (s.regs cnt).toNat⟩] [saved 0 s] := by
        rw [saved0_eq (f := wordR o (seqSize (wloop pre body imm)) cnt rdD rdS Pre' G clob) rfl]
        exact sep_of_mem (by simp [hS]) hsR
      have : (s.regs 1).toNat + 4 * (s.regs cnt).toNat ≤ 2 ^ 32 :=
        (hsrcw _ List.mem_cons_self _ List.mem_cons_self).1
      rw [hm.read32 (a := s.regs 1 + BitVec.ofNat 32 (4 * i)) (Sub.sep (by fp_tac) hsrcw)]
  · simp only [loopOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨⟨⟨by omega, ?_⟩, by omega⟩, ?_⟩, by simp [wordR]⟩
    · simp only [wordR, rangesSub, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, hsz]; omega
    · rw [show BitVec.ofNat 32 (o + 2 + seqSize pre + seqSize body) =
          BitVec.ofNat 32 (o + 2 + seqSize pre) + BitVec.ofNat 32 (seqSize body) by rw [BitVec.ofNat_add],
        BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 32 (seqSize body)), bimm,
        BitVec.add_zero]
  · uniq_tac
  · open StackEffect in
    refine ex_cat ⟨_, rfl⟩ (ex_cat (ex_cat ⟨_, rfl⟩ (ex_rep (Ψ := Tr.is []) (fun _ => ?_) ⟨_, rfl⟩ _ _)) ⟨_, rfl⟩)
    exact ex_cat (ex_cat ⟨_, rfl⟩ ⟨_, rfl⟩) ⟨_, rfl⟩
  · -- the effect: the frame, `pre`, and pass `j` writing the 8 bytes from `P 0 + 8 j`
    simp only [Bool.and_eq_true] at hblk
    have hn1 : nSaved 0 = 1 := by decide
    refine StackEffect.effT_of_gp fun sp0 n U hroom hn hF hR => StackEffect.GP.is_of (pushK_gp (mask := 0)
      (R2 := fun y => (U y ∨ Region (P 3 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
        Region (P 0) (8 * (0 + ((P 2).toNat / 2 - 0))) y ∧ BelowEntry sp0 n y)
      (R' := fun y => U y ∨ Region (P 0) (8 * ((P 2).toNat / 2)) y ∧ BelowEntry sp0 n y) (by rw [hn1]; omega) ?_
      (fun y h => .inl (.inr h)) (fun y h => h.elim .inl fun h => .inr ⟨hF y (.inl h.1) h.2, .inr ⟨by simpa using h.1, h.2⟩⟩)
      (fun y h => .inl (.inl h))) h
    have hab : ∀ y, Region (P 0) (8 * ((P 2).toNat / 2)) y ∨ rdS = true ∧ Region (P 1) (8 * ((P 2).toNat / 2)) y →
        BelowEntry sp0 n y → AtOrAboveSp sp0 (P 3 - BitVec.ofNat 32 (4 * nSaved 0)) y :=
      fun y hy hb => StackEffect.above_sub (hF y hy hb) (by rw [hn1]; omega)
    refine StackEffect.GP.cat (StackEffect.sir_blk hblk.1 fun y ⟨_, h, _⟩ => absurd h List.not_mem_nil)
      (StackEffect.GP.pre (fun q hq => StackEffect.SIR.mono hq fun y h => by
        rcases h with h | h; exact h; exact absurd h.1 (by simp [Region])) (StackEffect.GP.repI (I := fun j => StackEffect.SIR sp0 (P 3 - BitVec.ofNat 32 (4 * nSaved 0)) fun y =>
          (U y ∨ Region (P 3 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
            Region (P 0) (8 * j) y ∧ BelowEntry sp0 n y) _ 0 (fun j _ hj => ?_) (StackEffect.GP.nil fun _ h => h)))
    obtain ⟨d0, d1⟩ := den_vs rdS (b + BitVec.ofNat 32 (o + 2 + seqSize pre)) P j
    have hj8 : 8 * j + 8 ≤ 8 * ((P 2).toNat / 2) := by omega
    refine StackEffect.GP.cat (StackEffect.GP.cat (StackEffect.sir_segR (fun _ => StackEffect.blk_seg hblk.2 _
      (fun _ h => h) fun y hy hb => hab y ?_ hb) (fun y hy hb => ?_) fun y hy => ?_) (StackEffect.GP.nil fun _ h => h))
      (StackEffect.sir_quietC rfl rfl rfl)
    · rcases inR_fp hy with h | ⟨hS, h⟩
      · exact .inl (reg_in8 (d0 ▸ h) hj8)
      · exact .inr ⟨hS, reg_in8 (d1 hS ▸ h) hj8⟩
    · refine .inl (.inl (hR y ?_ hb))
      rcases inR_ini hy with ⟨hD, h⟩ | ⟨hS, h⟩
      · exact .inl ⟨hD, reg_in8 (d0 ▸ h) hj8⟩
      · exact .inr ⟨hS, reg_in8 (d1 hS ▸ h) hj8⟩
    · rcases hy with h | ⟨h, hb⟩
      · exact .inl (.inl h)
      · rcases StackEffect.reg_split (x := 8 * j) (w := 8) (by rwa [show 8 * j + 8 = 8 * (j + 1) by omega]) with h | h
        · exact .inl (.inr ⟨h, hb⟩)
        · exact .inr ⟨StackEffect.inR_one (by rw [d0]; exact h), hb⟩
/-! ## The three loops -/

/-- A pass of `m0c_copy`: `ldm r1!, {r3, r4}; stm r0!, {r3, r4}; subs r2, #2`. -/
def copyBody : List Instr := [.ldm 1 0x18, .stm 0 0x18, .subImm8 2 2]

/-- `m0c_zero` before its loop: `movs r2, #0; movs r3, #0`. -/
def zeroPre : List Instr := [.movImm 2 0, .movImm 3 0]

/-- A pass of `m0c_zero`: `stm r0!, {r2, r3}; subs r1, #2`. -/
def zeroBody : List Instr := [.stm 0 0x0c, .subImm8 1 2]

/-- A pass of `m0c_cmov`: load two words of `dst` (`r4`, `r5`) and of `src` (`r6`, `r7`), mix them
under the mask `r3`, store them, `subs r2, #2`. -/
def cmovBody : List Instr := [.memImm .ldr 4 0 0, .memImm .ldr 5 0 1, .ldm 1 0xc0, .dp .eors 6 4,
  .dp .eors 7 5, .dp .ands 6 3, .dp .ands 7 3, .dp .eors 4 6, .dp .eors 5 7, .stm 0 0x30, .subImm8 2 2]

/-- The word `m0c_cmov` stores: the bits of `b` where the mask `κ` is set, of `a` elsewhere. -/
def sel (κ a b : Word) : Word := a ^^^ ((b ^^^ a) &&& κ)

theorem sel_zero (a b : Word) : sel 0 a b = a := by simp [sel]

theorem sel_ones (a b : Word) : sel (BitVec.allOnes 32) a b = b := by
  rw [sel, BitVec.and_allOnes, BitVec.xor_comm, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem lr18 : listRegs 0x18 = [3, 4] := by decide
theorem lr0c : listRegs 0x0c = [2, 3] := by decide
theorem lrc0 : listRegs 0xc0 = [6, 7] := by decide
theorem lr30 : listRegs 0x30 = [4, 5] := by decide

theorem awc_sub2 (x : Word) : (M0Crypto.Armv6M.addWithCarry x 4294967293#32 true).1 = x - 2#32 :=
  M0Crypto.Release.sub_flags x 2#32

/-- Unfolds a pass to its effect. -/
macro "pass_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    simp only [$ts,*, execAll, Instr.next, Instr.exec, bitCount, List.map, loadRegs, storeWords]
    simp [State.setReg, State.reg, State.setNZCV, State.setNZ, addFlags, M0Crypto.Release.sub_flags,
      Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6,
      M0Crypto.Proofs.toReg_7, awc_sub2]))

theorem copy_step : Step copyBody 2 true (fun _ _ => True) (fun _ _ b => b) := by
  intro κ u _; pass_simp [copyBody, lr18]

theorem zero_pre (u : State) : (execAll zeroPre u).regs 2 = 0#32 ∧ (execAll zeroPre u).regs 3 = 0#32 := by
  simp [zeroPre, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3]

theorem zero_step :
    Step zeroBody 1 false (fun _ u => u.regs 2 = 0#32 ∧ u.regs 3 = 0#32)
      (fun _ _ _ => 0#32) := by
  intro κ u ⟨h2, h3⟩; pass_simp [zeroBody, lr0c]; simp [h2, h3]

theorem cmov_step : Step cmovBody 2 true (fun κ u => u.regs 3 = κ) sel := by
  intro κ u h3; subst h3; pass_simp [cmovBody, lrc0, lr30, sel, MemOp.width]

open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts

/-- `m0c_copy` in each build: `r2` words from `r1` to `r0`, with its effect. -/
noncomputable def copy_te (b : Build) : letI := b.codeBytes
    (wordR Ed25519Compact.copy (seqSize (wloop [] copyBody 0xfb)) 2 false true (fun _ => True) (fun _ _ b => b) [4]).TE
      (wordPub 2) (wloopE false true) :=
  @wloop_te _ _ b.codeBytes [] copyBody 0xfb _ 2 false true _ _ [4] _ (fun _ _ _ _ => trivial)
    (fun _ _ => trivial) copy_step (by intro h; cases h) (Or.inr rfl) (by decide +kernel) (by decide +kernel)
    (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)

theorem copy_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => wordR Ed25519Compact.copy (seqSize (wloop [] copyBody 0xfb)) 2 false
      true (fun _ => True) (fun _ _ b => b) [4]) (wordPub 2) :=
  letI := b.codeBytes; ⟨(copy_te b).T, fun _ => (copy_te b).spec⟩

/-- `m0c_zero` in each build: `r1` zero words at `r0`, with its effect. -/
noncomputable def zero_te (b : Build) : letI := b.codeBytes
    (wordR Ed25519Compact.zero (seqSize (wloop zeroPre zeroBody 0xfc)) 1 false false (fun _ => True)
      (fun _ _ _ => 0#32) []).TE (wordPub 1) (wloopE false false) :=
  @wloop_te _ _ b.codeBytes zeroPre zeroBody 0xfc _ 1 false false _ _ [] _
    (fun _ _ _ h => by simp [State.setReg, h.1, h.2]) (fun u _ => zero_pre u) zero_step
    (fun _ _ _ _ _ => rfl) (Or.inl rfl) (by decide +kernel) (by decide +kernel)
    (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)

theorem zero_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => wordR Ed25519Compact.zero (seqSize (wloop zeroPre zeroBody 0xfc)) 1
      false false (fun _ => True) (fun _ _ _ => 0#32) []) (wordPub 1) :=
  letI := b.codeBytes; ⟨(zero_te b).T, fun _ => (zero_te b).spec⟩

/-- `m0c_cmov` in each build: `r2` words at `r0` become `sel r3` of themselves and those at `r1`,
with its effect. -/
noncomputable def cmov_te (b : Build) : letI := b.codeBytes
    (wordR Ed25519Compact.cmov (seqSize (wloop [] cmovBody 0xf3)) 2 true true (fun _ => True) sel
      [4, 5, 6, 7]).TE (wordPub 2) (wloopE true true) :=
  @wloop_te _ _ b.codeBytes [] cmovBody 0xf3 _ 2 true true _ _ [4, 5, 6, 7] (fun κ u => u.regs 3 = κ)
    (fun _ _ _ h => by simp [State.setReg, h]) (fun _ _ => rfl) cmov_step (by intro h; cases h)
    (Or.inr rfl) (by decide +kernel) (by decide +kernel) (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel))
    (by decide)

theorem cmov_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => wordR Ed25519Compact.cmov (seqSize (wloop [] cmovBody 0xf3)) 2 true
      true (fun _ => True) sel [4, 5, 6, 7]) (wordPub 2) :=
  letI := b.codeBytes; ⟨(cmov_te b).T, fun _ => (cmov_te b).spec⟩

end M0Crypto.Release.Ed25519WordLoop
