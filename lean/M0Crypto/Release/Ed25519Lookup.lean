import M0Crypto.Release.Ed25519WordLoop
import M0Crypto.Release.Ed25519FeAddSub
import M0Crypto.Release.Ed25519FieldSite
import M0Crypto.Release.Ed25519GeAdd
import M0Crypto.Release.RoutineBlock
import M0Crypto.Release.FrameKeep
import M0Crypto.Sym.MemBridge
import M0Crypto.Thumb.RangeDecode

set_option linter.unusedSimpArgs false

/-!
# `m0c_ge_lookup`

The code is the decoded bytes (`code`), cut into its straight-line pieces (`sl`); no proof names
a scratch register. Values come from the symbolic executor: a piece's effect on a word of memory
or a register is `norm` of its symbolic run, compared by `decide` with a specification term
(`maskS`, `orS`, …) over the piece's entry registers and memory.

`lookupR` is the routine's contract; `lk_ok` and `code_at` decide its checks in each build. The
pieces of its call lemma: `hdr_ok` (the header's slots), `loopJ` with `Jv` (the six passes of the
block loop, each a `pass_ok`/`blk_ok` block whose words `or_sel` selects by the digit).
-/

namespace M0Crypto.Release.Ed25519Lookup

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Artifacts

/-! ## Symbolic effects -/

/-- The store addresses of a symbolic memory, normalised. -/
def normMem : SMem → SMem
  | .mem0 => .mem0
  | .w32 m a v => .w32 (normMem m) (norm a) v
  | .w16 m a v => .w16 (normMem m) (norm a) v
  | .w8 m a v => .w8 (normMem m) (norm a) v

theorem normMem_sound (s : State) : ∀ m : SMem, (normMem m).denote s = m.denote s
  | .mem0 => rfl
  | .w32 m a v | .w16 m a v | .w8 m a v => by
    simp only [normMem, SMem.denote, normMem_sound s m, norm_sound]

/-- A word of memory after the block `is`, at `aS` in its entry state, is `spec`. -/
theorem sym_rd {is : List Instr} (hf : is.all Instr.falls = true) (aS spec : SExpr)
    (h : rdW (normMem (symExec is SState.init).mem) (norm aS) = norm spec) (s : State) :
    read32 (execAll is s).mem (aS.denote s) = spec.denote s := by
  rw [← norm_sound s spec, ← h, rdW_sound, norm_sound, normMem_sound,
    mem_execAll_normK is hf [] s (by simp)]
  rfl

/-- A register after the block `is` is `spec`. -/
theorem sym_reg {is : List Instr} (hf : is.all Instr.falls = true) (r : Reg) (spec : SExpr)
    (h : norm ((symExec is SState.init).regs r) = norm spec) (s : State) :
    (execAll is s).regs r = spec.denote s := by
  rw [execAll_regs_normK is hf [] s (by simp) r, ← norm_sound s spec]
  exact congrArg (fun e => SExpr.denote s e) h

/-- The `Z` flag after the block `is` tests `x`. -/
theorem sym_z {is : List Instr} (hf : is.all Instr.falls = true) (x : SExpr)
    (h : (symExec is SState.init).z = .isZero x) (s : State) :
    (execAll is s).z = (x.denote s == 0#32) := by
  have e := congrArg State.z (symExec_sound is (sound_all hf) s SState.init)
  rw [SState.init_denote] at e
  rw [← e]; show SBool.denote s (symExec is SState.init).z = _; rw [h]; rfl

/-! ## The code -/

/-- `m0c_ge_lookup` without its literal pool, decoded from the bytes. -/
def code : List Instr :=
  (decodeN 300 432 (Ed25519Compact.bytes.drop Ed25519Compact.ge_lookup)).getD []

/-- The `n` instructions from instruction `a`. -/
def sl (a n : Nat) : List Instr := (code.drop a).take n

/-- The frame slots of `emit_lookup`: `OUT`, `ROW`, `NEG`, `BLK`, `Z`, the masks `M`. -/
def oOut : Nat := 0
def oRow : Nat := 4
def oNeg : Nat := 8
def oBlk : Nat := 12
def oZ : Nat := 16
def oM : Nat := 24

/-! ## Specification terms -/

def kS (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)
/-- The word at `sp + off` at entry. -/
def ldS (off : Nat) : SExpr := .ld32 .mem0 (.add (.reg0 13) (kS off))
def subS (x : SExpr) (n : Nat) : SExpr := .awc x (.const (~~~(BitVec.ofNat 32 n))) (.const true)
def rsbS (x : SExpr) : SExpr := .awc (.not x) (kS 0) (.const true)
/-- The sign mask, `|d|`, the zero flag and the mask of entry `k` of the digit `d`. -/
def sgnS (d : SExpr) : SExpr := rsbS (.lsr d 31)
def absS (d : SExpr) : SExpr := .awc (.xor d (sgnS d)) (.not (sgnS d)) (.const true)
def zS (d : SExpr) : SExpr := .lsr (subS (absS d) 1) 31
def maskS (k : Nat) (d : SExpr) : SExpr := rsbS (.lsr (subS (.xor (kS k) (absS d)) 1) 31)
/-- The address of block `BLK` of a table at slot `off`. -/
def blkS (off : Nat) : SExpr := .awc (ldS off) (.lsl (ldS oBlk) 4) (.const false)
/-- Word `i` of entry `k` in block `BLK`. -/
def wS (k i : Nat) : SExpr := .ld32 .mem0 (.add (blkS oRow) (kS (96 * k + 4 * i)))
/-- Word `i` of a block: the OR over the entries `k < K` of their word and mask. -/
def orS (i : Nat) : Nat → SExpr
  | 0 => kS 0
  | k + 1 => .or (orS i k) (.and (wS k i) (ldS (oM + 4 * k)))

/-- Header: the slot values. -/
theorem hdr_ok : (sl 2 60).all Instr.falls = true ∧
    rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS oOut))) = norm (.reg0 0) ∧
    rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS oRow))) = norm (.reg0 1) ∧
    rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS oNeg))) = norm (sgnS (.reg0 2)) ∧
    rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS oZ))) = norm (zS (.reg0 2)) ∧
    rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS oBlk))) = norm (kS 0) ∧
    ∀ k < 8, rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS (oM + 4 * k)))) =
      norm (maskS (k + 1) (.reg0 2)) := by decide +kernel

/-- A block of the table pass: its four words. -/
theorem blk_ok : (sl 62 108).all Instr.falls = true ∧ ∀ i < 4,
    rdW (normMem (symExec (sl 62 108) SState.init).mem) (norm (.add (blkS oOut) (kS (4 * i)))) =
      norm (orS i 8) := by decide +kernel

/-- The counter after a pass. -/
def incS : SExpr := .awc (ldS oBlk) (kS 1) (.const false)

/-- A pass: the atoms of its first block's addresses, and the counter step of its tail. -/
theorem pass_ok : Routine.traceOkE (sl 62 108) [.reg0 13, blkS oRow, blkS oOut] = true ∧
    (sl 170 4).all Instr.falls = true ∧ (symExec (sl 170 4) SState.init).z = .isZero (subS incS 6) ∧
    rdW (normMem (symExec (sl 170 4) SState.init).mem) (norm (.add (.reg0 13) (kS oBlk))) = norm incS := by
  decide +kernel

/-- The exit: digit 0's identity words (word 0 by the atoms, word 8 from `r0`, `r1`), then the
swap's mask and counter. -/
theorem fix_ok : (sl 176 5).all Instr.falls = true ∧ Routine.traceOkE (sl 176 5) [.reg0 13, ldS oOut] = true ∧
    rdW (normMem (symExec (sl 176 5) SState.init).mem) (norm (.add (ldS oOut) (kS 0))) =
      norm (.or (.ld32 .mem0 (.add (ldS oOut) (kS 0))) (ldS oZ)) ∧
    norm ((symExec (sl 176 5) SState.init).regs 0) = norm (ldS oOut) ∧
    norm ((symExec (sl 176 5) SState.init).regs 1) = norm (ldS oZ) ∧
    (sl 181 3).all Instr.falls = true ∧
    rdW (normMem (symExec (sl 181 3) SState.init).mem) (norm (.add (.reg0 0) (kS 32))) =
      norm (.or (.ld32 .mem0 (.add (.reg0 0) (kS 32))) (.reg0 1)) ∧
    (sl 184 2).all Instr.falls = true ∧ norm ((symExec (sl 184 2) SState.init).regs 3) = norm (ldS oNeg) ∧
    norm ((symExec (sl 184 2) SState.init).regs 7) = norm (kS 8) := by
  decide +kernel

/-- Word `a` (0 or 32) of a swap pass: words 0 and 32 swap where the mask in `r3` is set. -/
def swS (a : Nat) : SExpr :=
  .xor (.ld32 .mem0 (.add (.reg0 0) (kS a)))
    (.and (.xor (.ld32 .mem0 (.add (.reg0 0) (kS 0))) (.ld32 .mem0 (.add (.reg0 0) (kS 32)))) (.reg0 3))

/-- A swap pass: its two words, the pointer, the mask and the counter. -/
theorem swap_ok : (sl 186 11).all Instr.falls = true ∧
    rdW (normMem (symExec (sl 186 11) SState.init).mem) (norm (.add (.reg0 0) (kS 0))) = norm (swS 0) ∧
    rdW (normMem (symExec (sl 186 11) SState.init).mem) (norm (.add (.reg0 0) (kS 32))) = norm (swS 32) ∧
    norm ((symExec (sl 186 11) SState.init).regs 0) = norm (.awc (.reg0 0) (kS 4) (.const false)) ∧
    norm ((symExec (sl 186 11) SState.init).regs 3) = norm (.reg0 3) ∧
    norm ((symExec (sl 186 11) SState.init).regs 7) = norm (subS (.reg0 7) 1) ∧
    (symExec (sl 186 11) SState.init).z = .isZero (subS (.reg0 7) 1) := by
  decide +kernel

/-! ## The digit -/

/-- A state that holds nothing; closed terms denote alike in every state. -/
def st0 : State := ⟨fun _ => 0, false, false, false, false, fun _ => 0⟩

/-- `|d|` of a digit `d` with `d + 8 ≤ 16`, and its sign. -/
def dIdx (d : Word) : Nat := if (d + 8#32).toNat < 8 then 8 - (d + 8#32).toNat else (d + 8#32).toNat - 8
def dNeg (d : Word) : Bool := (d + 8#32).toNat < 8

theorem digit_facts : ∀ n < 17, (sgnS (.const (BitVec.ofNat 32 n - 8#32))).denote st0 =
      (if n < 8 then BitVec.allOnes 32 else 0) ∧
    (zS (.const (BitVec.ofNat 32 n - 8#32))).denote st0 = (if n = 8 then 1#32 else 0#32) ∧
    ∀ k < 8, (maskS (k + 1) (.const (BitVec.ofNat 32 n - 8#32))).denote st0 =
      if dIdx (BitVec.ofNat 32 n - 8#32) = k + 1 then BitVec.allOnes 32 else 0 := by decide +kernel

theorem digit_of {d : Word} (h : (d + 8#32).toNat ≤ 16) :
    ∃ n < 17, d = BitVec.ofNat 32 n - 8#32 :=
  ⟨(d + 8#32).toNat, by omega, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_sub_cancel]⟩

/-- **The OR over the first `K` entries** is the word of entry `|d| - 1` if `1 ≤ |d| ≤ K`, else 0. -/
theorem or_sel {u : State} {d : Word} (hd : (d + 8#32).toNat ≤ 16)
    (hm : ∀ k < 8, (ldS (oM + 4 * k)).denote u = (maskS (k + 1) (.const d)).denote st0) (i : Nat) :
    ∀ K ≤ 8, (orS i K).denote u =
      if 1 ≤ dIdx d ∧ dIdx d ≤ K then (wS (dIdx d - 1) i).denote u else 0
  | 0, _ => by simp [orS, kS, SExpr.denote]; omega
  | K + 1, hK => by
    obtain ⟨n, hn, rfl⟩ := digit_of hd
    have e := (digit_facts n hn).2.2 K (by omega)
    simp only [orS, SExpr.denote]
    rw [or_sel hd hm i K (by omega), hm K (by omega), e]
    generalize dIdx (BitVec.ofNat 32 n - 8#32) = x
    by_cases h : x = K + 1
    · subst h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(1 ≤ K + 1 ∧ K + 1 ≤ K) by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (show 1 ≤ K + 1 ∧ K + 1 ≤ K + 1 by omega)),
        BitVec.and_allOnes, Nat.add_sub_cancel]; simp
    · have h1 : (1 ≤ x ∧ x ≤ K + 1) ↔ (1 ≤ x ∧ x ≤ K) := by omega
      simp only [h, h1, ite_false]; simp

/-- The zero flag and the sign mask of a digit, and `|d| ≤ 8`. -/
theorem digit_exit {d : Word} (h : (d + 8#32).toNat ≤ 16) :
    (zS (.const d)).denote st0 = (if dIdx d = 0 then 1#32 else 0#32) ∧
    (sgnS (.const d)).denote st0 = (if dNeg d then BitVec.allOnes 32 else 0) ∧ dIdx d ≤ 8 := by
  obtain ⟨n, hn, rfl⟩ := digit_of h
  revert n; decide +kernel

/-- After the swap: `r0 = out + 96`. -/
theorem neg_ok : (sl 198 2).all Instr.falls = true ∧
    norm ((symExec (sl 198 2) SState.init).regs 0) = norm (.awc (ldS oOut) (kS 96) (.const false)) := by
  decide +kernel

/-- The glue of the `fe_sub` call: `r1` = the zero element, `r2 = out + 64`. -/
theorem sub_ok : (sl 201 3).all Instr.falls = true ∧
    norm ((symExec (sl 201 3) SState.init).regs 0) = norm (.reg0 0) ∧
    norm ((symExec (sl 201 3) SState.init).regs 1) = norm (.add (.reg0 1) (.add (.reg0 15) (kS 4))) ∧
    norm ((symExec (sl 201 3) SState.init).regs 2) = norm (.awc (ldS oOut) (kS 64) (.const false)) ∧
    norm ((symExec (sl 201 3) SState.init).regs 13) = norm (.reg0 13) := by
  decide +kernel

/-- The glue of the `cmov` call: `r0 = out + 64`, `r1 = out + 96`, 8 words, the sign mask. -/
theorem cmv_ok : (sl 205 6).all Instr.falls = true ∧
    norm ((symExec (sl 205 6) SState.init).regs 0) = norm (.awc (ldS oOut) (kS 64) (.const false)) ∧
    norm ((symExec (sl 205 6) SState.init).regs 1) =
      norm (.awc (.awc (.awc (ldS oOut) (kS 64) (.const false)) (kS 0) (.const false)) (kS 32) (.const false)) ∧
    norm ((symExec (sl 205 6) SState.init).regs 2) = norm (kS 8) ∧
    norm ((symExec (sl 205 6) SState.init).regs 3) = norm (ldS oNeg) ∧
    norm ((symExec (sl 205 6) SState.init).regs 13) = norm (.reg0 13) := by
  decide +kernel

/-! ## A loop closed by `b<cond> ex; b o` -/

open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Routine

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The decided checks of the exit branch at `ob` to `ex` and the `b` at `ob + 2` back to `o`. -/
def loopJOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o ob ex d N : Nat) (imm : BitVec 8) (imm11 : BitVec 11) : Bool :=
  ob % 2 == 0 && rangesSub [(ob, ob + 4)] cs && decide (ob + 4 ≤ BS) &&
  decide (BitVec.ofNat 32 ob + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 ex) &&
  decide (BitVec.ofNat 32 (ob + 2) + 4#32 + (imm11 ++ 0#1).signExtend 32 = BitVec.ofNat 32 o) &&
  decide (d ≤ N)

/-- The trace of pass `j` of `n`: the body, the exit branch and, but for the last pass, the `b`. -/
def passTr (base : Word) (Φb : Nat → TrP) (n ob : Nat) (cond : BitVec 4) (imm : BitVec 8)
    (imm11 : BitVec 11) (j : Nat) : TrP :=
  Tr.cat (Φb j) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 ob, .bcond cond imm, []⟩])
    (Tr.cond (decide (j + 1 = n)) (Tr.is []) (Tr.is [⟨base + BitVec.ofNat 32 (ob + 2), .b imm11, []⟩])))

/-- **A counted loop** whose body runs from `o` to the branch `b<cond> ex` at `ob`, taken exactly
after pass `n - 1`, followed by `b o`. `I j` holds before pass `j`. -/
theorem loopJ {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {Q : State → Prop}
    {Φb : Nat → TrP} {Ψx : TrP} {o ob ex d : Nat} (F : Caller base sp0 N Wc) (cond : BitVec 4)
    (imm : BitVec 8) (imm11 : BitVec 11) (hbr : instrAt B ob = some (.bcond cond imm))
    (hb : instrAt B (ob + 2) = some (.b imm11)) (n : Nat) (I : Nat → State → Prop)
    (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v))
    (hbody : ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t (fun u =>
        u.pc = base + BitVec.ofNat 32 ob ∧ u.regs 13 = sp0 - BitVec.ofNat 32 d ∧
        CodeAt u.mem base B ∧ I (j + 1) u ∧ condPassed cond u = decide (j + 1 = n)) (Φb j))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 ex → I n t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (hok : loopJOk cs o ob ex d N imm imm11 = true) :
    ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (passTr base Φb n ob cond imm imm11) j (n - j) Ψx) := by
  simp only [loopJOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hob, hcs⟩, hsz⟩, ht⟩, ht2⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have h15 : ∀ (u : State) (v : Word), (u.setReg 15 v).regs 13 = u.regs 13 := fun _ _ => by
    simp [State.setReg]
  have hpc15 : ∀ (u : State) (v : Word), (u.setReg 15 v).pc = v := fun _ _ => by
    simp [State.setReg, State.pc]
  have hP : ∀ (u : State) (x : Nat) (i : Instr), x = ob ∨ x = ob + 2 → u.pc = base + BitVec.ofNat 32 x →
      u.regs 13 = sp0 - BitVec.ofNat 32 d →
      Step (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u ⟨u.pc, i, []⟩ :=
    fun u x i hx hpu hu13 => ⟨by rw [hpu]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self
      (by omega) (by omega)), fun y hy => absurd hy (writes_nil y),
      fun y hy => absurd hy (reads_nil y), by rw [hu13]; exact ⟨d, hd, rfl⟩⟩
  suffices H : ∀ rem j t, rem + j + 1 = n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (passTr base Φb n ob cond imm imm11) j (rem + 1) Ψx) from
    fun j t hj => by rw [show n - j = (n - j - 1) + 1 by omega]; exact H (n - j - 1) j t (by omega)
  intro rem
  induction rem with
  | zero =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := true) hb2 ob ex cond imm hpu hob hbr (by omega) ht
        (hP u ob _ (.inl rfl) hpu hu13) (by rw [hcp]; simp; omega)
        (fun _ => hexit _ (hpc15 _ _) (by rw [show n = j + 1 by omega]; exact hpcI _ _ _ hIu)
          (by rw [h15]; exact hu13) hcu) (ΨF := Ψx)
        fun hF => absurd (hcp ▸ hF) (by simp; omega)) (fun _ _ h => h) (fun _ h => h) ?_
    rintro _ ⟨a, _, rfl, ha, b, c, rfl, hb', hc'⟩
    exact ⟨a ++ b, c, by simp, ⟨a, b, rfl, ha, b, [], by simp, hb',
      fun _ => rfl, fun h => absurd h (by simp; omega)⟩, hc'.1 rfl⟩
  | succ rem ih =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := false) hb2 ob ex cond imm hpu hob hbr (by omega) ht
        (hP u ob _ (.inl rfl) hpu hu13) (by rw [hcp]; simp; omega) (ΨT := Ψx)
        (fun hT => absurd (hcp ▸ hT) (by simp; omega)) fun _ =>
          ReachT.b hb2 (ob + 2) o imm11 (by rw [hpc15]) (by omega) hb (by omega) ht2
            (hP _ (ob + 2) _ (.inr rfl) (by rw [hpc15]) (by rw [h15]; exact hu13))
            (ih (j + 1) _ (by omega) (hpc15 _ _) (hpcI _ _ _ (hpcI _ _ _ hIu))
              (by rw [h15, h15]; exact hu13) hcu)) (fun _ _ h => h) (fun _ h => h) ?_
    rintro _ ⟨a, _, rfl, ha, b, c, rfl, hb', hc'⟩
    obtain ⟨e, f, rfl, he, hf⟩ := hc'.2 rfl
    exact ⟨a ++ (b ++ e), f, by simp, ⟨a, b ++ e, rfl, ha, b, e, rfl, hb',
      fun h => absurd h (by simp; omega), fun _ => he⟩, hf⟩

end

/-! ## The contract -/

open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Ed25519WordLoop (wordR wordPub sel)

/-- Word `i` of the niels entry `a` of the row at `row`; entry 0 is the identity `(1, 1, 0)`. -/
def ent (m : Mem) (row : Word) (a i : Nat) : Word :=
  if a = 0 then (if i = 0 ∨ i = 8 then 1#32 else 0#32)
  else read32 m (row + BitVec.ofNat 32 (96 * (a - 1) + 4 * i))

/-- The third element (`2 d x y`) of the niels entry `a`. -/
def tdX (m : Mem) (row : Word) (a : Nat) : Int :=
  if a = 0 then 0 else feVal m (row + BitVec.ofNat 32 (96 * (a - 1) + 64))

/-- **`m0c_ge_lookup`** at `o`, its code and its callees' within `cs`: `out = r0` (32 words, the
last 8 scratch) receives the niels entry `|d|` of the row `r1` (8 entries of 24 words) for the
digit `d = r2`, `-8 ≤ d ≤ 8`; for `d < 0` its first two elements swap and the third is negated. -/
def lookupR (o : Nat) (cs : List (Nat × Nat)) : Routine where
  entry := o
  code := cs
  stack := 64
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧
    (s.regs 2 + 8#32).toNat ≤ 16 ∧ Disj (s.regs 0) 128 (s.regs 1) 768
  wr := fun s => [⟨s.regs 0, 128⟩]
  rd := fun s => [⟨s.regs 1, 768⟩, ⟨s.regs 0, 128⟩]
  Post := fun s m _ => (∀ i < 8,
      read32 m (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
        ent s.mem (s.regs 1) (dIdx (s.regs 2)) (if dNeg (s.regs 2) then i + 8 else i) ∧
      read32 m (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) =
        ent s.mem (s.regs 1) (dIdx (s.regs 2)) (if dNeg (s.regs 2) then i else i + 8)) ∧
    ModP (feVal m (s.regs 0 + 64#32))
      (if dNeg (s.regs 2) then -tdX s.mem (s.regs 1) (dIdx (s.regs 2)) else tdX s.mem (s.regs 1) (dIdx (s.regs 2)))
  clob := hiRegs

/-- The public values of `m0c_ge_lookup`: `out`, the row and `sp` (not the digit). -/
def lookupPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 1, s.regs 13]

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem sl_split (a n m b k : Nat) (hb : a + n = b) (hk : n + m = k) : sl a k = sl a n ++ sl b m := by
  subst hb hk; rw [sl, sl, sl, List.take_add, List.drop_drop]

theorem shl4 (j : Nat) : BitVec.ofNat 32 j <<< 4 = BitVec.ofNat 32 (16 * j) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem maskS_reg (k : Nat) (u : State) :
    (maskS k (.reg0 2)).denote u = (maskS k (.const (u.regs 2))).denote st0 := rfl

/-- Offset of instruction `i`. -/
def off (i : Nat) : Nat := seqSize (code.take i)

theorem seqAt_sl {o : Nat} (h : seqAt B o code = true) (a n : Nat) :
    seqAt B (o + off a) (sl a n) = true := by
  have e : code = code.take a ++ (sl a n ++ (code.drop a).drop n) := by
    rw [sl, List.take_append_drop, List.take_append_drop]
  rw [e, seqAt_append, seqAt_append] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1

theorem off_add (a n : Nat) : off a + seqSize (sl a n) = off (a + n) := by
  rw [off, off, sl, List.take_add, seqSize_append]

/-- The immediates of the branches at instruction `i`. -/
def blOf (i : Nat) : BitVec 25 := match code.getD i (.b 0) with | .bl x => x | _ => 0
def bcOf (i : Nat) : BitVec 8 := match code.getD i (.b 0) with | .bcond _ x => x | _ => 0
def bOf (i : Nat) : BitVec 11 := match code.getD i (.b 0) with | .b x => x | _ => 0

/-- The little-endian word at the head of `bs`. -/
def wordAt (bs : List (BitVec 8)) : Word := bs.getD 3 0 ++ bs.getD 2 0 ++ bs.getD 1 0 ++ bs.getD 0 0

/-- The block loop's invariant before pass `j`: the counter slot holds `j`, and the output holds
the first `4 j` words of the selected entry (zero for digit `0`). -/
def Jv (sp out row d : Word) (m1 m0 : Mem) (j : Nat) (u : State) : Prop :=
  MemEq [⟨sp + BitVec.ofNat 32 oBlk, 4⟩, ⟨out, 16 * j⟩] m1 u.mem ∧ read32 u.mem (sp + BitVec.ofNat 32 oBlk) = BitVec.ofNat 32 j ∧
  ∀ i < 4 * j, read32 u.mem (out + BitVec.ofNat 32 (4 * i)) =
    if 1 ≤ dIdx d ∧ dIdx d ≤ 8 then read32 m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 4 * i)) else 0

theorem Jv_setReg {sp out row d : Word} {m1 m0 : Mem} {j : Nat} {u : State} {r : Reg} {v : Word}
    (h : Jv sp out row d m1 m0 j u) : Jv sp out row d m1 m0 j (u.setReg r v) := h

/-- The swap loop's invariant before pass `j`: `r0` at word `j`, the mask `κ` in `r3`, the count
in `r7`, and words `i < j` of the two halves at `out` swapped under `κ` (from `m0`). -/
def SwI (out κ : Word) (m0 : Mem) (j : Nat) (v : State) : Prop :=
  v.regs 0 = out + BitVec.ofNat 32 (4 * j) ∧ v.regs 3 = κ ∧ v.regs 7 = BitVec.ofNat 32 (8 - j) ∧
  MemEq [⟨out, 64⟩] m0 v.mem ∧ ∀ i < 8,
    read32 v.mem (out + BitVec.ofNat 32 (4 * i)) = (if i < j then sel κ (read32 m0 (out + BitVec.ofNat 32 (4 * i)))
      (read32 m0 (out + BitVec.ofNat 32 (32 + 4 * i))) else read32 m0 (out + BitVec.ofNat 32 (4 * i))) ∧
    read32 v.mem (out + BitVec.ofNat 32 (32 + 4 * i)) = (if i < j then sel κ (read32 m0 (out + BitVec.ofNat 32 (32 + 4 * i)))
      (read32 m0 (out + BitVec.ofNat 32 (4 * i))) else read32 m0 (out + BitVec.ofNat 32 (32 + 4 * i)))

theorem SwI_setReg {out κ : Word} {m0 : Mem} {j : Nat} {u : State} {v : Word}
    (h : SwI out κ m0 j u) : SwI out κ m0 j (u.setReg 15 v) := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by simp [State.setReg, a], by simp [State.setReg, b], by simp [State.setReg, c], d, e⟩

/-- The decided checks of `m0c_ge_lookup` at `o` in the code `cs`, calling `fe_sub` (`szS` bytes)
at `oS` and `cmov` (`szC` bytes) at `oC`, with the zero element at `oZ`. -/
def lkOk (cs : List (Nat × Nat)) (o oS szS oC szC oZ : Nat) : Bool :=
  o % 4 == 0 && rangesSub [(o, o + 432)] cs && decide (o + 432 ≤ BS) &&
  loopJOk cs (o + off 62) (o + off 174) (o + off 176) 60 64 (bcOf 174) (bOf 175) &&
  loopOk cs (o + off 186) (o + off 197) 60 64 (bcOf 197) &&
  glueOk cs (sl 2 60) (o + off 2) 60 64 [(13, 4)] [((13 : Reg), 0#32, 56)] [] &&
  sglueOk cs (sl 62 108) (o + off 62) 60 64 [(.reg0 13, 4), (blkS oRow, 4), (blkS oOut, 4)]
    [(blkS oOut, 16)] [(.reg0 13, 56), (blkS oRow, 688)] &&
  glueOk cs (sl 170 4) (o + off 170) 60 64 [(13, 4)] [((13 : Reg), BitVec.ofNat 32 oBlk, 4)] [((13 : Reg), BitVec.ofNat 32 oBlk, 4)] &&
  sglueOk cs (sl 176 5) (o + off 176) 60 64 [(.reg0 13, 4), (ldS oOut, 4)] [(ldS oOut, 4)]
    [(.reg0 13, 56), (ldS oOut, 4)] &&
  glueOk cs (sl 181 3) (o + off 181) 60 64 [(0, 4)] [((0 : Reg), 32#32, 4)] [((0 : Reg), 32#32, 4)] &&
  glueOk cs (sl 184 2) (o + off 184) 60 64 [(13, 4)] [] [((13 : Reg), BitVec.ofNat 32 oNeg, 4)] &&
  glueOk cs (sl 186 11) (o + off 186) 60 64 [(0, 4)] [((0 : Reg), 0#32, 4), ((0 : Reg), 32#32, 4)]
    [((0 : Reg), 0#32, 4), ((0 : Reg), 32#32, 4)] &&
  glueOk cs (sl 198 2) (o + off 198) 60 64 [(13, 4)] [] [((13 : Reg), BitVec.ofNat 32 oOut, 4)] &&
  litOk cs (o + off 200) 60 64 1 7 &&
  siteOk cs (fieldR oS szS 4 true (· - ·)) (sl 201 3) (o + off 201) 60 64 (blOf 204) [(13, 4)] []
    [((13 : Reg), BitVec.ofNat 32 oOut, 4)] &&
  siteOk cs (wordR oC szC 2 true true (fun _ => True) sel [4, 5, 6, 7]) (sl 205 6) (o + off 205) 60 64
    (blOf 211) [(13, 4)] [] [((13 : Reg), BitVec.ofNat 32 oOut, 4), ((13 : Reg), BitVec.ofNat 32 oNeg, 4)] &&
  decide (oZ + 32 ≤ BS) && oZ % 4 == 0 && ((B.drop oZ).take 32).all (· == 0) &&
  wordAt (B.drop (litOff (o + off 200) 7)) + BitVec.ofNat 32 (o + off 201 + 4) == BitVec.ofNat 32 oZ

/-- A code word from the bytes after its offset. -/
theorem codeWord_drop (x : Nat) : Frame.codeWord x = wordAt (B.drop x) := by
  simp [Frame.codeWord, wordAt, List.getD, List.getElem?_drop]

/-- The code words of a zero run of 32 bytes. -/
theorem codeWord_zero {x : Nat} (h : ((B.drop x).take 32).all (· == 0) = true) {i : Nat} (hi : i < 8) :
    Frame.codeWord (x + 4 * i) = 0 := by
  have hb : ∀ k < 32, B.getD (x + k) 0 = 0 := fun k hk => by
    rw [List.getD_eq_getElem?_getD]
    cases hx : B[x + k]? with
    | none => rfl
    | some b =>
      have hm : b ∈ (B.drop x).take 32 :=
        List.mem_iff_getElem?.mpr ⟨k, by simp [List.getElem?_take, hk, List.getElem?_drop, hx]⟩
      simpa using List.all_eq_true.mp h b hm
  simp (disch := omega) only [Frame.codeWord, Nat.add_assoc, hb]; rfl

/-- A field element whose eight words are zero. -/
theorem feVal_zeroes {m : Mem} {a : Word} (h : ∀ i < 8, read32 m (a + BitVec.ofNat 32 (4 * i)) = 0) :
    feVal m a = 0 := by
  unfold feVal
  rw [List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)]]
  decide

theorem feVal_congr {m m' : Mem} {a b : Word}
    (h : ∀ i < 8, read32 m (a + BitVec.ofNat 32 (4 * i)) = read32 m' (b + BitVec.ofNat 32 (4 * i))) :
    feVal m a = feVal m' b := by
  unfold feVal; congr 1; exact List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)]


end

open M0Crypto.Release.Ed25519 (Build)

/-- The code `m0c_ge_lookup` executes: its own body and its callees `m0c_fe_sub` and `m0c_cmov`.
A caller's return address must lie outside it, so callers in the unit are admitted. -/
def lookupCs : List (Nat × Nat) :=
  [(Ed25519Compact.ge_lookup, Ed25519Compact.ge_lookup + seqSize code),
   (Ed25519Compact.fe_sub,
    Ed25519Compact.fe_sub + seqSize (Ed25519FeAddSub.wrap Field25519AddSub.feSubBody)),
   (Ed25519Compact.cmov,
    Ed25519Compact.cmov + seqSize (Ed25519WordLoop.wloop [] Ed25519WordLoop.cmovBody 0xf3))]

set_option maxRecDepth 20000 in
/-- The decided checks of `m0c_ge_lookup` in each build. -/
theorem lk_ok (b : Build) : letI := b.codeBytes; lkOk lookupCs Ed25519Compact.ge_lookup Ed25519Compact.fe_sub
    (seqSize (Ed25519FeAddSub.wrap Field25519AddSub.feSubBody)) Ed25519Compact.cmov
    (seqSize (Ed25519WordLoop.wloop [] Ed25519WordLoop.cmovBody 0xf3)) Ed25519Compact.ed_zero = true := by
  cases b <;> decide +kernel

set_option maxRecDepth 20000 in
/-- `m0c_ge_lookup`'s code in each build. -/
theorem code_at (b : Build) : letI := b.codeBytes; seqAt b.bytes Ed25519Compact.ge_lookup code = true := by
  cases b <;> (rw [seqAt_eq_scan]; decide +kernel)

end M0Crypto.Release.Ed25519Lookup
