import M0Crypto.Release.Ed25519SignRun
import M0Crypto.Release.Ed25519CallProgAdapt
import M0Crypto.Release.Ed25519Lookup

/-!
# `m0c_sha512_init`'s adapter

The satisfiability witness for `Callees`: the adapter of `sha512_init` from the bytes of each
build, as the `.init` field of `Callees` (`initAd`). The routine is `push {lr}`, a head
(`mov r12, r0; adds r0, #4`), a literal load and `add r1, pc` that address the IV table in the
code, four pairs `ldm r1!, {r2-r5}; stm r0!, {r2-r5}`, a tail that stores the count 0, and
`pop {pc}`. Each pair copies four code words (`pair_glue`); the code stays in memory, so each
pair reads the table through `CodeAt`.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519Lookup (sym_rd sym_reg kS wordAt codeWord_drop normMem)
open M0Crypto.Artifacts.Ed25519Compact (sha512_init)

/-- Word `i` of the initial chaining value in the context: `H0[i / 2]`, low word first. -/
def ivWord (i : Nat) : Word :=
  let w := Spec.Sha512.H0.getD (i / 2) 0
  if i % 2 = 0 then w.extractLsb' 0 32 else w.extractLsb' 32 32

/-- A context just after `init`: the count 0, then the initial chaining value. -/
def CtxInit (m : Mem) (a : Word) : Prop :=
  read32 m a = 0 ∧ ∀ i < 16, read32 m (a + BitVec.ofNat 32 (4 + 4 * i)) = ivWord i

/-- The table's 64 bytes: the words `ivWord`, little-endian. -/
def ivBytes : List (BitVec 8) :=
  (List.range 16).flatMap fun i =>
    [(ivWord i).extractLsb' 0 8, (ivWord i).extractLsb' 8 8, (ivWord i).extractLsb' 16 8,
      (ivWord i).extractLsb' 24 8]

def headG : List Instr := [.movHi 12 0, .addImm8 0 4]
def litG : List Instr := [.ldrLit 1 7]
def pcG : List Instr := [.addPc 1]
/-- The registers of a pair, and the bytes it copies. -/
def pairL : BitVec 8 := 0x3c
def pairB : Nat := 4 * bitCount pairL
def pairG : List Instr := [.ldm 1 pairL, .stm 0 pairL]
def nPairs : Nat := 4
def pairsG : Nat → List Instr
  | 0 => []
  | n + 1 => pairG ++ pairsG n
def tailG : List Instr := [.movHi 0 12, .movImm 1 0, .memImm .str 1 0 0]

/-- The routine's instructions from its entry. -/
def initG : List Instr :=
  [.push 0 true] ++ (headG ++ (litG ++ (pcG ++ (pairsG nPairs ++ (tailG ++ [.pop 0 true])))))

/-! The pieces' offsets from the entry `o`, each after the one before. -/
def oHead (o : Nat) : Nat := o + seqSize [.push 0 true]
def oLitI (o : Nat) : Nat := oHead o + seqSize headG
def oPc (o : Nat) : Nat := oLitI o + seqSize litG
def oPair (o j : Nat) : Nat := oPc o + seqSize pcG + j * seqSize pairG
def oTail (o : Nat) : Nat := oPair o nPairs
def oPop (o : Nat) : Nat := oTail o + seqSize tailG
def oEnd (o : Nat) : Nat := oPop o + seqSize [.pop 0 true]

/-- `m0c_sha512_init` at `o`, running the code `cs`. -/
def initR (o : Nat) (cs : List (Nat × Nat)) : Routine where
  entry := o
  code := cs
  stack := 4
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0
  wr := fun s => [⟨s.regs 0, ctxSize⟩]
  rd := fun _ => []
  Post := fun s m _ => CtxInit m (s.regs 0)
  clob := Ed25519Routines.hiRegs

def initPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 13]

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The decided checks at `o` with the table at `oT`: the glue blocks and the literal lie in
`cs`, the literal addresses the table, and the table holds the IV. -/
def initOk {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (cs : List (Nat × Nat)) (o oT : Nat) :
    Bool :=
  glueOk cs headG (oHead o) 4 4 [] [] [] && litOk cs (oLitI o) 4 4 1 7 &&
  glueOk cs pcG (oPc o) 4 4 [] [] [] &&
  (List.range nPairs).all (fun j => glueOk cs pairG (oPair o j) 4 4 [(0, 4), (1, 4)]
    [((0 : Reg), 0#32, pairB)] [((1 : Reg), 0#32, pairB)]) &&
  glueOk cs tailG (oTail o) 4 4 [(12, 4)] [((12 : Reg), 0#32, 4)] [] &&
  rangesSub [(o, oHead o), (oPop o, oEnd o)] cs &&
  (wordAt (B.drop (litOff (oLitI o) 7)) + BitVec.ofNat 32 (oPc o + 4) == BitVec.ofNat 32 oT) &&
  oT % 4 == 0 && decide (oT + nPairs * pairB ≤ BS) && decide (oEnd o ≤ BS) && o % 2 == 0 &&
  (B.drop oT).take (nPairs * pairB) == ivBytes

/-- The table's words. -/
theorem iv_code {oT : Nat} (h : (B.drop oT).take (nPairs * pairB) = ivBytes) {i : Nat}
    (hi : i < nPairs * bitCount pairL) : Frame.codeWord (oT + 4 * i) = ivWord i := by
  have hn : nPairs * pairB = 4 * (nPairs * bitCount pairL) := by simp only [pairB]; ac_rfl
  have e : wordAt (B.drop (oT + 4 * i)) = wordAt (ivBytes.drop (4 * i)) := by
    rw [← h]
    simp only [wordAt, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take]
    simp (disch := omega) only [show ∀ k < 4, 4 * i + k < nPairs * pairB from fun k hk => by omega,
      ite_true, Nat.add_assoc]
  rw [codeWord_drop, e]
  exact (show ∀ i < nPairs * bitCount pairL, wordAt (ivBytes.drop (4 * i)) = ivWord i by decide) i hi

/-- One pair copies its words from `r1` to `r0` and steps both by `pairB`. -/
theorem pair_exec (u : State) :
    (execAll pairG u).regs 0 = u.regs 0 + BitVec.ofNat 32 pairB ∧
    (execAll pairG u).regs 1 = u.regs 1 + BitVec.ofNat 32 pairB ∧
    (execAll pairG u).regs 12 = u.regs 12 ∧
    ∀ k < bitCount pairL, read32 (execAll pairG u).mem (u.regs 0 + BitVec.ofNat 32 (4 * k)) =
      read32 u.mem (u.regs 1 + BitVec.ofNat 32 (4 * k)) := by
  have hf : pairG.all Instr.falls = true := by decide
  have hk : ∀ k < bitCount pairL, rdW (normMem (symExec pairG SState.init).mem)
      (norm (.add (.reg0 0) (kS (4 * k)))) = norm (.ld32 .mem0 (.add (.reg0 1) (kS (4 * k)))) := by
    decide
  exact ⟨sym_reg hf 0 (.add (.reg0 0) (kS pairB)) (by decide) u,
    sym_reg hf 1 (.add (.reg0 1) (kS pairB)) (by decide) u, sym_reg hf 12 (.reg0 12) (by decide) u,
    fun k h => sym_rd hf _ _ (hk k h) u⟩

/-- The copy after `j` pairs: `r0` and `r1` stepped, `r12 = c`, the first `j` pairs' words copied. -/
structure PI (base c : Word) (oT o j : Nat) (sp : Word) (u : State) : Prop where
  pc : u.pc = base + BitVec.ofNat 32 (oPair o j)
  r0 : u.regs 0 = c + BitVec.ofNat 32 (4 + pairB * j)
  r1 : u.regs 1 = base + BitVec.ofNat 32 (oT + pairB * j)
  r12 : u.regs 12 = c
  r13 : u.regs 13 = sp - BitVec.ofNat 32 4
  code : CodeAt u.mem base B
  wd : ∀ i < bitCount pairL * j, read32 u.mem (c + BitVec.ofNat 32 (4 + 4 * i)) = ivWord i

/-- **One pair** of the copy, inside the routine at `o` from the entry state `s`. -/
theorem pair_glue {o oT j : Nat} {cs : List (Nat × Nat)} {base c : Word} {s u : State}
    {Q : State → Prop} {Ψ : TrP} (e : (initR o cs).Entry base s) (hc : s.regs 0 = c) (hj : j < nPairs)
    (hseq : seqAt B (oPair o j) pairG = true)
    (hok : glueOk cs pairG (oPair o j) 4 4 [(0, 4), (1, 4)] [((0 : Reg), 0#32, pairB)]
      [((1 : Reg), 0#32, pairB)] = true)
    (hT : oT + nPairs * pairB ≤ BS) (hT4 : oT % 4 = 0) (hiv : (B.drop oT).take (nPairs * pairB) = ivBytes)
    (h : PI (B := B) base c oT o j (s.regs 13) u)
    (k : ∀ v, PI (B := B) base c oT o (j + 1) (s.regs 13) v →
      ReachFT base ((initR o cs).PcP base) ((initR o cs).RdP base s)
        (Has (lowWin (initR o cs) 0 s :: (initR o cs).wr s)) ((initR o cs).SpP s) v Q Ψ) :
    ReachFT base ((initR o cs).PcP base) ((initR o cs).RdP base s)
      (Has (lowWin (initR o cs) 0 s :: (initR o cs).wr s)) ((initR o cs).SpP s) u Q
      (Tr.cat (Tr.is (blockTr pairG (base + BitVec.ofNat 32 (oPair o j)) [0, 1]
        [c + BitVec.ofNat 32 (4 + pairB * j), base + BitVec.ofNat 32 (oT + pairB * j)])) Ψ) := by
  subst hc
  have F := Caller.of_entry (mask := 0) e
  have hc4 : (s.regs 0).toNat % 4 = 0 := e.pre
  have hsW := e.sepWr; have hroom := e.room; have hb4 := e.base4; have c32 := F.code32
  -- the pair's words lie in the context and the table
  have hm : pairB * j + pairB ≤ pairB * nPairs := by
    rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ hj
  have hB : pairB = 4 * bitCount pairL := rfl
  have hBj : pairB * j = 4 * (bitCount pairL * j) := by rw [hB, Nat.mul_assoc]
  have hw : 0 < bitCount pairL := by decide
  have hjB : 4 + pairB * j + pairB ≤ ctxSize := by
    have : 4 + pairB * nPairs ≤ ctxSize := by decide
    omega
  have hjT : oT + pairB * j + pairB ≤ BS := by rw [Nat.mul_comm] at hT; omega
  simp only [initR, Routine.win, ctxSize] at hsW hroom hjB
  fp_simp at hsW
  obtain ⟨hpc, r0, r1, r12, r13, hcode, hwd⟩ := h
  trefine ReachFT.glue F pairG _ _ _ hseq hpc r13 hcode
    (by glue_tac [r0, r1, initR, lowWin, ctxSize]) (tr_block [0, 1] hpc [r0, r1])
    (fun hpc' h13' hc' hm' => k _ ?_) hok
  obtain ⟨e0, e1, e12, ev⟩ := pair_exec u
  refine ⟨by rw [hpc', oPair, oPair, Nat.add_one_mul, Nat.add_assoc],
    by rw [e0, r0, ofNat_add_assoc, Nat.mul_add_one, Nat.add_assoc],
    by rw [e1, r1, ofNat_add_assoc, Nat.mul_add_one, Nat.add_assoc], by rw [e12, r12], h13', hc',
    fun i hi => ?_⟩
  by_cases hi' : i < bitCount pairL * j
  · rw [hm'.read32 (by simp only [regions, List.map, r0]; fp_tac), hwd i hi']
  · rw [Nat.mul_add_one] at hi
    obtain ⟨x, rfl⟩ : ∃ x, i = bitCount pairL * j + x := ⟨i - bitCount pairL * j, by omega⟩
    have := ev x (by omega)
    rw [r0, r1, ofNat_add_assoc, ofNat_add_assoc] at this
    rw [show 4 + 4 * (bitCount pairL * j + x) = 4 + pairB * j + 4 * x by omega, this,
      Frame.read32_code hcode _ (by omega),
      show oT + pairB * j + 4 * x = oT + 4 * (bitCount pairL * j + x) by omega,
      iv_code hiv ?_]
    have : bitCount pairL * j + bitCount pairL ≤ nPairs * bitCount pairL := by
      rw [← Nat.mul_add_one, Nat.mul_comm nPairs]; exact Nat.mul_le_mul_left _ hj
    omega

/-- The pairs from `o`: pair `j` at `o` plus `j` pairs. -/
theorem pairs_at : ∀ (n o : Nat), seqAt B o (pairsG n) = true →
    ∀ j < n, seqAt B (o + j * seqSize pairG) pairG = true
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, o, h, j, hj => by
    simp only [pairsG, seqAt_append, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using h.1
    · have := pairs_at n _ h.2 j (by omega)
      rw [Nat.add_one_mul, Nat.add_comm (j * seqSize pairG), ← Nat.add_assoc]; exact this

theorem seqSize_pairs : ∀ n, seqSize (pairsG n) = n * seqSize pairG
  | 0 => rfl
  | n + 1 => by simp only [pairsG, seqSize_append, seqSize_pairs n, Nat.succ_mul, Nat.add_comm]

/-- The routine's pieces from its bytes. -/
theorem init_pieces {o : Nat} (hseq : seqAt B o initG = true) :
    instrAt B o = some (.push 0 true) ∧ seqAt B (oHead o) headG = true ∧
    instrAt B (oLitI o) = some (.ldrLit 1 7) ∧ seqAt B (oPc o) pcG = true ∧
    (∀ j < nPairs, seqAt B (oPair o j) pairG = true) ∧ seqAt B (oTail o) tailG = true ∧
    instrAt B (oPop o) = some (.pop 0 true) := by
  simp only [initG, seqAt_append, Bool.and_eq_true] at hseq
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hseq
  rw [seqSize_pairs] at h5
  exact ⟨instrAt_of_seqAt h0, h1, instrAt_of_seqAt h2, h3, pairs_at nPairs _ h4, h5, instrAt_of_seqAt h6⟩

theorem head_exec (t : State) :
    (execAll headG t).regs 0 = t.regs 0 + 4#32 ∧ (execAll headG t).regs 12 = t.regs 0 :=
  ⟨sym_reg (by decide) 0 (.add (.reg0 0) (kS 4)) (by decide +kernel) t,
    sym_reg (by decide) 12 (.reg0 0) (by decide +kernel) t⟩

theorem pc_exec (y : State) :
    (execAll pcG y).regs 0 = y.regs 0 ∧ (execAll pcG y).regs 1 = y.regs 1 + (y.regs 15 + 4#32) ∧
    (execAll pcG y).regs 12 = y.regs 12 :=
  ⟨sym_reg (by decide) 0 (.reg0 0) (by decide +kernel) y,
    sym_reg (by decide) 1 (.add (.reg0 1) (.add (.reg0 15) (kS 4))) (by decide +kernel) y,
    sym_reg (by decide) 12 (.reg0 12) (by decide +kernel) y⟩

theorem tail_exec (v : State) : read32 (execAll tailG v).mem (v.regs 12) = 0 :=
  sym_rd (by decide) (.reg0 12) (kS 0) (by decide +kernel) v

/-- The literal and `add r1, pc` address the table. -/
theorem lit_tab {p oT : Nat} {base cw : Word} (h : cw + BitVec.ofNat 32 (p + 4) = BitVec.ofNat 32 oT) :
    cw + (base + BitVec.ofNat 32 p + 4#32) = base + BitVec.ofNat 32 oT := by
  rw [← h, BitVec.ofNat_add]
  generalize BitVec.ofNat 32 p = q; ac_rfl

/-- `sha512_init`'s effect at public values `P`: from the code, the bytes before the context's
buffer. -/
def initE (base : Word) (P : Nat → Word) : TrP :=
  EffT 4 (Has [codeR base, ⟨P 0, ctxSize⟩]) (Has [codeR base]) (Region (P 0) ctxBuf) (P 1)

theorem has_at {a : Word} {x o m n : Nat} (ho : o < m) (hx : x + m ≤ n) :
    Rgn.Has ⟨a, n⟩ (a + BitVec.ofNat 32 x + BitVec.ofNat 32 o) :=
  ⟨x + o, show x + o < n by omega, by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩

theorem region_has {a y : Word} {m n : Nat} (h : Region a m y) (hm : m ≤ n) : Rgn.Has ⟨a, n⟩ y :=
  ⟨(y - a).toNat, show _ < n by have : (y - a).toNat < m := h; omega,
    by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩

/-- A byte before the buffer lies in the count word or in a pair's words. -/
theorem ctx_parts {a y : Word} (h : Region a ctxBuf y) : (∃ o < 4, y = a + BitVec.ofNat 32 o) ∨
    ∃ j < nPairs, ∃ o < pairB, y = a + BitVec.ofNat 32 (4 + pairB * j) + BitVec.ofNat 32 o := by
  have hd : y = a + BitVec.ofNat 32 (y - a).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have hB : pairB = 16 := by decide
  replace h : (y - a).toNat < 68 := h
  rw [hB, show nPairs = 4 from rfl]
  generalize (y - a).toNat = d at hd h
  subst hd
  by_cases h4 : d < 4
  · exact .inl ⟨d, h4, rfl⟩
  · refine .inr ⟨(d - 4) / 16, by omega, (d - 4) % 16, by omega, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-- Each offset is the entry plus its offset from 0. -/
theorem oPop_eq (o : Nat) : oPop o = o + oPop 0 := by
  simp only [oPop, oTail, oPair, oPc, oLitI, oHead]; omega

/-- **`m0c_sha512_init`'s call lemma** at `o` with its table at `oT`, from the decided checks. -/
noncomputable def init_te {o oT : Nat} {cs : List (Nat × Nat)} (hseq : seqAt B o initG = true)
    (hok : initOk cs o oT = true) : (initR o cs).TE initPub initE := by
  simp only [initOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨gH, gL, gP, gPs, gT, hcs, hlit, hT4, hT, hBS, ho2, hiv⟩ := hok
  obtain ⟨i0, sH, iL, sP, sPs, sT, i32⟩ := init_pieces hseq
  trefine Routine.te_by (fun base s e => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun b P tr h => ?_)
  generalize hPb : initPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 13 = P 1 := by subst hPb; exact ⟨rfl, rfl⟩
  have F := Caller.of_entry (mask := 0) e
  have hc4 : (s.regs 0).toNat % 4 = 0 := e.pre
  have hsW := e.sepWr; have hroom := e.room; have hb4 := e.base4; have c32 := F.code32
  simp only [initR, Routine.win, ctxSize] at hsW hroom
  fp_simp at hsW
  have hP : oPop 0 % 2 = 0 ∧ 2 ≤ oPop 0 ∧ oPop 0 + 2 = oEnd 0 := by decide
  have hE : oEnd o = o + oEnd 0 := by simp only [oEnd, oPop_eq o]; omega
  rw [oPop_eq] at i32 hcs; rw [hE] at hBS
  trefine ReachFT.push_popK (f := initR o cs) (mask := 0) (epi := o + oPop 0) (by decide) i0 i32
    (by simp only [initR]; omega) (by omega) (by simp only [initR]; omega) (by omega)
    (by simp only [initR, ← hP.2.2, hE, oHead, Nat.add_assoc] at hcs ⊢; exact hcs) (by show 4 * nSaved 0 ≤ 4; decide) e q.2 ?_
  intro t tpc t13 tr hm hcd
  have t13' : t.regs 13 = s.regs 13 - BitVec.ofNat 32 4 := t13
  have tr0 := tr 0 (by decide) (by decide)
  have tpc' : t.pc = base + BitVec.ofNat 32 (oHead o) := tpc
  -- the head: `r12 = c`, `r0 = c + 4`
  trefine ReachFT.glue F headG [] [] [] sH tpc' t13' hcd (by glue_tac [])
    (tr_block [] tpc' []) (fun hp1 h131 hc1 _ => ?_) gH
  obtain ⟨a0, a12⟩ := head_exec t
  rw [tr0] at a0 a12
  -- the literal
  trefine ReachFT.lit F 1 7 iL (by rw [hp1]; rfl) (Hi.self _) h131 hc1
    (by simp only [codeR]; fp_tac) (fun y hy hp5 _ h135 hc5 => ?_) gL
  -- `add r1, pc`: the table
  trefine ReachFT.glue F pcG [] [] [] sP hp5 h135 hc5 (by glue_tac [])
    (tr_block [] hp5 []) (fun hp2 h132 hc2 _ => ?_) gP
  obtain ⟨b0, b1, b12⟩ := pc_exec y
  have y0 : y.regs 0 = s.regs 0 + BitVec.ofNat 32 4 := by
    rw [hy]; simp only [litState, State.setReg, M0Crypto.Proofs.toReg_1]; exact a0
  have y12 : y.regs 12 = s.regs 0 := by
    rw [hy]; simp only [litState, State.setReg, M0Crypto.Proofs.toReg_1]; exact a12
  have y1 : y.regs 1 + (y.regs 15 + 4#32) = base + BitVec.ofNat 32 oT := by
    rw [show y.regs 15 = y.pc from rfl, hp5, hy]
    simp only [litState, State.setReg, M0Crypto.Proofs.toReg_1]
    exact lit_tab (p := oPc o) (by rw [codeWord_drop]; exact hlit)
  have z0 : PI (B := B) base (P 0) oT o 0 (s.regs 13) (execAll pcG y) :=
    ⟨by rw [hp2]; rfl, by rw [b0, y0, q.1, Nat.mul_zero, Nat.add_zero], by rw [b1, y1]; rfl, by rw [b12, y12, q.1],
      h132, hc2, fun i hi => absurd hi (by omega)⟩
  -- the four pairs
  trefine pair_glue e q.1 (by decide) (sPs 0 (by decide)) (gPs 0 (by decide)) hT hT4 hiv z0
    (fun v1 h1 => ?_)
  trefine pair_glue e q.1 (by decide) (sPs 1 (by decide)) (gPs 1 (by decide)) hT hT4 hiv h1
    (fun v2 h2 => ?_)
  trefine pair_glue e q.1 (by decide) (sPs 2 (by decide)) (gPs 2 (by decide)) hT hT4 hiv h2
    (fun v3 h3 => ?_)
  trefine pair_glue e q.1 (by decide) (sPs 3 (by decide)) (gPs 3 (by decide)) hT hT4 hiv h3
    (fun v h4 => ?_)
  -- the tail: the count 0 at `c`
  obtain ⟨vpc, -, -, v12, v13, vc, vwd⟩ := h4
  rw [← q.1] at v12 vwd
  trefine ReachFT.glue F tailG [(12, 4)] [((12 : Reg), 0#32, 4)] [] sT vpc v13 vc
    (by glue_tac [v12, initR, lowWin, ctxSize]) (tr_block [12] vpc [v12, q.1]) (fun hp3 h133 _ hm3 => ?_) gT
  refine ReachT.done ⟨by rw [hp3, oPop_eq]; rfl, by rw [h133, t13'],
    fun r h4 h11 _ hK => absurd (Ed25519Routines.mem_hiRegs h4 h11) hK, ?_, fun i hi => ?_⟩
  · have := tail_exec v
    rw [v12] at this; exact this
  · have : 16 ≤ bitCount pairL * nPairs := by decide
    rw [hm3.read32 (by simp only [regions, List.map, v12] at hsW ⊢; fp_tac), vwd i (by simp only [nPairs] at this; omega)]
  · uniq_tac
  · simp only [Tr.cat_is_is, List.append_nil]; exact ⟨_, rfl⟩
  -- the effect: the frame, then the pieces, each reading code and writing the context
  simp only [Tr.cat_is_is, List.append_nil] at h
  subst h
  simp only [litOk, Bool.and_eq_true, decide_eq_true_eq] at gL
  have hB : pairB = 16 := by decide
  have h4 : 4 * nSaved 0 = 4 := by decide
  refine eff_frame (by decide) (fun y hy => ⟨_, .tail _ (.head _), region_has hy (by decide)⟩) rfl rfl rfl rfl
    (by simp only [spAfter, Bool.toNat_true, BitVec.sub_add_cancel]) rfl fun sp0 n hroom hn hF => ?_
  have up : ∀ {r : Rgn}, r = codeR b ∨ r = ⟨P 0, ctxSize⟩ → ∀ {y}, r.Has y → BelowEntry sp0 n y →
      AtOrAboveSp sp0 (P 1 - BitVec.ofNat 32 (4 * nSaved 0)) y := fun hr y hy hb =>
    above_sub (hF y ⟨_, by rcases hr with rfl | rfl <;> simp, hy⟩ hb) (by rw [h4]; omega)
  have nil : ∀ {t : State} {y : Word}, ¬ InR t [] y := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil
  have pS : ∀ j < nPairs, Seg sp0 n (P 1 - BitVec.ofNat 32 (4 * nSaved 0)) (Has [codeR b])
      (blockTr pairG (b + BitVec.ofNat 32 (oPair o j)) [0, 1]
        [P 0 + BitVec.ofNat 32 (4 + pairB * j), b + BitVec.ofNat 32 (oT + pairB * j)])
      (InR (regState (b + BitVec.ofNat 32 (oPair o j)) [0, 1]
        [P 0 + BitVec.ofNat 32 (4 + pairB * j), b + BitVec.ofNat 32 (oT + pairB * j)]) [(.reg0 0, pairB)]) := by
    intro j hj
    have hj' : pairB * j + pairB ≤ 64 := by rw [hB]; simp only [nPairs] at hj; omega
    have hc : ∀ {o'}, o' < pairB → (codeR b).Has (b + BitVec.ofNat 32 (oT + pairB * j) + BitVec.ofNat 32 o') :=
      fun ho => has_at ho (by simp only [nPairs] at hT; rw [hB] at hT hj' ⊢; omega)
    refine blk_seg (ini := [(.reg0 1, pairB)]) (fp := [(.reg0 1, pairB), (.reg0 0, pairB)]) (by decide) _
      (fun y ⟨r, hr, o', ho, hy⟩ => ?_) (fun y ⟨r, hr, o', ho, hy⟩ hb => ?_)
    · simp only [List.mem_singleton] at hr; subst hr hy; exact ⟨_, .head _, hc ho⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> subst hy
      · exact up (.inl rfl) (hc ho) hb
      · exact up (.inr rfl) (has_at ho (by rw [hB] at hj' ⊢; simp only [ctxSize]; omega)) hb
  refine Seg.mono (Seg.cat (blk_seg (ini := []) (wo := []) (fp := []) (by decide) _ (fun _ h => absurd h nil) fun _ h => absurd h nil)
    (Seg.cat (ev_seg rfl rfl (fun y hy hb => ?_) fun y hy _ => ?_)
    (Seg.cat (blk_seg (ini := []) (wo := []) (fp := []) (by decide) _ (fun _ h => absurd h nil) fun _ h => absurd h nil)
    (Seg.cat (pS 0 (by decide)) (Seg.cat (pS 1 (by decide)) (Seg.cat (pS 2 (by decide)) (Seg.cat (pS 3 (by decide))
      (blk_seg (ini := []) (wo := [(.reg0 12, 4)]) (fp := [(.reg0 12, 4)]) (by decide) _ (fun _ h => absurd h nil)
        fun y ⟨r, hr, o', ho, hy⟩ hb => ?_)))))))) (fun _ h => h) fun y hy => ?_
  · -- the literal reads the code
    rcases hy with ⟨a, ha, -, o', ho, rfl⟩ | ⟨a, ha, hw, -⟩
    · simp only [List.mem_singleton] at ha; subst ha
      exact up (.inl rfl) (has_at ho gL.1.1.2) hb
    · simp only [List.mem_singleton] at ha; subst ha; cases hw
  · obtain ⟨a, ha, -, o', ho, rfl⟩ := hy
    simp only [List.mem_singleton] at ha; subst ha
    exact ⟨_, .head _, has_at ho gL.1.1.2⟩
  · simp only [List.mem_singleton] at hr; subst hr hy
    exact up (.inr rfl) ⟨o', show o' < 196 by simp only at ho; omega, rfl⟩ hb
  · -- the bytes before the buffer: the tail's word and the pairs' words
    rcases ctx_parts hy with ⟨o', ho, rfl⟩ | ⟨j, hj, o', ho, rfl⟩
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, .head _, o', ho, rfl⟩))))))
    · have hI : InR (regState (b + BitVec.ofNat 32 (oPair o j)) [0, 1]
          [P 0 + BitVec.ofNat 32 (4 + pairB * j), b + BitVec.ofNat 32 (oT + pairB * j)]) [(.reg0 0, pairB)]
          (P 0 + BitVec.ofNat 32 (4 + pairB * j) + BitVec.ofNat 32 o') := ⟨_, .head _, o', ho, rfl⟩
      rcases j with _ | _ | _ | _ | j
      · exact .inr (.inr (.inr (.inl hI)))
      · exact .inr (.inr (.inr (.inr (.inl hI))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl hI)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl hI))))))
      · simp only [nPairs] at hj; omega

end

/-- `sha512_init`'s table offset in build `b`. -/
def ivTab (b : Build) : Nat :=
  (wordAt (b.bytes.drop (litOff (oLitI sha512_init) 7)) + BitVec.ofNat 32 (oPc sha512_init + 4)).toNat

theorem init_bytes (b : Build) :
    seqAt b.bytes sha512_init initG = true ∧
    @initOk b.bytes b.size b.codeBytes (footprint sha512_init) sha512_init (ivTab b) = true := by
  cases b <;> exact ⟨by rw [seqAt_eq_scan]; decide +kernel, by decide +kernel⟩

/-- **The `.init` field of `Callees`** for build `b`: `m0c_sha512_init`'s adapter and effect, for
any context relation that holds of a context just after `init`. -/
noncomputable def initAd (b : Build) (Rs : Rels) (hI : ∀ m a, CtxInit m a → Rs.ctx m a []) :
    @AdE Rs b.bytes b.size b.codeBytes (eaS .init) :=
  letI := b.codeBytes
  Ad.ofTSpec (initR sha512_init (footprint sha512_init)) rfl rfl (by decide) (init_te (init_bytes b).1 (init_bytes b).2)
    (fun _ _ _ h => EffT.mono h (by decide)
      (fun y hy => by simpa [CalleeS.Fp, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioInit, CalleeS.reg, ctxSize] using hy)
      (fun y hy => .inl hy) fun y ⟨x, hx, hy⟩ => by
        simp only [eaS, calleeAt, ioInit, List.mem_singleton] at hx; subst hx
        simpa [CalleeS.iniOut, CalleeS.cnt, CalleeS.rawLen, rawSum, CalleeS.reg, eaS, calleeAt, ioInit] using hy)
    (semE .init) (fun _ _ _ _ _ hg _ _ => hg.1 0 (List.mem_singleton_self _))
    (fun st => by simp [initR, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioInit, ctxSize]) (fun _ => rfl)
    fun _ _ st m _ vs _ _ hp => by
      simp only [OutsRel, All2, Rel, eaS, calleeAt, ioInit, semE, BitVec.add_zero, slen, List.map_nil,
        List.sum_nil, List.length_nil, and_true]
      exact hI m _ hp

/-- `Callees` with the `.init` field from the bytes: the other six adapters are the arguments. -/
noncomputable def Callees.ofInit (b : Build) (Rs : Rels) (hI : ∀ m a, CtxInit m a → Rs.ctx m a [])
    (ad : ∀ a, a ≠ .init → @Ad Rs b.bytes b.size b.codeBytes (eaS a))
    (sem : ∀ a h, @Ad.sem Rs b.bytes b.size b.codeBytes _ (ad a h) = semE a)
    (ef : ∀ a h base p, @CalleeS.Eff (eaS a) p b.bytes b.size b.codeBytes base
      (@Ad.T Rs b.bytes b.size b.codeBytes _ (ad a h) base p)) : Callees b where
  Rs := Rs
  ad
    | .init => (initAd b Rs hI).ad
    | .update n ℓ => ad (.update n ℓ) nofun
    | .final n => ad (.final n) nofun
    | .reduce => ad .reduce nofun
    | .mulBase => ad .mulBase nofun
    | .compress => ad .compress nofun
    | .muladd => ad .muladd nofun
  sem
    | .init => rfl
    | .update _ _ => sem _ _
    | .final _ => sem _ _
    | .reduce => sem _ _
    | .mulBase => sem _ _
    | .compress => sem _ _
    | .muladd => sem _ _
  ef
    | .init => (initAd b Rs hI).ef
    | .update _ _ => ef _ _
    | .final _ => ef _ _
    | .reduce => ef _ _
    | .mulBase => ef _ _
    | .compress => ef _ _
    | .muladd => ef _ _

end M0Crypto.Release.Ed25519CallProg
