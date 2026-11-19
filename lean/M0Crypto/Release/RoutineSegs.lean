import M0Crypto.Release.RoutineSLoop
import M0Crypto.Release.RoutinePieces
import M0Crypto.Release.RoutineDiagnose

/-!
# A sequence of blocks and one-block loops

A `Seg` is a straight-line block `g` with its footprints and trace atoms (as for
`ReachFT.sglue`), or, with `br = some c`, a counted loop `g; b<c> g` (`ReachFT.sloop`).
`ReachFT.segs` runs a list of segments; `ReachFT.segLoop` is a counted loop whose body is a list
of segments, closed by `b<c>` back to its start. The caller states one invariant family
`J k i` (segment `k`, before its pass `i`) and, per segment, its side conditions and the effect of
its block; the rules do the glue, the branches, the pcs and the trace. The layout is one
`piecesAt` of `segPieces` followed by any `rest`, handed on to the continuation, and the checks of
every segment are one decided `segsOk`.
-/

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

/-- A block, or with `br = some c` a loop of it closed by `b<c>`. -/
structure Seg where
  g : List Instr
  al : List (SExpr × Nat) := []
  wg : List (SExpr × Nat) := []
  rg : List (SExpr × Nat) := []
  As : List SExpr := []
  br : Option (BitVec 4) := none

def Seg.size (s : Seg) : Nat := seqSize s.g + if s.br.isSome then brSize else 0

def segsSize : List Seg → Nat
  | [] => 0
  | s :: ss => s.size + segsSize ss

/-- The pieces of the segments from `o`. -/
def segPieces : Nat → List Seg → List Piece
  | _, [] => []
  | o, s :: ss => .seq s.g :: ((s.br.map fun c => [Piece.bcond c o]).getD [] ++ segPieces (o + s.size) ss)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The decided checks of the segments from `o`. -/
def segsOk (cs : List (Nat × Nat)) (o d N : Nat) : List Seg → Bool
  | [] => true
  | s :: ss => sglueOk cs s.g o d N s.al s.wg s.rg && traceOkE s.g s.As &&
    (s.br.all fun _ => loopOk (B := B) cs o (o + seqSize s.g) d N (brImm8 (o + seqSize s.g) o)) &&
    segsOk cs (o + s.size) d N ss

/-- The checks of `sglueOk`, each named. -/
def sglueChecks (cs : List (Nat × Nat)) (g : List Instr) (o d N : Nat) (al wg rg : List (SExpr × Nat)) :
    List (String × Bool) :=
  [("block offset is odd", o % 2 == 0), ("block does not fall through", g.all Instr.falls),
   ("block changes sp", keepsSp g), ("block access not aligned (alignChkE)", alignChkE al g),
   ("block writes outside wg (rgnChk)", rgnChk .write wg g), ("block reads outside rg (rgnChk)", rgnChk .read rg g),
   ("block outside the caller's code", rangesSub [(o, o + seqSize g)] cs), ("sp offset beyond the window", decide (d ≤ N))]

theorem sglueChecks_all (cs : List (Nat × Nat)) (g : List Instr) (o d N : Nat) (al wg rg : List (SExpr × Nat)) :
    (sglueChecks cs g o d N al wg rg).all (·.2) = sglueOk cs g o d N al wg rg := by
  simp only [sglueChecks, sglueOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

/-- The first failing check of `segsOk cs o d N ss`: the segment's index and offset, and the check
by name. `none` exactly when `segsOk` holds. -/
def segsFailureFrom (cs : List (Nat × Nat)) (d N : Nat) : Nat → Nat → List Seg → Option String
  | _, _, [] => none
  | k, o, s :: ss =>
    match RoutineDiagnose.firstFalse (sglueChecks cs s.g o d N s.al s.wg s.rg ++
      [("trace atoms (traceOkE)", traceOkE s.g s.As),
       ("loop branch (loopOk)", s.br.all fun _ => loopOk (B := B) cs o (o + seqSize s.g) d N (brImm8 (o + seqSize s.g) o))]) with
    | some w => some s!"segment {k} at byte {o}: {w}"
    | none => segsFailureFrom cs d N (k + 1) (o + s.size) ss

def segsFailure (cs : List (Nat × Nat)) (o d N : Nat) (ss : List Seg) : Option String :=
  segsFailureFrom (B := B) cs d N 0 o ss

theorem segsFailureFrom_eq_none (cs : List (Nat × Nat)) (d N : Nat) :
    ∀ (k o : Nat) (ss : List Seg), segsFailureFrom (B := B) cs d N k o ss = none ↔ segsOk (B := B) cs o d N ss = true
  | _, _, [] => by simp [segsFailureFrom, segsOk]
  | k, o, s :: ss => by
    have ih := segsFailureFrom_eq_none cs d N (k + 1) (o + s.size) ss
    have hf := RoutineDiagnose.firstFalse_eq_none (sglueChecks cs s.g o d N s.al s.wg s.rg ++
      [("trace atoms (traceOkE)", traceOkE s.g s.As),
       ("loop branch (loopOk)", s.br.all fun _ => loopOk (B := B) cs o (o + seqSize s.g) d N (brImm8 (o + seqSize s.g) o))])
    simp only [List.all_append, sglueChecks_all, List.all_cons, List.all_nil, Bool.and_true] at hf
    simp only [segsFailureFrom, segsOk]
    split
    · rename_i w h
      simp only [reduceCtorEq, false_iff, Bool.and_eq_true, not_and]
      intro h1; rw [hf.mpr (by simp_all)] at h; cases h
    · rename_i h
      rw [ih]; simp_all

theorem segsFailure_eq_none (cs : List (Nat × Nat)) (o d N : Nat) (ss : List Seg) :
    segsFailure (B := B) cs o d N ss = none ↔ segsOk (B := B) cs o d N ss = true :=
  segsFailureFrom_eq_none cs d N 0 o ss

/-- The trace of the segments from `o`: segment `k` at the atoms' values `vs k i` of its pass `i`,
`n k` passes, then `Ψ`. -/
def segsTr (base : Word) : Nat → List Seg → (Nat → Nat → List Word) → (Nat → Nat) → TrP → TrP
  | _, [], _, _, Ψ => Ψ
  | o, s :: ss, vs, n, Ψ =>
    match s.br with
    | none => Tr.cat (Tr.is (blockTrE s.g (base + BitVec.ofNat 32 o) s.As (vs 0 0)))
      (segsTr base (o + s.size) ss (fun k => vs (k + 1)) (fun k => n (k + 1)) Ψ)
    | some c => Tr.rep (sloopTr base s.g o s.As (vs 0) c (brImm8 (o + seqSize s.g) o)) 0 (n 0)
      (segsTr base (o + s.size) ss (fun k => vs (k + 1)) (fun k => n (k + 1)) Ψ)

theorem sloopTr_uniq (g : List Instr) (o : Nat) (As : List SExpr) (vs : Nat → List Word)
    (c : BitVec 4) (imm : BitVec 8) (j : Nat) : Tr.Uniq (sloopTr base g o As vs c imm j) := by
  unfold sloopTr; uniq_tac

theorem segsTr_uniq {Ψ : TrP} (h : Tr.Uniq Ψ) : ∀ (o : Nat) (ss : List Seg) vs n,
    Tr.Uniq (segsTr base o ss vs n Ψ)
  | _, [], _, _ => h
  | o, s :: ss, vs, n => by
    have := segsTr_uniq h (o + s.size) ss (fun k => vs (k + 1)) (fun k => n (k + 1))
    unfold segsTr; split
    · exact Tr.uniq_cat (Tr.uniq_is _) this
    · exact Tr.uniq_rep (fun j => sloopTr_uniq _ _ _ _ _ _ j) this 0 _

/-- **A sequence of segments** from `o`: from `J 0 0`, pass `i` of segment `k` takes `J k i` to
`J k (i + 1)` (a block has one pass, a loop's branch is taken exactly while `i + 1 < n k`), and
`J k (n k)` gives `J (k + 1) 0`; then `hexit` from `J ss.length 0` after the last segment. -/
theorem ReachFT.segs {cs : List (Nat × Nat)} {sp0 : Word} {N d : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Ψx : TrP} (F : Caller base sp0 N Wc) (rest : List Piece) :
    ∀ (ss : List Seg) (o : Nat) (J : Nat → Nat → State → Prop) (n : Nat → Nat)
      (vs : Nat → Nat → List Word),
    piecesAt B o (segPieces o ss ++ rest) = true → segsOk (B := B) cs o d N ss = true →
    (∀ k i t v, J k i t → J k i (t.setReg 15 v)) →
    (∀ k s, ss[k]? = some s → 0 < n k ∧ (s.br = none → n k = 1)) →
    (∀ k s i t, ss[k]? = some s → i < n k → J k i t →
      SGlueSides t Rc Wc s.al s.wg s.rg ∧ s.As.map (·.denote t) = vs k i) →
    (∀ k s i t, ss[k]? = some s → i < n k → J k i t → MemEq (sregions t s.wg) t.mem (execAll s.g t).mem →
      J k (i + 1) (execAll s.g t) ∧ ∀ c, s.br = some c → condPassed c (execAll s.g t) = decide (i + 1 < n k)) →
    (∀ k s t, ss[k]? = some s → J k (n k) t → J (k + 1) 0 t) →
    (∀ t, t.pc = base + BitVec.ofNat 32 (o + segsSize ss) → J ss.length 0 t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      piecesAt B (o + segsSize ss) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx) →
    ∀ t, t.pc = base + BitVec.ofNat 32 o → J 0 0 t → t.regs 13 = sp0 - BitVec.ofNat 32 d →
      CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q (segsTr base o ss vs n Ψx)
  | [], o, _, _, _, hl, _, _, _, _, _, _, hexit, t, hpc, hJ, h13, hc =>
    hexit t (by simpa [segsSize] using hpc) hJ h13 hc (by simpa [segPieces, segsSize] using hl)
  | s :: ss, o, J, n, vs, hl, hok, hpcJ, hn, hside, hstep, hnext, hexit, t, hpc, hJ, h13, hc => by
    simp only [segsOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hg, htr⟩, hlp⟩, hok'⟩ := hok
    simp only [segPieces, List.cons_append, List.append_assoc] at hl
    obtain ⟨hseq, hl⟩ := piecesAt_cons hl
    have IH := ReachFT.segs F rest ss (o + s.size) (fun k => J (k + 1)) (fun k => n (k + 1))
      (fun k => vs (k + 1)) ?lay hok' (fun k => hpcJ (k + 1)) (fun k => hn (k + 1))
      (fun k => hside (k + 1)) (fun k => hstep (k + 1)) (fun k => hnext (k + 1))
      (fun t hp hJ h13 hc hr => hexit t (by rw [hp, segsSize, Nat.add_assoc]) hJ h13 hc
        (by rw [segsSize, ← Nat.add_assoc]; exact hr))
    case lay =>
      cases hb : s.br <;> simp only [hb, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some, List.nil_append, List.cons_append, Seg.size, Option.isSome_none,
        Option.isSome_some] at hl ⊢
      · simpa using hl
      · exact (piecesAt_cons hl).2
    have h0 := hn 0 s rfl
    unfold segsTr
    cases hb : s.br with
    | none =>
      have hf : s.g.all Instr.falls = true := by
        simp only [sglueOk, Bool.and_eq_true] at hg; exact hg.1.1.1.1.1.1.2
      exact ReachFT.sglue F s.g s.al s.wg s.rg hseq hpc h13 hc
        (hside 0 s 0 t rfl h0.1 hJ).1 (traceAll_blockTrE hf htr hpc (hside 0 s 0 t rfl h0.1 hJ).2)
        (fun hp' h13' hc' hm => IH _ (by rw [hp', Seg.size, hb]; rfl)
          (hnext 0 s _ rfl (by rw [h0.2 hb]; exact (hstep 0 s 0 t rfl h0.1 hJ hm).1)) h13' hc') hg
    | some c =>
      simp only [hb, Option.map_some, Option.getD_some, List.cons_append] at hl
      have hbr := instrAt_of_seqAt (piecesAt_cons hl).1
      simp only [hb, Option.all_some] at hlp
      exact ReachFT.sloop F s.g s.al s.wg s.rg s.As c _ hseq hbr (n 0) (J 0)
        (hpcJ 0) (vs 0) (fun j u hj hI => hside 0 s j u rfl hj hI)
        (fun j u hj hI hm => ⟨(hstep 0 s j u rfl hj hI hm).1, (hstep 0 s j u rfl hj hI hm).2 c hb⟩)
        (fun u hp hI h13 hc => IH u (by rw [hp, Seg.size, hb]; rfl) (hnext 0 s u rfl hI) h13 hc)
        (by simp only [hg, htr, Bool.true_and]; exact hlp) t h0.1 hpc hJ h13 hc

theorem piecesSize_segPieces : ∀ (o : Nat) (ss : List Seg), piecesSize (segPieces o ss) = segsSize ss
  | _, [] => rfl
  | o, s :: ss => by
    cases hb : s.br <;> simp [segPieces, segsSize, Seg.size, hb, piecesSize_segPieces, brSize_eq] <;>
      omega

/-- **A counted loop of segments**: `m` passes of the segments `ss` from `o`, each closed by
`b<c>` back to `o`. Pass `j` runs the segments with `J j`; `I j` gives `J j 0 0`, and
`J j ss.length 0` gives `I (j + 1)` and the branch exactly while `j + 1 < m`. -/
theorem ReachFT.segLoop {cs : List (Nat × Nat)} {sp0 : Word} {N d : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Ψx : TrP} (F : Caller base sp0 N Wc) (rest : List Piece) (ss : List Seg)
    (c : BitVec 4) (o m : Nat) (I : Nat → State → Prop) (J : Nat → Nat → Nat → State → Prop)
    (n : Nat → Nat → Nat) (vs : Nat → Nat → Nat → List Word)
    (hl : piecesAt B o (segPieces o ss ++ .bcond c o :: rest) = true)
    (hok : (segsOk (B := B) cs o d N ss &&
      loopOk (B := B) cs o (o + segsSize ss) d N (brImm8 (o + segsSize ss) o)) = true)
    (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v)) (hpcJ : ∀ j k i t v, J j k i t → J j k i (t.setReg 15 v))
    (hin : ∀ j t, j < m → I j t → J j 0 0 t)
    (hn : ∀ j k s, j < m → ss[k]? = some s → 0 < n j k ∧ (s.br = none → n j k = 1))
    (hside : ∀ j k s i t, j < m → ss[k]? = some s → i < n j k → J j k i t →
      SGlueSides t Rc Wc s.al s.wg s.rg ∧ s.As.map (·.denote t) = vs j k i)
    (hstep : ∀ j k s i t, j < m → ss[k]? = some s → i < n j k → J j k i t →
      MemEq (sregions t s.wg) t.mem (execAll s.g t).mem →
      J j k (i + 1) (execAll s.g t) ∧ ∀ c, s.br = some c → condPassed c (execAll s.g t) = decide (i + 1 < n j k))
    (hnext : ∀ j k s t, j < m → ss[k]? = some s → J j k (n j k) t → J j (k + 1) 0 t)
    (hout : ∀ j t, j < m → J j ss.length 0 t → I (j + 1) t ∧ condPassed c t = decide (j + 1 < m))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (o + segsSize ss + brSize) → I m t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      piecesAt B (o + segsSize ss + brSize) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (t : State) (hm : 0 < m) (hpc : t.pc = base + BitVec.ofNat 32 o) (hI : I 0 t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hc : CodeAt t.mem base B) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.rep (fun j => Tr.cat (segsTr base o ss (vs j) (n j) (Tr.is []))
        (Tr.is [⟨base + BitVec.ofNat 32 (o + segsSize ss), .bcond c (brImm8 (o + segsSize ss) o), []⟩]))
        0 m Ψx) := by
  simp only [Bool.and_eq_true] at hok
  have hseg := hl
  rw [piecesAt_append] at hseg
  simp only [Bool.and_eq_true] at hseg
  rw [piecesSize_segPieces] at hseg
  obtain ⟨hbr, hr⟩ := piecesAt_cons hseg.2
  have h := ReachFT.loop (Φb := fun j => segsTr base o ss (vs j) (n j) (Tr.is [])) F c _
    (instrAt_of_seqAt hbr) m I hpcI (fun j u hj hpu hIu h13u hcu =>
      ReachFT.segs F (.bcond c o :: rest) ss o (J j) (n j) (vs j) hl hok.1 (hpcJ j)
        (fun k s => hn j k s hj) (fun k s i t => hside j k s i t hj) (fun k s i t => hstep j k s i t hj)
        (fun k s t => hnext j k s t hj)
        (fun v hpv hJv h13v hcv _ => ReachT.done ⟨hpv, h13v, hcv, hout j v hj hJv⟩)
        u hpu (hin j u hj hIu) h13u hcu)
    (fun u hpu hIu h13u hcu => hexit u hpu hIu h13u hcu hr) hok.2 0 t hm hpc hI h13 hc
  rwa [Nat.sub_zero] at h

/-- Cases on the segment `k` of a list `ss` of three, its entry `hk : ss[k]? = some s` substituted. -/
macro "seg_cases" ss:ident k:ident hk:ident : tactic => `(tactic|
  (rcases $k:ident with _ | _ | _ | $k:ident <;>
    simp only [$ss:ident, List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq] at $hk:ident <;> subst $hk:ident))

end M0Crypto.Release.Routine

