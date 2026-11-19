import M0Crypto.Release.RoutineSegs

/-!
# Loops closed by a far branch

The generator's `jump_if` closes a loop with `b<inv> +0; b back` (`b` has the range `b<cond>`
lacks). `ReachFT.loopFar` is `ReachFT.loop` for that pair: pass `j` takes the exit branch exactly
when it is the last, else the `b`. `ReachFT.segLoopFar` is `ReachFT.segLoop` with that tail.
-/

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The decided checks of a far back branch at `ob`: `b<c>` to `ob + 4`, then `b` to `o`. -/
def loopFarOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o ob d N : Nat) (i8 : BitVec 8) (i11 : BitVec 11) : Bool :=
  ob % 2 == 0 && rangesSub [(ob, ob + 4)] cs && decide (ob + 4 ≤ BS) &&
  decide (BitVec.ofNat 32 ob + 4#32 + (i8 ++ 0#1).signExtend 32 = BitVec.ofNat 32 (ob + 4)) &&
  decide (BitVec.ofNat 32 (ob + 2) + 4#32 + (i11 ++ 0#1).signExtend 32 = BitVec.ofNat 32 o) && decide (d ≤ N)

/-- Pass `j` of `n`: the body, the exit test, and the `b` back unless it is the last. -/
def farPass (base : Word) (ob : Nat) (c : BitVec 4) (i8 : BitVec 8) (i11 : BitVec 11) (Φb : Nat → TrP)
    (n j : Nat) : TrP :=
  Tr.cat (Φb j) (Tr.is (⟨base + BitVec.ofNat 32 ob, .bcond c i8, []⟩ ::
    if j + 1 < n then [⟨base + BitVec.ofNat 32 (ob + 2), .b i11, []⟩] else []))

theorem farPass_uniq {ob : Nat} {c : BitVec 4} {i8 : BitVec 8} {i11 : BitVec 11} {Φb : Nat → TrP}
    (h : ∀ j, Tr.Uniq (Φb j)) (n j : Nat) : Tr.Uniq (farPass base ob c i8 i11 Φb n j) :=
  Tr.uniq_cat (h j) (Tr.uniq_is _)

/-- **A counted loop closed by a far branch**: as `ReachFT.loop`, with `b<c>` at `ob` to `ob + 4`
taken exactly after the last pass and `b` at `ob + 2` back to `o`. -/
theorem ReachFT.loopFar {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Φb : Nat → TrP} {Ψx : TrP} {o ob d : Nat} (F : Caller base sp0 N Wc) (c : BitVec 4)
    (i8 : BitVec 8) (i11 : BitVec 11) (hbr : instrAt B ob = some (.bcond c i8))
    (hb : instrAt B (ob + 2) = some (.b i11)) (n : Nat)
    (I : Nat → State → Prop) (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v))
    (hbody : ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t (fun u =>
        u.pc = base + BitVec.ofNat 32 ob ∧ u.regs 13 = sp0 - BitVec.ofNat 32 d ∧
        CodeAt u.mem base B ∧ I (j + 1) u ∧ condPassed c u = decide (n ≤ j + 1)) (Φb j))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (ob + 4) → I n t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (hok : loopFarOk cs o ob d N i8 i11 = true) :
    ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (farPass base ob c i8 i11 Φb n) j (n - j) Ψx) := by
  simp only [loopFarOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hob, hcs⟩, hsz⟩, ht⟩, ht2⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have hpc15 : ∀ (u : State) (v : Word), (u.setReg 15 v).pc = v := fun _ _ => by
    simp [State.setReg, State.pc]
  have h15 : ∀ (u : State) (v : Word), (u.setReg 15 v).regs 13 = u.regs 13 := fun _ _ => by
    simp [State.setReg]
  have pin : ∀ k, k < 4 → PcIn base cs (base + BitVec.ofNat 32 (ob + k)) := fun k hk =>
    PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega))
  have quiet : ∀ (u : State) (i : Instr) k, k < 4 → u.pc = base + BitVec.ofNat 32 (ob + k) →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → Step (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u ⟨u.pc, i, []⟩ :=
    fun u i k hk hpu hu13 => ⟨by rw [hpu]; exact pin k hk, fun y hy => absurd hy (writes_nil y),
      fun y hy => absurd hy (reads_nil y), by rw [hu13]; exact ⟨d, hd, rfl⟩⟩
  suffices H : ∀ rem j t, rem + j + 1 = n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (farPass base ob c i8 i11 Φb n) j (rem + 1) Ψx) from
    fun j t hj => by rw [show n - j = (n - j - 1) + 1 by omega]; exact H (n - j - 1) j t (by omega)
  intro rem
  induction rem with
  | zero =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := true) hb2 ob (ob + 4) c i8 hpu hob hbr (by omega) ht
        (quiet u _ 0 (by omega) hpu hu13) (by rw [hcp]; simp; omega) (ΨF := Ψx)
        (fun _ => hexit _ (hpc15 _ _) (by rw [show n = j + 1 by omega]; exact hpcI _ _ _ hIu)
          (by rw [h15]; exact hu13) hcu) fun hF => absurd (hcp ▸ hF) (by simp; omega))
      (fun _ _ h => h) (fun _ h => h) ?_
    rintro _ ⟨a, _, rfl, ha, _, d, rfl, rfl, hd⟩
    refine ⟨_, d, ?_, ⟨a, _, rfl, ha, rfl⟩, hd.1 rfl⟩
    simp [show ¬ j + 1 < n by omega]
  | succ rem ih =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := false) hb2 ob (ob + 4) c i8 hpu hob hbr (by omega) ht
        (quiet u _ 0 (by omega) hpu hu13) (by rw [hcp]; simp; omega)
        (ΨT := Ψx) (fun hT => absurd (hcp ▸ hT) (by simp; omega))
        fun _ => ReachT.b hb2 (ob + 2) o i11 (hpc15 _ _) (by omega) hb (by omega) ht2
          (quiet _ _ 2 (by omega) (hpc15 _ _) (by rw [h15]; exact hu13))
          (ih (j + 1) _ (by omega) (hpc15 _ _) (hpcI _ _ _ (hpcI _ _ _ hIu)) (by rw [h15, h15]; exact hu13) hcu))
      (fun _ _ h => h) (fun _ h => h) ?_
    rintro _ ⟨a, _, rfl, ha, _, _, rfl, rfl, hd⟩
    obtain ⟨_, x, rfl, rfl, hx⟩ := hd.2 rfl
    refine ⟨_, x, ?_, ⟨a, _, rfl, ha, rfl⟩, hx⟩
    simp [show j + 1 < n by omega]

/-- **A counted loop of segments closed by a far branch**: `ReachFT.segLoop` with `b<c>` to the
exit and `b` back to `o`. -/
theorem ReachFT.segLoopFar {cs : List (Nat × Nat)} {sp0 : Word} {N d : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Ψx : TrP} (F : Caller base sp0 N Wc) (rest : List Piece) (ss : List Seg)
    (c : BitVec 4) (o m : Nat) (I : Nat → State → Prop) (J : Nat → Nat → Nat → State → Prop)
    (n : Nat → Nat → Nat) (vs : Nat → Nat → Nat → List Word)
    (hl : piecesAt B o (segPieces o ss ++ .bcond c (o + segsSize ss + 4) :: .b o :: rest) = true)
    (hok : (segsOk (B := B) cs o d N ss && loopFarOk (B := B) cs o (o + segsSize ss) d N
      (brImm8 (o + segsSize ss) (o + segsSize ss + 4)) (brImm11 (o + segsSize ss + 2) o)) = true)
    (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v)) (hpcJ : ∀ j k i t v, J j k i t → J j k i (t.setReg 15 v))
    (hin : ∀ j t, j < m → I j t → J j 0 0 t)
    (hn : ∀ j k s, j < m → ss[k]? = some s → 0 < n j k ∧ (s.br = none → n j k = 1))
    (hside : ∀ j k s i t, j < m → ss[k]? = some s → i < n j k → J j k i t →
      SGlueSides t Rc Wc s.al s.wg s.rg ∧ s.As.map (·.denote t) = vs j k i)
    (hstep : ∀ j k s i t, j < m → ss[k]? = some s → i < n j k → J j k i t →
      MemEq (sregions t s.wg) t.mem (execAll s.g t).mem →
      J j k (i + 1) (execAll s.g t) ∧ ∀ c, s.br = some c → condPassed c (execAll s.g t) = decide (i + 1 < n j k))
    (hnext : ∀ j k s t, j < m → ss[k]? = some s → J j k (n j k) t → J j (k + 1) 0 t)
    (hout : ∀ j t, j < m → J j ss.length 0 t → I (j + 1) t ∧ condPassed c t = decide (m ≤ j + 1))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (o + segsSize ss + 4) → I m t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      piecesAt B (o + segsSize ss + 4) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (t : State) (hm : 0 < m) (hpc : t.pc = base + BitVec.ofNat 32 o) (hI : I 0 t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hc : CodeAt t.mem base B) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.rep (farPass base (o + segsSize ss) c (brImm8 (o + segsSize ss) (o + segsSize ss + 4))
        (brImm11 (o + segsSize ss + 2) o) (fun j => segsTr base o ss (vs j) (n j) (Tr.is [])) m) 0 m Ψx) := by
  simp only [Bool.and_eq_true] at hok
  have hseg := hl
  rw [piecesAt_append] at hseg
  simp only [Bool.and_eq_true] at hseg
  rw [piecesSize_segPieces] at hseg
  obtain ⟨hbr, hr⟩ := piecesAt_cons hseg.2
  obtain ⟨hb, hr⟩ := piecesAt_cons hr
  simp only [Piece.size, brSize_eq] at hr hb
  have h := ReachFT.loopFar (Φb := fun j => segsTr base o ss (vs j) (n j) (Tr.is [])) F c _ _
    (instrAt_of_seqAt hbr) (instrAt_of_seqAt hb) m I hpcI (fun j u hj hpu hIu h13u hcu =>
      ReachFT.segs F (.bcond c (o + segsSize ss + 4) :: .b o :: rest) ss o (J j) (n j) (vs j) hl hok.1 (hpcJ j)
        (fun k s => hn j k s hj) (fun k s i t => hside j k s i t hj) (fun k s i t => hstep j k s i t hj)
        (fun k s t => hnext j k s t hj)
        (fun v hpv hJv h13v hcv _ => ReachT.done ⟨hpv, h13v, hcv, hout j v hj hJv⟩)
        u hpu (hin j u hj hIu) h13u hcu)
    (fun u hpu hIu h13u hcu => hexit u hpu hIu h13u hcu (by rwa [show o + segsSize ss + 4 = o + segsSize ss + 2 + 2 by omega]))
    hok.2 0 t hm hpc hI h13 hc
  rwa [Nat.sub_zero] at h

end M0Crypto.Release.Routine
