import SafegcdTermination.EndFootprint
import M0Crypto.Release.SymReadChk
import M0Crypto.Release.StackEffectSym

namespace SafegcdTermination.TraceReads

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank (addr InSlot)
open SafegcdTermination.PublicTrace (publicState stackState)
open SafegcdTermination.TraceWrites (subregion)
open SafegcdTermination.InitCode SafegcdTermination.ClearLoop SafegcdTermination.RunInit
open SafegcdTermination.FinalCode SafegcdTermination.FinalPrepare SafegcdTermination.RunFinal
open SafegcdTermination.FinalSub SafegcdTermination.FinalSelect
open SafegcdTermination.Leaf (callTrace leafTrace)
open M0Crypto.Armv6M (Reg State)
open M0Crypto.Thumb M0Crypto.Release M0Crypto.Sym

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

private abbrev LoadRegions := List (Reg × Word × Nat)

private theorem block {is : List Instr} {s : State} {rs : LoadRegions} {R : Word → Prop}
    (hf : is.all Instr.falls = true) (hc : readChk (fun _ => true) rs is = true)
    (hr : ∀ p ∈ rs, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o)) :
    ReadsFrom R (traceAll is s) := by
  intro e he x hx
  obtain ⟨p,hp,o,ho,rfl⟩ := readChk_sound _ _ is (sound_all hf) s hc e he rfl x hx
  exact hr p hp o ho

private theorem event (pc : Word) (i : Instr) (R : Word → Prop) :
    ReadsFrom R [⟨pc,i,[]⟩] :=
  readsFrom_of_empty _ (fun _ h => (List.mem_singleton.mp h) ▸ rfl)

private theorem call {is : List Instr} {base : Word} {off dest : Nat} {s : State} {R : Word → Prop}
    (h : ReadsFrom R (traceAll is s)) :
    ReadsFrom R (callTrace is base off dest s) := by
  exact (event _ _ _).append (h.append (event _ _ _))

private theorem quiet {is : List Instr} {s : State} {R : Word → Prop}
    (hf : is.all Instr.falls = true) (hc : readChk (fun _ => true) [] is = true) :
    ReadsFrom R (traceAll is s) :=
  block hf hc (fun _ hp => False.elim (List.not_mem_nil hp))

private theorem one {is : List Instr} {s : State} {r : Reg} {n : Nat}
    (hf : is.all Instr.falls = true) (hc : readChk (fun _ => true) [(r,0,n)] is = true) :
    ReadsFrom (Region (s.regs r) n) (traceAll is s) := by
  apply block (s := s) (R := Region (s.regs r) n) hf hc
  intro p hp o ho
  rw [List.mem_singleton] at hp
  subst p
  exact Region.mk ho (by simp)

private theorem clear (base a : Word) (off n : Nat) (R : Word → Prop) :
    ReadsFrom R (clearTrace base off a n) := by
  induction n generalizing a with
  | zero => exact ReadsFrom.nil _
  | succ n ih =>
    rw [clearTrace, clearStepTrace]
    exact ((quiet (by decide) (by decide +kernel)).append (event _ _ _)).append (ih _)

theorem init (base sp src : Word) (start canon : Nat) :
    ReadsFrom (fun y => Region sp frameBytes y ∨ Region src 32 y) (initTrace base sp src start canon) := by
  unfold initTrace
  let s := publicState [(15,base+BitVec.ofNat 32 canon),(0,addr sp temp),(1,src)]
  have hCanon : ReadsFrom (fun y => Region sp frameBytes y ∨ Region src 32 y)
      (traceAll canonBody s) := by
    apply block (s := s) (is := canonBody) (rs := [(0,0,32),(1,0,32)])
      (R := fun y => Region sp frameBytes y ∨ Region src 32 y) (by decide) (by decide +kernel)
    intro j hj o ho
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with h | h <;> subst j
    · left
      apply subregion (off := temp) (m := 32) (by decide)
      exact Region.mk ho (by simp [s, publicState, addr])
    · right
      exact Region.mk ho (by simp [s, publicState])
  have hTail (pc : Word) : ReadsFrom (Region sp frameBytes) (traceAll InitCode.tail (stackState pc sp)) :=
    one (r := 13) (by decide) (by decide +kernel)
  exact ((((quiet (by decide) (by decide +kernel)).append (call hCanon)).append
    (quiet (by decide) (by decide +kernel))).append (clear _ _ _ _ _)).append
    ((hTail _).mono (fun _ h => .inl h))

private theorem fold (pc a : Word) : ReadsFrom (Region a vectorBytes) (FoldCode.predictedTrace pc a) := by
  let s := publicState [(15,pc),(0,a)]
  change ReadsFrom _ (FoldCode.predictedTrace s.pc (s.regs 0))
  rw [FoldCode.predicted_eq s]
  exact (one (r := 0) (by decide) (by decide +kernel)).append (event _ _ _)

/-- The vector banks, counter, and matrix occupy a contiguous prefix of the frame. -/
def batchBytes : Nat := matrixAt + 16

private theorem sub (base sp : Word) (off dest : Nat) :
    ReadsFrom (Region sp batchBytes) (subTrace base sp off dest) := by
  unfold subTrace
  apply call
  let s := publicState [(15,base+BitVec.ofNat 32 dest),(0,addr sp bankE),(1,addr sp bankG),(2,sp)]
  change ReadsFrom _ (traceAll subBody s)
  apply block (s := s) (is := subBody) (rs := [(1,0,32),(2,0,32)])
    (R := Region sp batchBytes) (by decide) (by decide +kernel)
  intro j hj o ho
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
  rcases hj with h | h <;> subst j
  · apply subregion (off := bankG) (m := 32) (by decide)
    exact Region.mk ho (by simp [s, publicState, addr])
  · exact Region.mk (Nat.lt_of_lt_of_le ho (by decide : 32 ≤ batchBytes)) (by simp [s, publicState])

private theorem select (base sp dst : Word) (off dest : Nat) :
    ReadsFrom (Region sp batchBytes) (selectTrace base sp dst off dest) := by
  unfold selectTrace pickTrace
  apply ReadsFrom.append (one (r := 13) (by decide) (by decide +kernel))
  apply call
  let s := publicState [(15,base+BitVec.ofNat 32 dest),(0,dst),(1,sp),(2,addr sp bankE)]
  change ReadsFrom _ (traceAll selectBody s)
  apply block (s := s) (is := selectBody) (rs := [(1,0,32),(2,0,32)])
    (R := Region sp batchBytes) (by decide) (by decide +kernel)
  intro j hj o ho
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
  rcases hj with h | h <;> subst j
  · exact Region.mk (Nat.lt_of_lt_of_le ho (by decide : 32 ≤ batchBytes)) (by simp [s, publicState])
  · apply subregion (off := bankE) (m := 32) (by decide)
    exact Region.mk ho (by simp [s, publicState, addr])

theorem final (q : Targets) (base sp dst : Word) (off subOff selectOff : Nat) :
    ReadsFrom (fun y => Region sp batchBytes y ∨ Region (addr sp returnAt) 4 y)
      (finalTrace q base sp dst off subOff selectOff) := by
  unfold finalTrace
  have hFold := (fold (base+BitVec.ofNat 32 q.fold) sp).mono (fun _ h =>
    Nat.lt_of_lt_of_le h (by decide : vectorBytes ≤ batchBytes))
  have hRet (pc : Word) : ReadsFrom (Region (addr sp returnAt) 4)
      (traceAll [loadSp 3 returnAt] (stackState pc sp)) := by
    apply block (is := [loadSp 3 returnAt]) (s := stackState pc sp)
      (rs := [(13,BitVec.ofNat 32 returnAt,4)]) (R := Region (addr sp returnAt) 4)
      (by decide) (by decide +kernel)
    intro p hp o ho
    rw [List.mem_singleton] at hp
    subst p
    exact Region.mk ho rfl
  have hPack : ReadsFrom (Region sp batchBytes)
      (traceAll subPrep (stackState (base+BitVec.ofNat 32 (packSite off)) sp)) :=
    one (r := 13) (by decide) (by decide +kernel)
  have hPre : ReadsFrom (Region sp batchBytes)
      (traceAll (prepareFold finalRow) (stackState (base+BitVec.ofNat 32 off) sp)) :=
    quiet (by decide) (by decide +kernel)
  let call := foldSite off
  have hCall := event (base+BitVec.ofNat 32 call) (callTo call q.fold) (Region sp batchBytes)
  have hBody := ((((hPre.append (hCall.append hFold)).append hPack).append
    (sub base sp (subSite off) subOff)).append (select base sp dst (selectSite off) selectOff))
  exact (hBody.mono (fun _ h => .inl h)).append
    (((hRet _).mono (fun _ h => .inr h)).append (event _ _ _))

open SafegcdTermination.BatchSlots (row)
open SafegcdTermination.RunRow (rowPre rowLit rowTrace)
open SafegcdTermination.PhaseOperands (row_cases)
open M0Crypto.Release.StackEffect (fpChk InR fp_acc spl_denote evD)

private def literalExpr (r : RowCall) (imm : BitVec 8) : SExpr :=
  .add (.and (.add (.reg0 15) (.const (BitVec.ofNat 32
    (seqSize (prepareRow r) + seqSize correctionPrefix + 4)))) (.not (.const 3#32)))
    (.const (BitVec.ofNat 32 (imm.toNat * 4)))

private def rowRegions (q : Targets) (off : Nat) (r : RowCall) : List (SExpr × Nat) :=
  (.reg0 13,batchBytes) :: if r.modular then [(literalExpr r (rowLit q off r),4)] else []

private theorem prepare_footprint (q : Targets) (off : Nat) (phase : Fin 3) (i : Fin 4) :
    let r := row phase i
    fpChk (rowRegions q off r) (rowPre q off r) = true := by
  rcases phase_cases phase with rfl | rfl | rfl <;>
    rcases row_cases i with rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    dsimp only [rowRegions, rowPre]
    generalize h : rowLit q off (row _ _) = lit
    clear h
    revert lit
    decide +kernel

open SafegcdTermination.RunRows (literalAt rowPc rowsTrace)
open SafegcdTermination.Literal (LiteralLinks literal_address)
open SafegcdTermination.RunBatch (batchTrace)
open SafegcdTermination.Run43 (tripletTrace tripletsTrace loopTrace)
open SafegcdTermination.LoopLinks (counterSite phaseAt backSite)
open SafegcdTermination.LoopControl (countTrace bTo)
open SafegcdTermination.LoopCounter (updateCounter triplets)

abbrev LoopReads (base sp : Word) (q : Targets) :=
  ReadsFrom (fun y => Region sp batchBytes y ∨ Region (base + BitVec.ofNat 32 q.literal) 4 y)

private theorem prepare (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3) (i : Fin 4)
    (hLit : (row phase i).modular = true →
      literalAt base q off (row phase i) = base + BitVec.ofNat 32 q.literal) :
    LoopReads base sp q (traceAll (rowPre q off (row phase i))
      (stackState (base+BitVec.ofNat 32 off) sp)) := by
  let r := row phase i
  let s := stackState (base+BitVec.ofNat 32 off) sp
  have hf : (rowPre q off r).all Instr.falls = true := by
    unfold rowPre
    split
    · exact SafegcdTermination.ModularCalls.prepareMod_falls _ _
    · exact SafegcdTermination.RowCalls.prepareRow_falls _
  have hT := symTrace_sound _ (sound_all hf) s SState.init
  rw [SState.init_denote] at hT
  change LoopReads base sp q (traceAll (rowPre q off r) s)
  rw [← hT]
  intro e he y hy
  have hR : InR s (rowRegions q off r) y :=
    fp_acc (dpc := (·.denote s)) (prepare_footprint q off phase i)
      (spl_denote s) e he y (.inl hy)
  obtain ⟨p,hp,o,ho,rfl⟩ := hR
  simp only [rowRegions, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact .inl (Region.mk ho rfl)
  · split at hp
    · rename_i hMod
      rw [List.mem_singleton] at hp
      subst p
      have hAddr : (literalExpr r (rowLit q off r)).denote s =
          literalAt base q off r := by
        unfold literalExpr literalAt
        change ((base + BitVec.ofNat 32 off + BitVec.ofNat 32
          (seqSize (prepareRow r) + seqSize correctionPrefix + 4)) &&& ~~~3#32) + _ = _
        rw [ofNat_add_assoc]
        simp only [SExpr.denote, Nat.add_assoc, Nat.mul_comm]
      exact .inr (Region.mk ho (by rw [hAddr, hLit hMod]))
    · cases hp

private theorem body_reads (p : Pins) (pc : Word) (modular : Bool) :
    ReadsFrom (fun y => Region p.x vectorBytes y ∨ Region p.y vectorBytes y)
      (predictedBody p pc modular) := by
  intro e he y hy
  obtain ⟨a,ha,hr,k,hk,rfl⟩ := hy
  obtain ⟨i,hi,hx | hy | hw⟩ := body_trace_in p pc modular e he a ha
  · subst a
    left
    apply Region.mk (o := 4*i+k)
    · change k < 4 at hk
      unfold vectorBytes
      omega
    · simp only [loadAt, M0Crypto.Armv6M.slot, ofNat_add_assoc]
  · subst a
    right
    apply Region.mk (o := 4*i+k)
    · change k < 4 at hk
      unfold vectorBytes
      omega
    · simp only [loadAt, M0Crypto.Armv6M.slot, ofNat_add_assoc]
  · subst a
    cases hr

private theorem one_row (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3) (i : Fin 4)
    (hLit : (row phase i).modular = true →
      literalAt base q off (row phase i) = base + BitVec.ofNat 32 q.literal) :
    LoopReads base sp q (rowTrace q base sp off (row phase i)) := by
  let r := row phase i
  have slots : ∀ (j : Fin 3) (k : Fin 4),
      (row j k).dst + vectorBytes ≤ batchBytes ∧ (row j k).x + vectorBytes ≤ batchBytes ∧
      (row j k).y + vectorBytes ≤ batchBytes := by decide +kernel
  obtain ⟨hd,hx,hy⟩ := slots phase i
  let call := off+seqSize (rowPre q off r)
  let dest := if r.modular then q.modular else q.exact
  let pc := base+BitVec.ofNat 32 dest
  let ps : Pins := ⟨addr sp r.dst,addr sp r.x,addr sp r.y,0,0,0,0,0⟩
  have hBody : LoopReads base sp q (predictedBody ps pc r.modular) :=
    (body_reads ps pc r.modular).mono (fun _ h =>
      .inl (h.elim (subregion hx) (subregion hy)))
  have hFold : LoopReads base sp q (FoldCode.predictedTrace (base+BitVec.ofNat 32 q.fold) ps.out) :=
    (fold _ _).mono (fun _ h => .inl (subregion hd h))
  have hLeaf := (event (base+BitVec.ofNat 32 call) (callTo call dest) _).append
    (hBody.append (event (nextPC pc (body r.modular)) (.bx 12) _))
  unfold rowTrace
  apply ReadsFrom.append ((prepare q base sp off phase i hLit).append hLeaf)
  split
  · exact (quiet (by rfl) (by rfl)).append ((event _ _ _).append hFold)
  · exact ReadsFrom.nil _

private theorem annotate_quiet (pc : Word) (is : List Instr) (R : Word → Prop) :
    ReadsFrom R (annotate pc is []) := by
  induction is generalizing pc with
  | nil => exact ReadsFrom.nil _
  | cons i is ih => exact (event _ _ _).append (ih _)

private theorem rows (q : Targets) (base sp : Word) (start : Nat) (phase : Fin 3)
    (hLit : ∀ i : Fin 4, (row phase i).modular = true →
      literalAt base q (rowPc q start phase i.val) (row phase i) = base + BitVec.ofNat 32 q.literal)
    (n : Nat) (hn : n ≤ 4) : LoopReads base sp q (rowsTrace q base sp start phase n) := by
  induction n with
  | zero => exact ReadsFrom.nil _
  | succ n ih =>
    have h := hLit (Fin.ofNat 4 n)
    have hi : (Fin.ofNat 4 n).val = n := by
      change n % 4 = n
      omega
    rw [hi] at h
    exact (ih (by omega)).append (one_row q base sp _ _ _ h)

private theorem batch (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3)
    (hLit : ∀ i : Fin 4, (row phase i).modular = true →
      literalAt base q (rowPc q (firstRow q off (phases phase)) phase i.val) (row phase i) =
        base + BitVec.ofNat 32 q.literal) :
    LoopReads base sp q (batchTrace q base sp off phase) := by
  unfold batchTrace
  have hPrep (pc : Word) : ReadsFrom (Region sp batchBytes)
      (traceAll (prepareMatrix (phases phase)) (stackState pc sp)) := by
    apply one (r := 13) (SafegcdTermination.MatrixCall.matrix_pre_falls phase)
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  have hSave (pc : Word) : LoopReads base sp q (traceAll saveMatrix (stackState pc sp)) :=
    quiet (by decide) (by decide +kernel)
  let leaf := base+BitVec.ofNat 32 q.matrix
  let call := off+seqSize (prepareMatrix (phases phase))
  have hLeaf : LoopReads base sp q
      ([⟨base+BitVec.ofNat 32 call,callTo call q.matrix,[]⟩] ++
        (annotate leaf MatrixCode.body [] ++ [⟨nextPC leaf MatrixCode.body,.bx 14,[]⟩])) :=
    (event _ _ _).append ((annotate_quiet _ _ _).append (event _ _ _))
  exact ((((hPrep _).mono (fun _ h => .inl h)).append hLeaf).append (hSave _)).append
    (rows q base sp _ _ hLit 4 (by decide))

private theorem count (q : Targets) (base sp : Word) (off done : Nat) (last : Bool) :
    LoopReads base sp q (countTrace base sp off done last) := by
  have hUpdate : ReadsFrom (Region sp batchBytes)
      (traceAll updateCounter (stackState (base+BitVec.ofNat 32 off) sp)) :=
    one (r := 13) (by decide) (by decide +kernel)
  let o := off+seqSize updateCounter
  have h := (hUpdate.mono (Rd' := fun y => Region sp batchBytes y ∨
    Region (base + BitVec.ofNat 32 q.literal) 4 y) (fun _ h => .inl h)).append
    (event (base+BitVec.ofNat 32 o) (.bcond 1 0) _)
  cases last
  · simpa only [countTrace,Bool.false_eq_true,ite_false,List.append_nil,o] using h
  · exact h.append (event _ _ _)

theorem loop {code : List (BitVec 8)} {q : Targets} {entry done : Nat} {base sp : Word}
    (h : LiteralLinks code q entry done) (hb : base.toNat % 4 = 0)
    (hBound : base.toNat + q.literal + 4 ≤ 2^32) :
    LoopReads base sp q (loopTrace q base sp entry done) := by
  have hBatch (j : Fin 3) : LoopReads base sp q
      (batchTrace q base sp (phaseAt q entry done j) j) := by
    apply batch
    intro i hi
    have he := h.2.2 j i hi
    rw [literal_address _ _ _ _ hb (by rw [he]; exact hBound), he]
  have hTriplet : LoopReads base sp q (tripletTrace q base sp entry done) := by
    exact ((((hBatch 0).append (count q base sp _ _ false)).append (hBatch 1)).append
      (hBatch 2)).append (event _ _ _)
  have hTriplets (k : Nat) : LoopReads base sp q (tripletsTrace q base sp entry done k) := by
    induction k with
    | zero => exact ReadsFrom.nil _
    | succ k ih => exact ih.append hTriplet
  exact ((hTriplets triplets).append (hBatch 0)).append (count q base sp _ _ true)

/-- All reads of the inversion are from its frame, source, or the checked literal. -/
theorem inversion {code : List (BitVec 8)} {q : Targets} {base sp dst src : Word}
    {start canon entry done subOff selectOff : Nat}
    (h : LiteralLinks code q entry done) (hb : base.toNat % 4 = 0)
    (hBound : base.toNat + q.literal + 4 ≤ 2^32) :
    ReadsFrom (fun y => Region sp frameBytes y ∨ Region src 32 y ∨
      Region (base + BitVec.ofNat 32 q.literal) 4 y)
      (Invert.inversionTrace q base sp dst src start canon entry done subOff selectOff) := by
  exact (((init base sp src start canon).mono (fun _ h =>
      h.elim (fun h => .inl h) (fun h => .inr (.inl h)))).append
    ((loop (sp := sp) h hb hBound).mono (fun _ h =>
      h.elim (fun h => .inl (Nat.lt_of_lt_of_le h (by decide : batchBytes ≤ frameBytes)))
        (fun h => .inr (.inr h))))).append
    ((final q base sp dst done subOff selectOff).mono (fun _ h =>
      .inl (h.elim (fun h => Nat.lt_of_lt_of_le h (by decide : batchBytes ≤ frameBytes))
        (subregion (by decide : returnAt+4 ≤ frameBytes)))))

end SafegcdTermination.TraceReads
