import SafegcdTermination.InitStackEffect
import SafegcdTermination.TraceReads

namespace SafegcdTermination.LoopStackEffect

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank (addr)
open SafegcdTermination.InitStackEffect
open SafegcdTermination.TraceReads (batchBytes)
open SafegcdTermination.TraceWrites (subregion)
open SafegcdTermination.PublicTrace (stackState publicState)
open SafegcdTermination.BatchSlots (row)
open SafegcdTermination.RunBatch (batchTrace)
open SafegcdTermination.RunRow (rowTrace rowPre)
open SafegcdTermination.RunRows (rowPc rowsTrace)
open M0Crypto.Armv6M (Reg State)
open M0Crypto.Thumb M0Crypto.Sym M0Crypto.Release
open M0Crypto.Release.TraceSpec (BelowEntry AtOrAboveSp)
open M0Crypto.Release.StackEffect

set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

variable {sp0 sp : Word} {n : Nat}

abbrev NoBytes : Word → Prop := fun _ => False

theorem Seg.keep_inputs {X Y : Word → Prop} {tr : List Event}
    (h : Seg sp0 n sp X tr Y) : Seg sp0 n sp X tr (fun y => X y ∨ Y y) := by
  intro q hs hu hx
  obtain ⟨hg,hsp,hkeep,hw⟩ := h q hs hu hx
  exact ⟨hg,hsp,hkeep,fun y hy hb =>
    hy.elim (fun h => hkeep y (hx y h hb)) (fun h => hw y h hb)⟩

theorem Seg.then_keep {X Y : Word → Prop} {a b : List Event}
    (h : Seg sp0 n sp X a Y) (hNext : Seg sp0 n sp Y b NoBytes) :
    Seg sp0 n sp X (a ++ b) Y :=
  (h.append (hNext.mono (fun _ h => .inr h) (fun _ h => h))).mono (fun _ h => h) (fun _ h => .inl h)

private theorem block_preserves {is : List Instr} {ini fp : List (SExpr × Nat)} {X : Word → Prop} {s : State}
    (chk : blkChk ini [] fp is = true)
    (hi : ∀ y, InR s ini y → X y)
    (hf : ∀ y, InR s fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    Seg sp0 n sp X (traceAll is s) NoBytes :=
  (blk_seg chk s hi hf).mono (fun _ h => h) (fun _ h => False.elim h)

private theorem quiet_trace (is : List Instr) (pc : Word) {X : Word → Prop}
    (h : is.all (fun i => !i.dsts.contains 13) = true) :
    Seg sp0 n sp X (annotate pc is []) NoBytes := by
  induction is generalizing pc with
  | nil =>
    intro q hs hu _
    exact ⟨trivial,hs,fun _ h => h,fun _ h => False.elim h⟩
  | cons i is ih =>
    obtain ⟨hi,ht⟩ := Bool.and_eq_true_iff.mp h
    exact ((quiet (e := ⟨pc,i,[]⟩) hi rfl).cat (ih _ ht)).mono (fun _ h => h)
      (fun _ h => False.elim h)

abbrev MatrixBytes (sp : Word) := Region (addr sp matrixAt) 16

private theorem prepare_matrix (pc : Word) (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (Initialized sp) (traceAll (prepareMatrix (phases 0)) (stackState pc sp)) NoBytes := by
  let slots := [(bankF,8),(bankG,8),(deltaAt,4)]
  apply block_preserves (ini := spRg slots) (fp := spRg slots) (by decide +kernel)
  · intro y hy
    obtain ⟨r,hr,hR⟩ := stack_regions.mp hy
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (.inl (subregion (by decide : bankF+8 ≤ 4*vectorBytes) hR)))
    · exact .inr (.inr (.inl (subregion (by decide : bankG+8 ≤ 4*vectorBytes) hR)))
    · exact .inr (.inr (.inr (.inl hR)))
  · exact fun y h => hA y (stack_region_bound (by decide) h)

private theorem save_matrix (pc : Word) (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (Initialized sp) (traceAll saveMatrix (stackState pc sp)) (MatrixBytes sp) :=
  (blk_seg (ini := []) (wo := spRg [(matrixAt,16)]) (fp := spRg [(deltaAt,4),(matrixAt,16)])
    (by decide +kernel) (stackState pc sp) (X := Initialized sp) (fun _ h => False.elim (no_region h))
    (fun y h => hA y (stack_region_bound (by decide) h))).mono (fun _ h => h)
      (fun _ h => stack_regions.mpr ⟨_,List.mem_singleton_self _,h⟩)

private theorem first_row_prepare (pc : Word) (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (MatrixBytes sp) (traceAll (prepareRow (row 0 0)) (stackState pc sp)) NoBytes := by
  let slots := [(matrixAt,16)]
  apply block_preserves (ini := spRg slots) (fp := spRg slots) (by decide +kernel)
  · intro y hy
    obtain ⟨r,hr,hR⟩ := stack_regions.mp hy
    rw [List.mem_singleton] at hr
    subst r
    exact hR
  · exact fun y h => hA y (stack_region_bound (by decide) h)

abbrev FullTemp (sp : Word) := Region (addr sp temp) vectorBytes

private theorem first_row_leaf (pc : Word)
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (InitialBanks sp) (predictedBody
      ⟨addr sp temp,addr sp bankF,addr sp bankG,0,0,0,0,0⟩ pc false) (FullTemp sp) := by
  let s := publicState [(15,pc),(0,addr sp temp),(1,addr sp bankF),(2,addr sp bankG)]
  let q := Pins.load s false
  change Seg sp0 n sp _ (predictedBody q s.pc false) _
  rw [← trace_body s false]
  let r : List (SExpr × Nat) := [(.reg0 1,vectorBytes),(.reg0 2,vectorBytes)]
  let out : List (SExpr × Nat) := [(.reg0 0,vectorBytes)]
  have hBound : ∀ y, InR s r y → InitialBanks sp y := by
    intro y ⟨p,hp,o,ho,he⟩
    simp only [r,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact subregion (by decide : bankF+vectorBytes ≤ 4*vectorBytes) (Region.mk ho he)
    · exact subregion (by decide : bankG+vectorBytes ≤ 4*vectorBytes) (Region.mk ho he)
  have hWrites : ∀ y, InR s out y → FullTemp sp y := by
    intro y ⟨p,hp,o,ho,he⟩
    have hp' := List.mem_singleton.mp hp
    subst p
    exact Region.mk ho he
  have hAcc : ∀ y, InR s (out ++ r) y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y := by
    intro y hy
    rcases (inR_append (den := (·.denote s))).mp hy with h | h
    · exact hA y (subregion (by decide : temp+vectorBytes ≤ frameBytes) (hWrites y h))
    · exact hA y (Nat.lt_of_lt_of_le (hBound y h) (by decide : 4*vectorBytes ≤ frameBytes))
  exact (blk_seg (ini := r) (wo := out) (fp := out ++ r) (by decide +kernel)
    s (X := InitialBanks sp) hBound hAcc).mono (fun _ h => h) (fun _ h => inR_one h)

/-- Once the read footprint is initialized, the effect needs no further
    symbolic execution. The output set contains each byte written by the trace. -/
theorem closed {R W : Word → Prop} {tr : List Event}
    (hR : ReadsFrom R tr) (hW : WritesTo W tr)
    (hSp : ∀ e ∈ tr, (!(e.instr.dsts.contains 13)) = true)
    (hA : Above sp0 n sp (fun y => R y ∨ W y)) :
    Seg sp0 n sp R tr (fun y => ∃ e ∈ tr, Writes e.accesses y) := by
  induction tr with
  | nil =>
    intro q hs hu _
    refine ⟨trivial,hs,fun _ h => h,?_⟩
    rintro y ⟨_,h,_⟩
    exact False.elim (List.not_mem_nil h)
  | cons e tr ih =>
    have hm := List.mem_cons_self (l := tr) (a := e)
    obtain ⟨heSp,heExact⟩ := keep_sp (hSp e hm) sp
    have hHead : Seg sp0 n sp R [e] (Writes e.accesses) :=
      ev_seg heExact heSp (fun y h => hA y (h.imp (hR e hm y) (hW e hm y)))
        (fun y h _ => hR e hm y h)
    have hTail := ih (fun f hf => hR f (List.mem_cons_of_mem _ hf))
      (fun f hf => hW f (List.mem_cons_of_mem _ hf))
      (fun f hf => hSp f (List.mem_cons_of_mem _ hf))
    exact (hHead.cat hTail).mono (fun _ h => h) (fun y ⟨f,hf,hw⟩ =>
      (List.mem_cons.mp hf).elim (fun eq => .inl (eq ▸ hw)) (fun hf => .inr ⟨f,hf,hw⟩))

private def matrixTrace (q : Targets) (base sp : Word) (entry : Nat) : List Event :=
  let is := prepareMatrix (phases 0)
  let call := entry+seqSize is
  let leaf := base+BitVec.ofNat 32 q.matrix
  traceAll is (stackState (base+BitVec.ofNat 32 entry) sp) ++
    (⟨base+BitVec.ofNat 32 call,callTo call q.matrix,[]⟩ ::
      (annotate leaf MatrixCode.body [] ++ [⟨nextPC leaf MatrixCode.body,.bx 14,[]⟩])) ++
    traceAll saveMatrix (stackState (base+BitVec.ofNat 32 (saveOff q entry (phases 0))) sp)

private theorem matrix_effect (q : Targets) (base : Word) (entry : Nat)
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (Initialized sp) (matrixTrace q base sp entry) (MatrixBytes sp) := by
  unfold matrixTrace
  let is := prepareMatrix (phases 0)
  let call := entry+seqSize is
  let leaf := base+BitVec.ofNat 32 q.matrix
  have hCall : Seg sp0 n sp (Initialized sp)
      [⟨base+BitVec.ofNat 32 call,callTo call q.matrix,[]⟩] NoBytes :=
    quiet (by rfl) rfl
  have hRet : Seg sp0 n sp (Initialized sp)
      [⟨nextPC leaf MatrixCode.body,.bx 14,[]⟩] NoBytes :=
    quiet (by rfl) rfl
  have hMat := quiet_trace (sp0 := sp0) (n := n) (sp := sp) (X := Initialized sp) MatrixCode.body leaf (by decide +kernel)
  exact ((((prepare_matrix _ hA).cat (hCall.cat (hMat.cat hRet))).cat (save_matrix _ hA))).mono
    (fun _ h => h) (fun _ h => .inr h)

private theorem first_row (q : Targets) (base : Word) (off : Nat)
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (fun y => MatrixBytes sp y ∨ InitialBanks sp y)
      (rowTrace q base sp off (row 0 0)) (FullTemp sp) := by
  let call := off+seqSize (rowPre q off (row 0 0))
  let leaf := base+BitVec.ofNat 32 q.exact
  let R := fun y => MatrixBytes sp y ∨ InitialBanks sp y
  have hCall : Seg sp0 n sp R
      [⟨base+BitVec.ofNat 32 call,callTo call q.exact,[]⟩] NoBytes := quiet (by rfl) rfl
  have hRet : Seg sp0 n sp R
      [⟨nextPC leaf (body false),.bx 12,[]⟩] NoBytes := quiet (by rfl) rfl
  have hPre := (first_row_prepare (base+BitVec.ofNat 32 off) hA).mono (X' := R) (Y := NoBytes)
    (fun _ h => .inl h) (fun _ h => h)
  have hCore := (first_row_leaf leaf hA).mono (X' := R) (Y := FullTemp sp)
    (fun _ h => .inr h) (fun _ h => h)
  have h := (hPre.cat (hCall.cat (hCore.cat hRet))).mono (X' := R) (Y' := FullTemp sp)
    (fun _ h => h) (fun _ h => .inr (.inr (.inl h)))
  simpa only [rowTrace, rowPre, show (row 0 0).modular = false by decide,
    show (row 0 0).dst = temp by decide, show (row 0 0).x = bankF by decide,
    show (row 0 0).y = bankG by decide, Bool.false_eq_true,
    ite_false,List.append_nil,call,leaf,List.singleton_append] using h

private def firstRowPrefix (q : Targets) (base sp : Word) (entry : Nat) : List Event :=
  matrixTrace q base sp entry ++
    rowTrace q base sp (rowPc q (firstRow q entry (phases 0)) 0 0) (row 0 0)

private theorem offset_region {y : Word} {o lo w : Nat}
    (hy : y = sp + BitVec.ofNat 32 o) (hlo : lo ≤ o) (hhi : o < lo+w) :
    Region (addr sp lo) w y := by
  apply Region.mk (o := o-lo) (by omega)
  rw [addr,ofNat_add_assoc,show lo+(o-lo) = o by omega]
  exact hy

private theorem covered_prefix {y : Word} (h : Region sp batchBytes y) :
    Initialized sp y ∨ MatrixBytes sp y ∨ FullTemp sp y := by
  obtain ⟨o,ho,hA⟩ := h.exists
  have h0 : temp = 4*vectorBytes := rfl
  have h1 : outputAt = temp+vectorBytes := by decide
  have h2 : deltaAt = outputAt+4 := rfl
  have h3 : counterAt = deltaAt+4 := rfl
  have h4 : matrixAt = counterAt+4 := rfl
  have h5 : batchBytes = matrixAt+16 := rfl
  by_cases ht : o < temp
  · exact .inl (.inr (.inr (.inl (Region.mk (by omega) hA))))
  by_cases hT : o < outputAt
  · exact .inr (.inr (offset_region hA (by omega) (by omega)))
  by_cases hO : o < deltaAt
  · exact .inl (.inl (.inl (offset_region hA (by omega) (by omega))))
  by_cases hD : o < counterAt
  · exact .inl (.inr (.inr (.inr (.inl (offset_region hA (by omega) (by omega))))))
  by_cases hC : o < matrixAt
  · exact .inl (.inr (.inr (.inr (.inr (offset_region hA (by omega) (by omega))))))
  exact .inr (.inl (offset_region hA (by omega) (by omega)))

private theorem prefix_effect (q : Targets) (base : Word) (entry : Nat)
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (Initialized sp) (firstRowPrefix q base sp entry) (Region sp batchBytes) := by
  have hM := matrix_effect q base entry hA
  have hR := first_row q base (rowPc q (firstRow q entry (phases 0)) 0 0) hA
  have h := hM.append (hR.mono (fun y hy => hy.elim (fun hm => .inr hm)
    (fun hb => .inl (.inr (.inr (.inl hb))))) (fun _ h => h))
  exact (Seg.keep_inputs h).mono (fun _ h => h) (fun _ h => covered_prefix h)

open SafegcdTermination.Run43 (tripletTrace tripletsTrace loopTrace)
open SafegcdTermination.LoopCounter (triplets)
open SafegcdTermination.LoopControl (countTrace bTo)
open SafegcdTermination.LoopLinks (phaseAt counterSite backSite)
open SafegcdTermination.Literal (LiteralLinks)
open SafegcdTermination.TraceReads (LoopReads)

private theorem first_triplet (q : Targets) (base sp : Word) (entry done k : Nat) :
    ∃ rest, tripletsTrace q base sp entry done (k+1) = tripletTrace q base sp entry done ++ rest := by
  induction k with
  | zero => exact ⟨[],by simp only [tripletsTrace,List.nil_append,List.append_nil]⟩
  | succ k ih =>
    obtain ⟨rest,h⟩ := ih
    exact ⟨rest ++ tripletTrace q base sp entry done,by rw [tripletsTrace,h,List.append_assoc]⟩

private theorem starts_with_row (q : Targets) (base sp : Word) (entry done : Nat) :
    ∃ rest, loopTrace q base sp entry done = firstRowPrefix q base sp entry ++ rest := by
  have hStart : ∃ rest, tripletTrace q base sp entry done = firstRowPrefix q base sp entry ++ rest := by
    let start := firstRow q entry (phases 0)
    let rt (i : Nat) := rowTrace q base sp (rowPc q start 0 i) (row 0 (Fin.ofNat 4 i))
    let back := backSite q entry done
    refine ⟨rt 1 ++ rt 2 ++ rt 3 ++ countTrace base sp (counterSite q entry) done false ++
      batchTrace q base sp (phaseAt q entry done 1) 1 ++ batchTrace q base sp (phaseAt q entry done 2) 2 ++
      [⟨base+BitVec.ofNat 32 back,bTo back entry,[]⟩],?_⟩
    simp only [tripletTrace,batchTrace,rowsTrace,firstRowPrefix,matrixTrace,start,rt,back,
      List.nil_append,List.append_assoc]
    rfl
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by decide : triplets ≠ 0)
  obtain ⟨a,ha⟩ := first_triplet q base sp entry done k
  obtain ⟨b,hb⟩ := hStart
  refine ⟨b ++ a ++ batchTrace q base sp entry 0 ++
    countTrace base sp (counterSite q entry) done true,?_⟩
  simp only [loopTrace,hk,ha,hb,List.append_assoc]

/-- The first row fills the temporary bank. From then on, only the initialized
    banks and control words and the public correction literal are read. -/
theorem loop {code : List (BitVec 8)} {q : Targets} {base : Word} {entry done : Nat}
    (h : LiteralLinks code q entry done) (hBase : base.toNat % 4 = 0)
    (hSp : ∀ e ∈ loopTrace q base sp entry done, (!(e.instr.dsts.contains 13)) = true)
    (hA : Above sp0 n sp (fun y => Region sp frameBytes y ∨ Region (base+BitVec.ofNat 32 q.literal) 4 y)) :
    Seg sp0 n sp (fun y => Initialized sp y ∨ Region (base+BitVec.ofNat 32 q.literal) 4 y)
      (loopTrace q base sp entry done) (Region sp batchBytes) := by
  obtain ⟨rest,hr⟩ := starts_with_row q base sp entry done
  let L := Region (base+BitVec.ofNat 32 q.literal) 4
  let In := fun y => Initialized sp y ∨ L y
  let Ready := fun y => Region sp batchBytes y ∨ L y
  have hInit : Seg sp0 n sp In (firstRowPrefix q base sp entry) (Region sp batchBytes) :=
    (prefix_effect q base entry (fun y h => hA y (.inl h))).mono (fun _ h => .inl h) (fun _ h => h)
  have hStart : Seg sp0 n sp In (firstRowPrefix q base sp entry) Ready :=
    (Seg.keep_inputs hInit).mono (fun _ h => h) (fun _ h => h.elim .inr (fun hb => .inl (.inr hb)))
  have hReads : ReadsFrom Ready rest := by
    have r := TraceReads.loop (sp := sp) h hBase
    intro e he
    exact r e (by rw [hr]; exact List.mem_append_right _ he)
  have hWrites : WritesTo (Region sp frameBytes) rest := by
    intro e he
    exact LoopFootprint.loop_writes q base sp entry done e (by rw [hr]; exact List.mem_append_right _ he)
  have hRest : Seg sp0 n sp Ready rest NoBytes :=
    (closed hReads hWrites (fun e he => hSp e (by rw [hr]; exact List.mem_append_right _ he))
      (fun y h => hA y (h.elim (fun h => h.elim
        (fun hb => .inl (Nat.lt_of_lt_of_le hb (by decide : batchBytes ≤ frameBytes))) .inr) .inl))).mono
      (fun _ h => h) (fun _ h => False.elim h)
  rw [hr]
  exact (Seg.then_keep hStart hRest).mono (fun _ h => h) (fun _ h => .inl h)

end SafegcdTermination.LoopStackEffect
