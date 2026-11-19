import SafegcdTermination.Run43
import SafegcdTermination.TraceWrites

namespace SafegcdTermination.LoopFootprint

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.PublicTrace SafegcdTermination.TraceWrites
open SafegcdTermination.LoopCounter SafegcdTermination.LoopControl SafegcdTermination.Run43
open SafegcdTermination.LoopLinks (counterSite)
open SafegcdTermination.RunRow SafegcdTermination.RunRows SafegcdTermination.RunBatch
open SafegcdTermination.BatchSlots (row row_layout)
open M0Crypto.Thumb
open M0Crypto.Release (Region WritesTo)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

abbrev FrameWrites (sp : Word) := WritesTo (Region sp frameBytes)

theorem fold_writes (pc a : Word) : WritesTo (Region a vectorBytes) (FoldCode.predictedTrace pc a) := by
  let s := publicState [(15,pc),(0,a)]
  change WritesTo _ (FoldCode.predictedTrace s.pc (s.regs 0))
  rw [FoldCode.predicted_eq s]
  exact (frame (s := s) (r := 0) (by decide) (by decide +kernel)).append (event rfl)

theorem row_body_writes (p : Pins) (pc : Word) (modular : Bool) :
    WritesTo (Region p.out vectorBytes) (predictedBody p pc modular) := by
  have h := body_trace_in p pc modular
  intro e he x hx
  obtain ⟨a,ha,hw,k,hk,rfl⟩ := hx
  obtain ⟨i,hi,ha' | ha' | ha'⟩ := h e he a ha
  · cases ha'
    cases hw
  · cases ha'
    cases hw
  · subst a
    apply Region.mk (o := 4*i+k)
    · change k < 4 at hk
      unfold vectorBytes
      omega
    · simp only [storeAt,M0Crypto.Armv6M.slot,ofNat_add_assoc]

theorem call_row_writes (q : Targets) (base sp : Word) (off : Nat) (r : RowCall) (h : InSlot r.dst) :
    FrameWrites sp (rowTrace q base sp off r) := by
  have hPre : ∀ W : Word → Prop, WritesTo W (traceAll (rowPre q off r) (stackState (base+BitVec.ofNat 32 off) sp)) := by
    intro W
    cases hMod : r.modular
    · refine TraceWrites.quiet (W := W) ?_ ?_ <;> simp only [rowPre,hMod,Bool.false_eq_true,ite_false] <;> rfl
    · refine TraceWrites.quiet (W := W) ?_ ?_ <;> simp only [rowPre,hMod,ite_true] <;> rfl
  have hLift : ∀ a, Region (addr sp r.dst) vectorBytes a → Region sp frameBytes a :=
    fun a hA => subregion h.1 hA
  have hFold : ∀ pc, FrameWrites sp (FoldCode.predictedTrace pc (addr sp r.dst)) :=
    fun pc => (fold_writes pc _).mono hLift
  have hBody : ∀ pc, FrameWrites sp (predictedBody ⟨addr sp r.dst,addr sp r.x,addr sp r.y,0,0,0,0,0⟩ pc r.modular) :=
    fun pc => (row_body_writes _ pc _).mono hLift
  let call := off+seqSize (rowPre q off r)
  let dest := if r.modular then q.modular else q.exact
  let leaf := base+BitVec.ofNat 32 dest
  let foldPC := call+4+seqSize (prepareFold r)
  have hMore : FrameWrites sp (if r.modular then
      traceAll (prepareFold r) (stackState (base+BitVec.ofNat 32 (call+4)) sp) ++
        (⟨base+BitVec.ofNat 32 foldPC,callTo foldPC q.fold,[]⟩ ::
          FoldCode.predictedTrace (base+BitVec.ofNat 32 q.fold) (addr sp r.dst)) else []) := by
    split
    · have prep : FrameWrites sp (traceAll (prepareFold r) (stackState (base+BitVec.ofNat 32 (call+4)) sp)) :=
        TraceWrites.quiet (by rfl) (by rfl)
      exact prep.append ((branch (base+BitVec.ofNat 32 foldPC) (callTo foldPC q.fold)).append (hFold _))
    · exact WritesTo.nil _
  have hLeaf := (branch (base+BitVec.ofNat 32 call) (callTo call dest)).append
    ((hBody leaf).append (branch (nextPC leaf (body r.modular)) (.bx 12)))
  exact ((hPre _).append hLeaf).append hMore

private theorem row_slots_bound (phase : Fin 3) (i : Fin 4) : InSlot (row phase i).dst := by
  unfold InSlot
  have h : ∀ (j : Fin 3) (k : Fin 4), (row j k).dst + vectorBytes ≤ frameBytes ∧ (row j k).dst % 4 = 0 := by
    decide +kernel
  exact h phase i

theorem rows_writes (q : Targets) (base sp : Word) (entry : Nat) (phase : Fin 3) (n : Nat) :
    FrameWrites sp (rowsTrace q base sp entry phase n) := by
  induction n with
  | zero => exact WritesTo.nil _
  | succ n ih => exact ih.append (call_row_writes q base sp _ _ (row_slots_bound _ _))

private theorem annotate_quiet {W : Word → Prop} (pc : Word) (is : List Instr) : WritesTo W (annotate pc is []) := by
  induction is generalizing pc with
  | nil => exact WritesTo.nil _
  | cons i is ih => exact (event rfl).append (ih _)

theorem batch_writes (q : Targets) (base sp : Word) (entry : Nat) (phase : Fin 3) :
    FrameWrites sp (batchTrace q base sp entry phase) := by
  unfold batchTrace
  have first : FrameWrites sp (traceAll (prepareMatrix (phases phase)) (stackState (base+BitVec.ofNat 32 entry) sp)) := by
    refine TraceWrites.quiet (MatrixCall.matrix_pre_falls phase) ?_
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  have saved (pc : Word) : FrameWrites sp (traceAll saveMatrix (stackState pc sp)) :=
    frame (r := 13) (by decide) (by decide +kernel)
  let call := entry+seqSize (prepareMatrix (phases phase))
  let leaf := base+BitVec.ofNat 32 q.matrix
  have hCall := (branch (base+BitVec.ofNat 32 call) (callTo call q.matrix)).append
    ((annotate_quiet (W := Region sp frameBytes) leaf MatrixCode.body).append
      (branch (nextPC leaf MatrixCode.body) (.bx 14)))
  exact (((first.append hCall).append (saved (base+BitVec.ofNat 32 (saveOff q entry (phases phase))))).append
    (rows_writes q base sp (firstRow q entry (phases phase)) phase 4))

theorem count_writes (base sp : Word) (off done : Nat) (last : Bool) :
    FrameWrites sp (countTrace base sp off done last) := by
  have hCmd : FrameWrites sp (traceAll updateCounter (stackState (base+BitVec.ofNat 32 off) sp)) :=
    frame (r := 13) (by decide) (by decide +kernel)
  let o := off+seqSize updateCounter
  have test := branch (W := Region sp frameBytes) (base+BitVec.ofNat 32 o) (.bcond 1 0)
  cases last
  · simpa only [countTrace,Bool.false_eq_true,ite_false,List.append_nil,o] using hCmd.append test
  · exact (hCmd.append test).append (branch (base+BitVec.ofNat 32 (o+2)) (bTo (o+2) done))

theorem triplet_writes (q : Targets) (base sp : Word) (entry done : Nat) :
    FrameWrites sp (tripletTrace q base sp entry done) := by
  let back := LoopLinks.backSite q entry done
  exact ((((batch_writes q base sp entry 0).append (count_writes base sp (counterSite q entry) done false)).append
    (batch_writes q base sp (LoopLinks.phaseAt q entry done 1) 1)).append
    (batch_writes q base sp (LoopLinks.phaseAt q entry done 2) 2)).append (branch (base+BitVec.ofNat 32 back) (bTo back entry))

theorem triplets_writes (q : Targets) (base sp : Word) (entry done : Nat) (n : Nat) :
    FrameWrites sp (tripletsTrace q base sp entry done n) := by
  induction n with
  | zero => exact WritesTo.nil _
  | succ n ih => exact ih.append (triplet_writes q base sp entry done)

theorem loop_writes (q : Targets) (base sp : Word) (entry done : Nat) :
    FrameWrites sp (loopTrace q base sp entry done) :=
  ((triplets_writes q base sp entry done triplets).append (batch_writes q base sp entry 0)).append
    (count_writes base sp (counterSite q entry) done true)

end SafegcdTermination.LoopFootprint
