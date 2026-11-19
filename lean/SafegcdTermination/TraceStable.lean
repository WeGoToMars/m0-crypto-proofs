import SafegcdTermination.EndFootprint

namespace SafegcdTermination.TraceStable

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank (addr)
open SafegcdTermination.PublicTrace (stackState publicState)
open SafegcdTermination.RunRow (rowPre rowTrace)
open SafegcdTermination.RunRows (rowsTrace)
open SafegcdTermination.RunBatch (batchTrace)
open SafegcdTermination.BatchSlots (row)
open SafegcdTermination.Run43 (tripletTrace tripletsTrace loopTrace)
open SafegcdTermination.LoopLinks (counterSite phaseAt backSite)
open SafegcdTermination.LoopControl (countTrace bTo)
open SafegcdTermination.LoopCounter (updateCounter triplets)
open SafegcdTermination.FinalCode SafegcdTermination.FinalPrepare SafegcdTermination.RunFinal
open SafegcdTermination.FinalSub SafegcdTermination.FinalSelect
open SafegcdTermination.Leaf (callTrace leafTrace)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

abbrev Stable (tr : List Event) := ∀ e ∈ tr, (!(e.instr.dsts.contains 13)) = true

private theorem append {a b : List Event} (ha : Stable a) (hb : Stable b) : Stable (a ++ b) :=
  fun e he => (List.mem_append.mp he).elim (ha e) (hb e)

private theorem event (pc : Word) (i : Instr) (hi : (!(i.dsts.contains 13)) = true) :
    Stable [⟨pc,i,[]⟩] := by
  intro e he
  rw [List.mem_singleton] at he
  exact he.symm ▸ hi

private theorem block {is : List Instr} (s : State) (h : is.all (fun i => !i.dsts.contains 13) = true) :
    Stable (traceAll is s) := by
  induction is generalizing s with
  | nil => intro e he; cases he
  | cons i is ih =>
    obtain ⟨hi,ht⟩ := Bool.and_eq_true_iff.mp h
    intro e he
    simp only [traceAll,List.mem_cons] at he
    exact he.elim (fun eq => eq.symm ▸ hi) (fun h => ih (i.next s) ht e h)

private theorem annotate_empty (pc : Word) (is : List Instr)
    (h : is.all (fun i => !i.dsts.contains 13) = true) : Stable (annotate pc is []) := by
  induction is generalizing pc with
  | nil => intro e he; cases he
  | cons i is ih =>
    obtain ⟨hi,ht⟩ := Bool.and_eq_true_iff.mp h
    exact append (event _ _ hi) (ih _ ht)

private theorem fold (pc a : Word) : Stable (FoldCode.predictedTrace pc a) := by
  let s := publicState [(15,pc),(0,a)]
  change Stable (FoldCode.predictedTrace s.pc (s.regs 0))
  rw [FoldCode.predicted_eq s]
  exact append (block s (by decide +kernel)) (event _ _ rfl)

private theorem row_body (pc dst x y : Word) (m : Bool) :
    Stable (predictedBody ⟨dst,x,y,0,0,0,0,0⟩ pc m) := by
  let s := publicState [(15,pc),(0,dst),(1,x),(2,y)]
  cases m
  · change Stable (predictedBody (Pins.load s false) s.pc false)
    rw [← trace_body s false]
    exact block s (by decide +kernel)
  · change Stable (predictedBody (Pins.load s true) s.pc true)
    rw [← trace_body s true]
    exact block s (by decide +kernel)

private theorem one_row (q : Targets) (base sp : Word) (off : Nat) (r : RowCall) :
    Stable (rowTrace q base sp off r) := by
  let pre := rowPre q off r
  let call := off+seqSize pre
  let dest := if r.modular then q.modular else q.exact
  let leaf := base+BitVec.ofNat 32 dest
  have hp : pre.all (fun i => !i.dsts.contains 13) = true := by
    unfold pre rowPre
    split <;> rfl
  have h := append (block (stackState (base+BitVec.ofNat 32 off) sp) hp)
    (append (event (base+BitVec.ofNat 32 call) (callTo call dest) rfl)
      (append (row_body leaf (addr sp r.dst) (addr sp r.x) (addr sp r.y) r.modular)
        (event (nextPC leaf (body r.modular)) (.bx 12) rfl)))
  unfold rowTrace
  apply append h
  split
  · exact append (block _ rfl) (append (event _ _ rfl) (fold _ _))
  · intro e he
    cases he

private theorem rows (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3) (n : Nat) :
    Stable (rowsTrace q base sp off phase n) := by
  induction n with
  | zero => intro e he; cases he
  | succ n ih => exact append ih (one_row _ _ _ _ _)

private theorem batch (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3) :
    Stable (batchTrace q base sp off phase) := by
  unfold batchTrace
  let call := off + seqSize (prepareMatrix (phases phase))
  let leaf := base + BitVec.ofNat 32 q.matrix
  have h := append (event (base+BitVec.ofNat 32 call) (callTo call q.matrix) rfl)
    (append (annotate_empty leaf MatrixCode.body (by decide +kernel))
      (event (nextPC leaf MatrixCode.body) (.bx 14) rfl))
  exact append (append (append (block _ rfl) h)
    (block _ (by decide))) (rows _ _ _ _ _ _)

private theorem counter (base sp : Word) (off done : Nat) (last : Bool) :
    Stable (countTrace base sp off done last) := by
  cases last
  · simpa only [countTrace,Bool.false_eq_true,ite_false,List.append_nil] using
      append (block (stackState (base+BitVec.ofNat 32 off) sp) (is := updateCounter) (by decide))
        (event (base+BitVec.ofNat 32 (off+seqSize updateCounter)) (.bcond 1 0) rfl)
  · exact append (append (block _ (by decide)) (event _ _ rfl)) (event _ _ rfl)

theorem loop (q : Targets) (base sp : Word) (entry done : Nat) :
    Stable (loopTrace q base sp entry done) := by
  have ht : Stable (tripletTrace q base sp entry done) :=
    append (append (append (append (batch _ _ _ _ _) (counter _ _ _ _ _))
      (batch _ _ _ _ _)) (batch _ _ _ _ _)) (event _ _ rfl)
  have hs (k : Nat) : Stable (tripletsTrace q base sp entry done k) := by
    induction k with
    | zero => intro e he; cases he
    | succ k ih => exact append ih ht
  exact append (append (hs triplets) (batch _ _ _ _ _)) (counter _ _ _ _ _)

private theorem call {is : List Instr} {base : Word} {off dest : Nat} {s : State}
    (hi : is.all (fun i => !i.dsts.contains 13) = true) :
    Stable (callTrace is base off dest s) :=
  append (event _ _ rfl) (append (block s hi) (event _ _ rfl))

theorem final (q : Targets) (base sp dst : Word) (off subOff selectOff : Nat) :
    Stable (finalTrace q base sp dst off subOff selectOff) := by
  unfold finalTrace
  have hSub : Stable (subTrace base sp (subSite off) subOff) := call (by decide +kernel)
  have hSelect : Stable (selectTrace base sp dst (selectSite off) selectOff) :=
    append (block _ (by decide)) (call (by decide +kernel))
  exact append (append (append (append (append (block _ (by decide)) (append (event _ _ rfl) (fold _ _)))
    (block _ (by decide +kernel))) hSub) hSelect) (append (block _ (by decide)) (event _ _ rfl))

end SafegcdTermination.TraceStable
