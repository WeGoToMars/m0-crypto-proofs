import SafegcdTermination.LoopMemory
import SafegcdTermination.RunBatch

namespace SafegcdTermination.LoopLinks

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.LoopCounter (updateCounter)
open SafegcdTermination.LoopControl
open SafegcdTermination.RunRow (LeafLinks)
open M0Crypto.Thumb

def batchEnd (q : Targets) (o : Nat) (phase : Fin 3) : Nat :=
  o + seqSize (batchCode q o (phases phase))

def afterCounter (q : Targets) (entry done : Nat) : Nat :=
  let o := batchEnd q entry 0
  o + seqSize (countControl o done)

def phaseAt (q : Targets) (entry done : Nat) : Fin 3 → Nat
  | 0 => entry
  | 1 => afterCounter q entry done
  | _ => batchEnd q (afterCounter q entry done) 1

def counterSite (q : Targets) (entry : Nat) : Nat := batchEnd q entry 0

def backSite (q : Targets) (entry done : Nat) : Nat := batchEnd q (phaseAt q entry done 2) 2

structure Place (code : List (BitVec 8)) (q : Targets) (entry done : Nat) : Prop where
  leaves : LeafLinks code q
  phase : ∀ i, let o := phaseAt q entry done i; seqAt code o (batchCode q o (phases i)) = true
  count : seqAt code (counterSite q entry) (countControl (counterSite q entry) done) = true
  countTarget : TargetMatches (counterSite q entry + seqSize updateCounter + 2) done
  back : seqAt code (backSite q entry done) [bTo (backSite q entry done) entry] = true
  backTarget : TargetMatches (backSite q entry done) entry

theorem end_even (q : Targets) {o : Nat} (phase : Fin 3) (h : o % 2 = 0) :
    batchEnd q o phase % 2 = 0 := by
  have he := seqSize_mod_two (batchCode q o (phases phase))
  unfold batchEnd
  omega

theorem phase_even (q : Targets) {entry done : Nat} (h : entry % 2 = 0) (p : Fin 3) :
    phaseAt q entry done p % 2 = 0 := by
  have hE := end_even q 0 h
  have hC := seqSize_mod_two (countControl (batchEnd q entry 0) done)
  have he : afterCounter q entry done % 2 = 0 := by
    change (batchEnd q entry 0 + seqSize (countControl (batchEnd q entry 0) done)) % 2 = 0
    omega
  rcases phase_cases p with rfl | rfl | rfl
  · exact h
  · exact he
  · exact end_even q 1 he

theorem after_counter (q : Targets) (entry done : Nat) :
    afterCounter q entry done = counterSite q entry + seqSize updateCounter + 4 := by
  dsimp only [afterCounter, counterSite, countControl]
  rw [seqSize_append]
  have e : (2 : Nat) + 2 = 4 := rfl
  simp only [seqSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Instr.size,
    bTo, Nat.add_zero, e, Nat.add_assoc]

end SafegcdTermination.LoopLinks
