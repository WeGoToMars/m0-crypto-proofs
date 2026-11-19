import SafegcdTermination.InitWords
import M0Crypto.Release.Field25519CRLoop

namespace SafegcdTermination.SplitInput

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.InitCode
open SafegcdTermination.InitWords
open SafegcdTermination.Bank
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.Packing
open M0Crypto.Armv6M (State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr read32_storeWords_same)
open M0Crypto.Release.Field25519CR (storeWords_snoc)
open M0Crypto.Release.Field25519Routines (feVal)

set_option maxHeartbeats 850000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

def splitWords (s : State) (n : Nat) : List Word :=
  (List.range n).flatMap fun i =>
    let x := stackWord s (temp+4*i)
    [low x, x >>> 16]

theorem split_next (s : State) (n : Nat) :
    splitWords s (n+1) = splitWords s n ++
      [low (stackWord s (temp+4*n)), stackWord s (temp+4*n) >>> 16] := by
  simp [splitWords, List.range_succ]

theorem split_length (s : State) (n : Nat) : (splitWords s n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [split_next, List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, ih, Nat.mul_succ]

theorem split_read_old (s : State) (n i : Nat) (hn : n ≤ 8) (hi : i < 8) :
    read32 (storeWords s.mem (addr s.sp bankG) (splitWords s n)) (addr s.sp (temp+4*i)) =
      stackWord s (temp+4*i) := by
  apply read32_congr
  intro k hk
  apply storeWords_other
  intro j b hj hb
  rw [split_length] at hj
  simp only [addr, ofNat_add_assoc]
  have hG : bankG = 68 := rfl
  have hT : temp = 272 := rfl
  exact addr_sep s.sp (by omega) (by omega) (by omega)

theorem split_exec (s : State) (n : Nat) (hn : n ≤ 8) :
    let t := execAll ((List.range n).flatMap splitColumn) s
    t.sp = s.sp ∧ t.mem = storeWords s.mem (addr s.sp bankG) (splitWords s n) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hSp,hMem⟩ := ih (by omega)
    dsimp only
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, execAll_append]
    let u := execAll ((List.range n).flatMap splitColumn) s
    obtain ⟨hS,hM⟩ := split_column u n (by omega)
    have hW : stackWord u (temp+4*n) = stackWord s (temp+4*n) := by
      change read32 u.mem (addr u.sp (temp+4*n)) = _
      rw [show u.sp = s.sp from hSp, show u.mem = _ from hMem]
      exact split_read_old s n n (by omega) (by omega)
    refine ⟨hS.trans hSp, ?_⟩
    rw [hM, hW, show u.sp = s.sp from hSp, show u.mem = _ from hMem, split_next,
      show [low (stackWord s (temp+4*n)), stackWord s (temp+4*n) >>> 16] =
          [low (stackWord s (temp+4*n))] ++ [stackWord s (temp+4*n) >>> 16] from rfl,
      ← List.append_assoc, storeWords_snoc, storeWords_snoc]
    simp only [split_length, List.length_append, List.length_cons, List.length_nil,
      addr, ofNat_add_assoc, Nat.mul_add, Nat.mul_comm 4 2, Nat.mul_one, Nat.mul_assoc, Nat.add_assoc, Nat.mul_zero, Nat.zero_add, show 4 * (2*n) = 8*n by omega]

theorem split_pair {s : State} {n i : Nat} (hi : i < n) :
    let w := stackWord s (temp+4*i)
    (splitWords s n)[2*i]'(by rw [split_length]; omega) = low w ∧
      (splitWords s n)[2*i+1]'(by rw [split_length]; omega) = w >>> 16 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · simp only [split_next, List.getElem_append_left (show 2*i < (splitWords s n).length by rw [split_length]; omega),
        List.getElem_append_left (show 2*i+1 < (splitWords s n).length by rw [split_length]; omega)]
      exact ih h
    · simp only [split_next, List.getElem_append_right (by rw [split_length]; exact Nat.le_refl _ : (splitWords s i).length ≤ 2*i),
        List.getElem_append_right (by rw [split_length]; omega : (splitWords s i).length ≤ 2*i+1),
        split_length, Nat.sub_self, Nat.add_sub_cancel_left, List.getElem_cons_zero, List.getElem_cons_succ, true_and]

theorem split_limbs (s : State) (i : Nat) (hi : i < 8) :
    let m := (execAll putInput s).mem
    let w := stackWord s (temp+4*i)
    vec m (addr s.sp bankG) (2*i) = low w ∧
      vec m (addr s.sp bankG) (2*i+1) = w >>> 16 := by
  have hM := (split_exec s 8 (by decide)).2
  have E : (execAll putInput s).mem = _ := hM
  rw [E]
  have hL : (splitWords s 8).length ≤ 2^28 := by rw [split_length]; decide
  have e₀ := read32_storeWords_same s.mem (addr s.sp bankG) (splitWords s 8) (2*i)
    (by rw [split_length]; omega) hL
  have e₁ := read32_storeWords_same s.mem (addr s.sp bankG) (splitWords s 8) (2*i+1)
    (by rw [split_length]; omega) hL
  exact ⟨e₀.trans (split_pair hi).1,e₁.trans (split_pair hi).2⟩

theorem split_value (s : State) (m : Mem)
    (hLimbs : ∀ i < 8, vec m (addr s.sp bankG) (2*i) = low (stackWord s (temp+4*i)) ∧
      vec m (addr s.sp bankG) (2*i+1) = stackWord s (temp+4*i) >>> 16)
    (hTop : vec m (addr s.sp bankG) 16 = 0#32) :
    value m (addr s.sp bankG) = feVal s.mem (addr s.sp temp) := by
  apply vector_packed _ _ _ _ hTop
  intro i hi
  obtain ⟨hLo,hHi⟩ := hLimbs i hi
  rw [hLo,hHi]
  have hh : vec s.mem (addr s.sp temp) i = stackWord s (temp+4*i) := stack_vec _ _ _
  rw [hh]
  exact (halves_value (stackWord s (temp+4*i))).symm

end SafegcdTermination.SplitInput
