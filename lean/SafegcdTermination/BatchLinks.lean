import SafegcdTermination.BatchSlots
import SafegcdTermination.ModularCalls
import SafegcdTermination.FoldCall

namespace SafegcdTermination.BatchLinks

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.BatchSlots (row)
open M0Crypto.Thumb

def rowOffset (q : Targets) (off : Nat) : List RowCall → Nat → Nat
  | [], _ => off
  | _ :: _, 0 => off
  | r :: rs, i+1 => rowOffset q (off + seqSize (rowCode q off r)) rs i

theorem row_links {code : List (BitVec 8)} (q : Targets) (off : Nat)
    (rs : List RowCall) (h : seqAt code off (rowsCode q off rs) = true) (i : Nat) (hi : i < rs.length) :
    seqAt code (rowOffset q off rs i) (rowCode q (rowOffset q off rs i) rs[i]) = true := by
  induction rs generalizing off i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [rowsCode, seqAt_append, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      exact ih (off + seqSize (rowCode q off r)) h.2 i (by simpa using hi)

theorem batch_links {code : List (BitVec 8)} (q : Targets) (off : Nat) (b : Banks)
    (h : seqAt code off (batchCode q off b) = true) :
    seqAt code off (matrixPre off q.matrix b) = true ∧
    seqAt code (saveOff q off b) saveMatrix = true ∧
    seqAt code (firstRow q off b) (rowsCode q (firstRow q off b) (rowCalls b)) = true := by
  simp only [batchCode, List.append_assoc, seqAt_append, Bool.and_eq_true] at h
  exact h

end SafegcdTermination.BatchLinks
