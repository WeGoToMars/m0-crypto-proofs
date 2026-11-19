import M0Crypto.Thumb.SeqScan

/-!
Decoding whole code ranges in the kernel.

`decodeN fuel n bs` decodes instructions from the start of `bs` until they tile exactly `n`
bytes, or fails. `decodeRanges pos rs bs` does this for every range `(lo, hi)` of `rs`, in
increasing order, reading `bs` (the bytes from offset `pos` on) once from start to end, so the
kernel walks the byte list once rather than once per range.

`decodeRanges_sound`: a successful decoding gives, for each range, an instruction list that
lies at `lo` (`seqAt`) and tiles `[lo, hi)` (`seqSize`). A proof device, untrusted.
-/

namespace M0Crypto.Thumb

/-- Decode instructions from the start of `bs` that tile exactly `n` bytes, in at most `fuel`
steps. -/
def decodeN : Nat → Nat → List (BitVec 8) → Option (List Instr)
  | _, 0, _ => some []
  | 0, _ + 1, _ => none
  | fuel + 1, n + 1, bs =>
    match instrScan bs with
    | none => none
    | some i =>
      if i.size ≤ n + 1 ∧ i.size ≤ bs.length then
        (decodeN fuel (n + 1 - i.size) (bs.drop i.size)).map (i :: ·)
      else none

theorem decodeN_sound : ∀ (fuel n : Nat) (bs : List (BitVec 8)) (is : List Instr),
    decodeN fuel n bs = some is → seqScan bs is = true ∧ seqSize is = n
  | _, 0, _, is, h => by
    simp only [decodeN, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | 0, _ + 1, _, _, h => by simp [decodeN] at h
  | fuel + 1, n + 1, bs, is, h => by
    simp only [decodeN] at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hs
        obtain ⟨js, hj, he⟩ := Option.map_eq_some_iff.mp h
        subst he
        obtain ⟨h1, h2⟩ := decodeN_sound fuel _ _ js hj
        refine ⟨?_, ?_⟩
        · simp only [seqScan, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          exact ⟨⟨hi, hs.2⟩, h1⟩
        · simp only [seqSize, List.map_cons, List.sum_cons] at h2 ⊢; omega
      · cases h

/-- Decode the ranges `rs` (increasing, none before `pos`) of the bytes `bs` from offset `pos`. -/
def decodeRanges : Nat → List (Nat × Nat) → List (BitVec 8) → Option (List (List Instr))
  | _, [], _ => some []
  | pos, (lo, hi) :: rs, bs =>
    if pos ≤ lo ∧ lo ≤ hi then
      let cs := bs.drop (lo - pos)
      match decodeN (hi - lo) (hi - lo) cs with
      | none => none
      | some is => (decodeRanges hi rs (cs.drop (hi - lo))).map (is :: ·)
    else none

/-- Range `k` of `rs` holds the instructions `iss[k]` at its start, tiling it exactly. -/
def RangesAt (bytes : List (BitVec 8)) : List (Nat × Nat) → List (List Instr) → Prop
  | [], [] => True
  | r :: rs, is :: iss => (seqAt bytes r.1 is = true ∧ seqSize is = r.2 - r.1) ∧ RangesAt bytes rs iss
  | _, _ => False

theorem decodeRanges_sound (bytes : List (BitVec 8)) : ∀ (rs : List (Nat × Nat)) (pos : Nat)
    (iss : List (List Instr)), decodeRanges pos rs (bytes.drop pos) = some iss → RangesAt bytes rs iss
  | [], _, iss, h => by simp only [decodeRanges, Option.some.injEq] at h; subst h; exact trivial
  | (lo, hi) :: rs, pos, iss, h => by
    simp only [decodeRanges] at h
    split at h
    · rename_i hr
      simp only [List.drop_drop] at h
      split at h
      · cases h
      · rename_i is his
        obtain ⟨jss, hj, he⟩ := Option.map_eq_some_iff.mp h
        subst he
        have e1 : pos + (lo - pos) = lo := by omega
        have e2 : lo + (hi - lo) = hi := by omega
        rw [e1] at his
        rw [e1, e2] at hj
        obtain ⟨h1, h2⟩ := decodeN_sound _ _ _ _ his
        exact ⟨⟨by rw [seqAt_eq_scan]; exact h1, h2⟩, decodeRanges_sound bytes rs hi jss hj⟩
    · cases h

/-- Every range of `rs` decodes and is tiled exactly by its instructions. -/
theorem decodeRanges_isSome {bytes : List (BitVec 8)} {rs : List (Nat × Nat)}
    (h : (decodeRanges 0 rs bytes).isSome = true) :
    ∃ iss, RangesAt bytes rs iss := by
  obtain ⟨iss, hs⟩ := Option.isSome_iff_exists.mp h
  exact ⟨iss, decodeRanges_sound bytes rs 0 iss (by simpa using hs)⟩

end M0Crypto.Thumb
