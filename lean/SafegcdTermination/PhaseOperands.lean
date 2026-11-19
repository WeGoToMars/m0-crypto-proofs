import SafegcdTermination.PhaseData
import SafegcdTermination.RunRow

namespace SafegcdTermination.PhaseOperands

set_option maxHeartbeats 2200000

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchSlots
open SafegcdTermination.BatchMachine (Slot VectorsAt Range)
open SafegcdTermination.PhaseData (Progress rowResult)
open SafegcdTermination.FoldRefine (value vec)
open M0Crypto.Armv6M (State Mem)

def coefficients (m : Matrix) : Fin 4 → Row
  | 0 => m.f
  | 1 => m.g
  | 2 => m.f
  | _ => m.g

def operandX (x : BatchState) (i : Fin 4) : Int := if i.val < 2 then x.scalar.f else x.d
def operandY (x : BatchState) (i : Fin 4) : Int := if i.val < 2 then x.scalar.g else x.e

theorem row_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have he : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases he with h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (Fin.ext h)))

theorem Slot.read_eq {m m' : Mem} {sp : Word} {off : Nat} {x : Int} (h : Slot m sp off x)
    (he : ∀ i < 17, vec m' (addr sp off) i = vec m (addr sp off) i) : Slot m' sp off x := by
  refine ⟨?_, ⟨fun i hi => ?_, ?_⟩⟩
  · calc
      _ = value m (addr sp off) := weighted_congr 17 (fun i hi => by simp only [limb, he i hi])
      _ = _ := h.value
  · rw [he i (by omega)]
    exact h.formed.1 i hi
  · rw [he 16 (by decide)]
    exact h.formed.2

theorem original_slots {s : State} {x : BatchState} (phase : Fin 3) (h : VectorsAt s (phases phase) x) (i : Fin 4) :
    Slot s.mem s.sp (row phase i).x (operandX x i) ∧ Slot s.mem s.sp (row phase i).y (operandY x i) := by
  rcases row_cases i with rfl | rfl | rfl | rfl
  · exact ⟨h.f, h.g⟩
  · exact ⟨h.f, h.g⟩
  · exact ⟨h.d, h.e⟩
  · exact ⟨h.d, h.e⟩

theorem row_slots {s : State} {m : Mem} {phase : Fin 3} {x : BatchState} {i : Fin 4}
    (h : VectorsAt s (phases phase) x) (hP : Progress s.mem m s.sp phase i.val x.next) :
    Slot m s.sp (row phase i).x (operandX x i) ∧ Slot m s.sp (row phase i).y (operandY x i) := by
  have hS := original_slots phase h i
  obtain ⟨hx, hy⟩ := hP.before i (by omega)
  exact ⟨Slot.read_eq hS.1 hx, Slot.read_eq hS.2 hy⟩

theorem exact_mode (phase : Fin 3) (i : Fin 4) :
    (row phase i).modular = decide (2 ≤ i.val) := by
  have h : ∀ (p : Fin 3) (i : Fin 4), (row p i).modular = decide (2 ≤ i.val) := by
    decide +kernel
  exact h phase i

theorem row_math (x : BatchState) (h : Range x) (phase : Fin 3) (i : Fin 4) :
    let (_u, m) := accumulate x.scalar batchSteps
    let a := coefficients m i
    let r := row phase i
    let X := operandX x i
    let Y := operandY x i
    let N := rowResult x.next i
    a.norm ≤ batchScale ∧
      (r.modular = true → ResidueBounds X ∧ ResidueBounds Y) ∧
      (r.modular = false → a.apply X Y = batchScale * N ∧ -2 * foldRadix ≤ N ∧ N < 3 * foldRadix) ∧
      RunRow.rightValue r a X Y = N := by
  obtain ⟨ho, _, ⟨hf, hg⟩, hfEq, hgEq⟩ := one_matrix x.scalar h.odd
  have hr := h.next
  have hLo : -2 * foldRadix ≤ -p := by decide +kernel
  have hHi : p < 3 * foldRadix := by decide +kernel
  have hBF := magnitude_le_iff.mp hr.magnitudeF
  have hBG := magnitude_le_iff.mp hr.magnitudeG
  have hRf := CoreRows.exact_output _ _ _ _ hfEq
  have hRg := CoreRows.exact_output _ _ _ _ hgEq
  let n := accumulate x.scalar batchSteps
  have hmode := exact_mode phase i
  dsimp only
  change (coefficients n.2 i).norm ≤ batchScale ∧
    ((row phase i).modular = true → ResidueBounds (operandX x i) ∧ ResidueBounds (operandY x i)) ∧
    ((row phase i).modular = false → (coefficients n.2 i).apply (operandX x i) (operandY x i) =
      batchScale * rowResult x.next i ∧ -2 * foldRadix ≤ rowResult x.next i ∧ rowResult x.next i < 3 * foldRadix) ∧
    RunRow.rightValue (row phase i) (coefficients n.2 i) (operandX x i) (operandY x i) = rowResult x.next i
  unfold RunRow.rightValue
  rw [hmode]
  rcases row_cases i with rfl | rfl | rfl | rfl
  · exact ⟨hf, fun e => Bool.noConfusion e, fun _ => ⟨hfEq, Int.le_trans hLo hBF.1, Int.lt_of_le_of_lt hBF.2 hHi⟩, hRf⟩
  · exact ⟨hg, fun e => Bool.noConfusion e, fun _ => ⟨hgEq, Int.le_trans hLo hBG.1, Int.lt_of_le_of_lt hBG.2 hHi⟩, hRg⟩
  · exact ⟨hf, fun _ => ⟨h.d, h.e⟩, fun e => Bool.noConfusion e, rfl⟩
  · exact ⟨hg, fun _ => ⟨h.d, h.e⟩, fun e => Bool.noConfusion e, rfl⟩

end SafegcdTermination.PhaseOperands
