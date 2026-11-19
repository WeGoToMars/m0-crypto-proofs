import SafegcdTermination.LoopControl
import SafegcdTermination.PhaseOperands

namespace SafegcdTermination.LoopMemory

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchMachine (Image VectorsAt)
open SafegcdTermination.PhaseOperands
open SafegcdTermination.FoldRefine (vec)
open M0Crypto.Armv6M (State Mem read32 write32 write32_other read32_write32_same)
open M0Crypto.Thumb (ofNat_add_assoc)
open M0Crypto.Release.Frame (read32_congr)

theorem count_keep_byte (s : State) (cnt : Word) (o : Nat) (h : o < counterAt ∨ counterAt+4 ≤ o)
    (hb : o < 2^32) :
    write32 s.mem (addr s.sp counterAt) cnt (addr s.sp o) = s.mem (addr s.sp o) := by
  apply write32_other
  intro j hj
  simp only [addr, ofNat_add_assoc]
  have hM : counterAt+4 < 2^32 := by decide
  exact addr_sep s.sp hb (by omega) (by omega)

theorem count_preserves_slot (s : State) (cnt : Word) (o : Nat)
    (ho : o + vectorBytes ≤ counterAt) (i : Nat) (hi : i < 17) :
    vec (write32 s.mem (addr s.sp counterAt) cnt) (addr s.sp o) i = vec s.mem (addr s.sp o) i := by
  apply read32_congr
  intro j hj
  rw [slot_addr]
  simp only [addr, ofNat_add_assoc]
  have hB : counterAt < 2^32 := by decide
  change o + 68 ≤ counterAt at ho
  exact count_keep_byte s cnt (o+4*i+j) (.inl (by omega)) (by omega)

theorem count_preserves_word (s : State) (cnt : Word) (o : Nat)
    (ho : o + 4 ≤ counterAt ∨ counterAt+4 ≤ o) (hb : o+4 ≤ 2^32) :
    read32 (write32 s.mem (addr s.sp counterAt) cnt) (addr s.sp o) = stackWord s o := by
  apply read32_congr
  intro j hj
  simp only [addr, ofNat_add_assoc]
  exact count_keep_byte s cnt (o+j) (by omega) (by omega)

theorem count_write {u s : State} {cnt : Word} (hS : u.sp = s.sp)
    (hM : u.mem = write32 s.mem (addr s.sp counterAt) cnt) :
    stackWord u counterAt = cnt := by
  unfold stackWord stackAddr
  rw [hS,hM]
  exact read32_write32_same _ _ _

theorem count_frame {u s : State} {cnt : Word}
    (hM : u.mem = write32 s.mem (addr s.sp counterAt) cnt) :
    WritesOnly s.mem u.mem s.sp frameBytes := by
  intro a ha
  rw [hM]
  apply write32_other
  intro j hj
  simp only [addr, ofNat_add_assoc]
  have hB : counterAt+4 ≤ frameBytes := by decide
  exact ha _ (by omega)

theorem count_image {u s : State} {cnt : Word} {phase : Fin 3} {x : BatchState}
    (h : Image s (phases phase) x) (hS : u.sp = s.sp)
    (hM : u.mem = write32 s.mem (addr s.sp counterAt) cnt) :
    Image u (phases phase) x := by
  have hF : (phases phase).f + vectorBytes ≤ counterAt := by
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  have hD : (phases phase).d + vectorBytes ≤ counterAt := by
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hS, hM]
    exact Slot.read_eq h.f (count_preserves_slot _ _ _ hF)
  · rw [hS, hM]
    exact Slot.read_eq h.g (count_preserves_slot _ _ _ (by decide))
  · rw [hS, hM]
    exact Slot.read_eq h.d (count_preserves_slot _ _ _ hD)
  · rw [hS, hM]
    exact Slot.read_eq h.e (count_preserves_slot _ _ _ (by decide))
  · unfold stackWord stackAddr
    rw [hS, hM]
    exact (count_preserves_word _ _ _ (by decide) (by decide)).trans h.delta

end SafegcdTermination.LoopMemory
