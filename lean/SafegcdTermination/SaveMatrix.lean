import SafegcdTermination.MatrixCall

namespace SafegcdTermination.SaveMatrix

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open M0Crypto.Armv6M (State Mem read32 write32 read32_write32_same write32_other)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr read32_storeWords_same)

set_option linter.unusedSimpArgs false

def words (s : State) : List Word := [s.regs 3, s.regs 4, s.regs 5, s.regs 6]

def result (s : State) : Mem :=
  storeWords (write32 s.mem (addr s.sp deltaAt) (s.regs 2)) (addr s.sp matrixAt) (words s)

theorem saved_reads (s : State) :
    let t := execAll saveMatrix s
    ∀ i (hi : i < 4), stackWord t (matrixAt+4*i) = (words s)[i]'(by simpa [words] using hi) := by
  obtain ⟨hm, hs⟩ := matrix_saved s
  dsimp only
  intro i hi
  have hw : i < (words s).length := by simpa [words] using hi
  have hW := read32_storeWords_same (write32 s.mem (addr s.sp deltaAt) (s.regs 2))
    (addr s.sp matrixAt) (words s) i hw (by simp [words])
  unfold stackWord stackAddr
  rw [hs, hm]
  simp only [addr, ofNat_add_assoc] at hW ⊢
  exact hW

theorem outside_regs (s : State) (x : Word)
    (hd : ∀ j < 4, x ≠ addr s.sp deltaAt + BitVec.ofNat 32 j)
    (hm : ∀ j < 16, x ≠ addr s.sp matrixAt + BitVec.ofNat 32 j) :
    result s x = s.mem x := by
  unfold result
  rw [storeWords_other]
  · exact write32_other _ _ _ _ hd
  · intro i j hi hj
    change i < 4 at hi
    rw [ofNat_add_assoc]
    exact hm _ (by omega)

theorem saved_delta (s : State) :
    stackWord (execAll saveMatrix s) deltaAt = s.regs 2 := by
  let m := write32 s.mem (addr s.sp deltaAt) (s.regs 2)
  obtain ⟨hm, hs⟩ := matrix_saved s
  have hMem : (execAll saveMatrix s).mem = result s := hm
  calc
    _ = read32 (result s) (addr s.sp deltaAt) := by unfold stackWord stackAddr; rw [hMem, hs]; rfl
    _ = read32 m (addr s.sp deltaAt) := by
      apply read32_congr
      intro j hj
      apply storeWords_other
      intro i k hi hk
      change i < 4 at hi
      have hN : deltaAt + 4 ≤ matrixAt := by decide
      have hHi : matrixAt + 16 < 2^32 := by decide
      simp only [addr, ofNat_add_assoc]
      exact addr_sep s.sp (by omega) (by omega) (by omega)
    _ = _ := read32_write32_same _ _ _

theorem keep_byte (s : State) (a : Nat) (ha : a < deltaAt ∨ matrixAt + 16 ≤ a)
    (h : a < 2^32) : result s (addr s.sp a) = s.mem (addr s.sp a) := by
  have hD : deltaAt + 4 ≤ matrixAt := by decide
  have hM : matrixAt + 16 < 2^32 := by decide
  apply outside_regs
  · intro j hj
    simp only [addr, ofNat_add_assoc]
    exact addr_sep s.sp h (by omega) (by omega)
  · intro j hj
    simp only [addr, ofNat_add_assoc]
    exact addr_sep s.sp h (by omega) (by omega)

theorem lower_slot (s : State) (a : Nat) (ha : a + vectorBytes ≤ deltaAt) (i : Nat) (hi : i < 17) :
    FoldRefine.vec (result s) (addr s.sp a) i = FoldRefine.vec s.mem (addr s.sp a) i := by
  apply read32_congr
  intro j hj
  rw [slot_addr]
  simp only [addr, ofNat_add_assoc]
  have hD : deltaAt < 2^32 := by decide
  change a + 68 ≤ deltaAt at ha
  exact keep_byte s (a + 4*i + j) (.inl (by omega)) (by omega)

theorem save_aligned (s : State) (h : FrameOk s.sp) : alignedAll saveMatrix s = true := by
  have hs := h.1
  unfold saveMatrix storeSp withSp imm
  simp only [alignedAll]
  row_simps
  simp only [wordAccesses, Access.aligned, List.all_eq_true, List.mem_map, beq_iff_eq]
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, State.sp, Nat.reducePow]
    change (s.sp.toNat + 344) % 4294967296 % 4 = 0
    omega
  · intro v hv
    obtain ⟨i, _, rfl⟩ := hv
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, State.sp, Nat.reducePow]
    change ((s.sp.toNat + 352) % 4294967296 + 4*i % 4294967296) % 4294967296 % 4 = 0
    omega

def PreservedWord (o : Nat) : Prop :=
  o = outputAt ∨ o = counterAt ∨ o = frameBytes - 4

theorem preserved_bound {o : Nat} (h : PreservedWord o) :
    5*vectorBytes ≤ o ∧ o+4 ≤ frameBytes := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem saved_preserves (s : State) (o : Nat) (h : PreservedWord o) :
    stackWord (execAll saveMatrix s) o = stackWord s o := by
  obtain ⟨hm, hs⟩ := matrix_saved s
  unfold stackWord stackAddr
  rw [hs, hm]
  change read32 (result s) (addr s.sp o) = read32 s.mem (addr s.sp o)
  apply read32_congr
  intro i hi
  apply outside_regs
  · intro j hj
    simp only [addr, ofNat_add_assoc]
    rcases h with rfl | rfl | rfl <;>
      apply addr_sep <;>
      simp only [outputAt, deltaAt, counterAt, vectorBytes, frameBytes] <;> omega
  · intro j hj
    simp only [addr, ofNat_add_assoc]
    rcases h with rfl | rfl | rfl <;>
      apply addr_sep <;>
      simp only [outputAt, deltaAt, counterAt, matrixAt, vectorBytes, frameBytes] <;> omega

end SafegcdTermination.SaveMatrix
