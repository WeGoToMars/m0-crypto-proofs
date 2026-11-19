import SafegcdTermination.BatchState
import SafegcdTermination.RowCalls

namespace SafegcdTermination.BatchSlots

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.RowCalls (Setup)
open M0Crypto.Armv6M (Mem State read32)
open M0Crypto.Release.Frame (read32_congr)
open M0Crypto.Thumb

def row (phase : Fin 3) (i : Fin 4) : RowCall :=
  (rowCalls (phases phase))[i.val]'(by simp [rowCalls, i.isLt])

theorem row_layout (phase : Fin 3) (i : Fin 4) (sp : Word) (hf : FrameOk sp) :
    Setup sp (row phase i) := by
  have h : ∀ (phase : Fin 3) (i : Fin 4),
      let c := row phase i
      InSlot c.dst ∧ InSlot c.x ∧ InSlot c.y ∧
        (c.dst = c.x ∨ Separate c.dst c.x) ∧ (c.dst = c.y ∨ Separate c.dst c.y) ∧ c.coeff ≤ 2 := by
    simp only [InSlot, Separate]
    decide +kernel
  obtain ⟨hd, hx, hy, hax, hay, hc⟩ := h phase i
  exact ⟨hf, hd, hx, hy, hax, hay, hc⟩

theorem bankF_slot (phase : Fin 3) : InSlot (phases phase).f := by
  unfold InSlot
  rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel

theorem bankG_slot : InSlot bankG := by unfold InSlot; decide +kernel

theorem bankD_slot (phase : Fin 3) : InSlot (phases phase).d := by
  unfold InSlot
  rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel

theorem bankE_slot : InSlot bankE := by unfold InSlot; decide +kernel

theorem free_slot (phase : Fin 3) : InSlot (phases phase).free := by
  unfold InSlot
  rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel

theorem row_dst_limit (phase : Fin 3) (i : Fin 4) :
    (row phase i).dst + vectorBytes ≤ 5 * vectorBytes := by
  have h : ∀ (phase : Fin 3) (i : Fin 4), (row phase i).dst + vectorBytes ≤ 5 * vectorBytes := by
    decide +kernel
  exact h phase i

theorem row_keep_word {m m' : Mem} {sp : Word} {a off : Nat}
    (hw : WritesOnly m m' (addr sp a) vectorBytes) (ha : a + vectorBytes ≤ off)
    (ho : off + 4 ≤ 2^32) :
    read32 m' (addr sp off) = read32 m (addr sp off) := by
  apply read32_congr
  intro j hj
  apply hw
  intro i hi
  simp only [addr, ofNat_add_assoc]
  exact addr_sep sp (by omega) (by omega) (by omega)

theorem row_keep_delta {m m' : Mem} {sp : Word} (phase : Fin 3) (i : Fin 4)
    (hw : WritesOnly m m' (addr sp (row phase i).dst) vectorBytes) :
    read32 m' (addr sp deltaAt) = read32 m (addr sp deltaAt) :=
  row_keep_word hw (Nat.le_trans (row_dst_limit phase i) (by decide)) (by decide)

theorem row_keep_matrix {m m' : Mem} {sp : Word} (phase : Fin 3) (i : Fin 4)
    (j : Nat) (hj : j < 4) (hw : WritesOnly m m' (addr sp (row phase i).dst) vectorBytes) :
    read32 m' (addr sp (matrixAt + 4*j)) = read32 m (addr sp (matrixAt + 4*j)) := by
  have hM : 5*vectorBytes ≤ matrixAt := by decide
  have hB : matrixAt + 16 ≤ 2^32 := by decide
  have hD := row_dst_limit phase i
  exact row_keep_word hw (by omega) (by omega)

end SafegcdTermination.BatchSlots
