import SafegcdTermination.BatchSlots

namespace SafegcdTermination.PhaseData

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchSlots
open SafegcdTermination.BatchMachine (Slot Image)
open SafegcdTermination.FoldRefine (vec value)
open M0Crypto.Armv6M (Mem read32)
open M0Crypto.Thumb (ofNat_add_assoc)
open M0Crypto.Release.Frame (read32_congr)

def rowResult (x : BatchState) : Fin 4 → Int
  | 0 => x.scalar.f
  | 1 => x.scalar.g
  | 2 => x.d
  | _ => x.e

theorem before_disjoint (phase : Fin 3) (i j : Fin 4) (h : i.val < j.val) :
    Separate (row phase i).dst (row phase j).x ∧ Separate (row phase i).dst (row phase j).y := by
  have check : ∀ (phase : Fin 3) (i j : Fin 4), i.val < j.val →
      Separate (row phase i).dst (row phase j).x ∧ Separate (row phase i).dst (row phase j).y := by
    unfold Separate
    decide +kernel
  exact check phase i j h

theorem output_disjoint (phase : Fin 3) (i j : Fin 4) (h : i.val ≠ j.val) :
    Separate (row phase i).dst (row phase j).dst := by
  have check : ∀ (phase : Fin 3) (i j : Fin 4), i.val ≠ j.val →
      Separate (row phase i).dst (row phase j).dst := by
    unfold Separate
    decide +kernel
  exact check phase i j h

structure Progress (m₀ m : Mem) (sp : Word) (phase : Fin 3) (n : Nat) (result : BatchState) : Prop where
  before : ∀ i : Fin 4, n ≤ i.val →
    (∀ k < 17, vec m (addr sp (row phase i).x) k = vec m₀ (addr sp (row phase i).x) k) ∧
    (∀ k < 17, vec m (addr sp (row phase i).y) k = vec m₀ (addr sp (row phase i).y) k)
  after : ∀ i : Fin 4, i.val < n → Slot m sp (row phase i).dst (rowResult result i)
  outside : WritesOnly m₀ m sp (5*vectorBytes)

theorem progress_start (m : Mem) (sp : Word) (phase : Fin 3) (out : BatchState) :
    Progress m m sp phase 0 out :=
  ⟨fun _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ _ => rfl⟩

theorem progress_next {m₀ m m' : Mem} {sp : Word} {phase : Fin 3} {i : Fin 4} {out : BatchState}
    (hf : FrameOk sp) (h : Progress m₀ m sp phase i.val out)
    (hs : Slot m' sp (row phase i).dst (rowResult out i))
    (hw : WritesOnly m m' (addr sp (row phase i).dst) vectorBytes) :
    Progress m₀ m' sp phase (i.val+1) out := by
  have hi := row_layout phase i sp hf
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hb := before_disjoint phase i j (by omega)
    have hJ := row_layout phase j sp hf
    obtain ⟨hx, hy⟩ := h.before j (by omega)
    exact ⟨fun k hk => (read_vec_disjoint hf hi.dst hJ.x hb.1 hw k hk).trans (hx k hk),
      fun k hk => (read_vec_disjoint hf hi.dst hJ.y hb.2 hw k hk).trans (hy k hk)⟩
  · intro j hj
    by_cases he : j = i
    · simpa only [he] using hs
    · have hn : i.val ≠ j.val := fun heq => he (Fin.ext heq.symm)
      have hlt : j.val < i.val := by have := j.isLt; omega
      exact (h.after j hlt).move hf hi.dst (row_layout phase j sp hf).dst (output_disjoint phase i j hn) hw
  · intro a ha
    apply Eq.trans _ (h.outside a ha)
    apply hw
    intro k hk
    simp only [addr, ofNat_add_assoc]
    have hB := row_dst_limit phase i
    exact ha _ (by omega)

theorem Progress.registers {m₀ m : Mem} {sp : Word} {phase : Fin 3} {n : Nat} {out : BatchState}
    (h : Progress m₀ m sp phase n out) (off : Nat) (ho : 5*vectorBytes ≤ off) (hb : off+4 ≤ 2^32) :
    read32 m (addr sp off) = read32 m₀ (addr sp off) := by
  apply read32_congr
  intro j hj
  apply h.outside
  intro i hi
  simp only [addr, ofNat_add_assoc]
  have hN : 5*vectorBytes < 2^32 := by decide
  exact addr_sep sp (by omega) (by omega) (by omega)

theorem Progress.read_outside {m₀ m : Mem} {sp a : Word} {phase : Fin 3} {n : Nat} {out : BatchState}
    (h : Progress m₀ m sp phase n out)
    (hd : ∀ j < 4, ∀ i < 5*vectorBytes, a + BitVec.ofNat 32 j ≠ sp + BitVec.ofNat 32 i) :
    read32 m a = read32 m₀ a :=
  read32_congr fun j hj => h.outside _ (hd j hj)

end SafegcdTermination.PhaseData
