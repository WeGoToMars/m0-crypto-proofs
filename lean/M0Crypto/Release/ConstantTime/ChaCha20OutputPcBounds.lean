import M0Crypto.Release.ConstantTime.ChaCha20OutputAccess

/-! Relationships between output-store PCs and surrounding code intervals. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout

/-- Both families of caller-buffer store instructions lie in the output region. -/
theorem output_store_offset_bounds :
    (List.range 16).all (fun i => decide
      (achOff ≤ achOff + achSize * i + seqSize (ach i).dropLast ∧
       achOff + achSize * i + seqSize (ach i).dropLast < n1Off)) = true ∧
    achOff ≤ blOff + seqSize (bl.take 3) ∧ blOff + seqSize (bl.take 3) < n1Off := by
  decide +kernel

/-- Natural offsets in the address space have unique 32-bit encodings. -/
theorem offset32_eq {a b : Nat} (ha : a < 2^32) (hb : b < 2^32)
    (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- A PC before the output region cannot be a caller-buffer output store. -/
theorem before_output_not_store (base pc : Word)
    (hbefore : PCBefore base achOff pc) : ¬ OutputStorePC base pc := by
  obtain ⟨off, hoff, hp⟩ := hbefore
  have ha : off < 2^32 := by
    have hlimit : achOff < 2^32 := by decide +kernel
    omega
  have hn : n1Off < 2^32 := by decide +kernel
  rintro (⟨i, hi, hs⟩ | hs)
  · have hb := List.all_eq_true.mp output_store_offset_bounds.1 i (List.mem_range.mpr hi)
    simp only [decide_eq_true_eq] at hb
    have eq : off = achOff + achSize * i + seqSize (ach i).dropLast := by
      apply offset32_eq ha (by omega)
      apply (BitVec.add_right_inj base).mp
      exact hp.symm.trans hs
    omega
  · have hb := output_store_offset_bounds.2
    have eq : off = blOff + seqSize (bl.take 3) := by
      apply offset32_eq ha (by omega)
      apply (BitVec.add_right_inj base).mp
      exact hp.symm.trans hs
    omega

/-- A PC in the post-output code interval cannot be an output store. -/
theorem after_output_not_store (base pc : Word)
    (hafter : PCBetween base n1Off Artifacts.Release.size pc) : ¬ OutputStorePC base pc := by
  obtain ⟨off, hlo, hhi, hp⟩ := hafter
  have ha : off < 2^32 := by
    have : Artifacts.Release.size < 2^32 := by decide +kernel
    omega
  have hn : n1Off < 2^32 := by decide +kernel
  rintro (⟨i, hi, hs⟩ | hs)
  · have hb := List.all_eq_true.mp output_store_offset_bounds.1 i (List.mem_range.mpr hi)
    simp only [decide_eq_true_eq] at hb
    have eq : off = achOff + achSize * i + seqSize (ach i).dropLast := by
      apply offset32_eq ha (by omega)
      apply (BitVec.add_right_inj base).mp
      exact hp.symm.trans hs
    omega
  · have hb := output_store_offset_bounds.2
    have eq : off = blOff + seqSize (bl.take 3) := by
      apply offset32_eq ha (by omega)
      apply (BitVec.add_right_inj base).mp
      exact hp.symm.trans hs
    omega

end M0Crypto.Release.ConstantTime
