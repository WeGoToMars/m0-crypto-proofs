import M0Crypto.Release.ConstantTime.AddImmediate
import M0Crypto.Release.ConstantTime.TightenSound

/-! Preservation of affine links when a register is shifted by a constant. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)

/-- Moving the pointer end of an affine link adds the same displacement to its
constant. The equation is an equation of 32-bit words. -/
theorem lnkSem_shift_pointer {p : Params} {l : Lnk} {s u : State} (δ : Int)
    (hi : regAt u l.i = regAt s l.i + BitVec.ofInt 32 δ)
    (hj : regAt u l.j = regAt s l.j) (h : LnkSem p l s) :
    LnkSem p { l with c := l.c + δ } u := by
  simp only [LnkSem] at *
  rw [hi, hj, h, BitVec.ofInt_add, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofInt_add, BitVec.ofInt_add]
  bv_omega

/-- Moving the counter end subtracts its scaled displacement from the affine
constant. This holds even when the counter wraps as a 32-bit word. -/
theorem lnkSem_shift_counter {p : Params} {l : Lnk} {s u : State} (δ : Int)
    (hi : regAt u l.i = regAt s l.i)
    (hj : regAt u l.j = regAt s l.j + BitVec.ofInt 32 δ)
    (h : LnkSem p l s) : LnkSem p { l with c := l.c - l.k * δ } u := by
  simp only [LnkSem] at *
  rw [hi, h, hj]
  simp only [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_mul,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.mul_add]
  bv_omega

/-- Shifting the abstract links preserves the paired relation when the concrete
destination changes by the same modular displacement. -/
theorem shiftLinks_sound {p : Params} {bytes : List (BitVec 8)} {off off' : Nat}
    {pre post : AbsState} {r : Nat} {s₁ s₂ u₁ u₂ : State} (w : StackWindow) (δ : Int)
    (hpre : LowEq p bytes off pre s₁ s₂) (hpost : LowEq p bytes off' post u₁ u₂)
    (hpreidx : pre.indicesOk) (hpostidx : post.indicesOk)
    (hvalue₁ : regAt u₁ r = regAt s₁ r + BitVec.ofInt 32 δ)
    (hvalue₂ : regAt u₂ r = regAt s₂ r + BitVec.ofInt 32 δ)
    (hother₁ : ∀ j, regIndexOk j → j ≠ r → regAt u₁ j = regAt s₁ j)
    (hother₂ : ∀ j, regIndexOk j → j ≠ r → regAt u₂ j = regAt s₂ j) :
    LowEq p bytes off' (shiftLinks w pre r δ post) u₁ u₂ := by
  have hstrength : LowEq p bytes off' (AbsState.tighten w { post with lnk :=
      (post.lnk ++ pre.lnk.filterMap (fun (l : Lnk) =>
        if l.i == r && l.j == r then none
        else if l.i == r then some { l with c := l.c + δ }
        else if l.j == r then some { l with c := l.c - l.k * δ }
        else none)).eraseDups }) u₁ u₂ := by
    apply AbsState.tighten_sound
    · rcases hpost with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstk,
        hrel, hlnk, hsize, hcode₁, hcode₂⟩
      refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hstk, hrel, ?_, hsize, hcode₁, hcode₂⟩
      intro l hl
      simp only [List.mem_eraseDups, List.mem_append, List.mem_filterMap] at hl
      rcases hl with hl | ⟨old, hold, hmoved⟩
      · exact hlnk l hl
      · have hidx := hpreidx.2.2 old hold
        have hsem := hpre.links old hold
        split at hmoved
        · simp at hmoved
        · split at hmoved
          · rename_i hp
            simp only [beq_iff_eq] at hp
            simp only [Option.some.injEq] at hmoved
            subst l
            have hj : old.j ≠ r := by
              rename_i hboth
              simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hboth
              exact hboth hp
            exact ⟨lnkSem_shift_pointer δ (by simpa [hp] using hvalue₁)
                (hother₁ old.j hidx.2 hj) hsem.1,
              lnkSem_shift_pointer δ (by simpa [hp] using hvalue₂)
                (hother₂ old.j hidx.2 hj) hsem.2⟩
          · rename_i hp
            split at hmoved
            · rename_i hj
              simp only [beq_iff_eq] at hj
              simp only [beq_iff_eq] at hp
              simp only [Option.some.injEq] at hmoved
              subst l
              exact ⟨lnkSem_shift_counter δ (hother₁ old.i hidx.1 hp)
                  (by simpa [hj] using hvalue₁) hsem.1,
                lnkSem_shift_counter δ (hother₂ old.i hidx.1 hp)
                  (by simpa [hj] using hvalue₂) hsem.2⟩
            · simp at hmoved
    · refine ⟨hpostidx.1, hpostidx.2.1, ?_⟩
      intro l hl
      simp only [List.mem_eraseDups, List.mem_append, List.mem_filterMap] at hl
      rcases hl with hl | ⟨old, hold, hmoved⟩
      · exact hpostidx.2.2 l hl
      · have hi := hpreidx.2.2 old hold
        split at hmoved
        · simp at hmoved
        · split at hmoved
          · simp only [Option.some.injEq] at hmoved
            subst l
            exact hi
          · split at hmoved
            · simp only [Option.some.injEq] at hmoved
              subst l
              exact hi
            · simp at hmoved
  unfold shiftLinks
  dsimp only
  split <;> try simp only [Bool.not_true, Bool.not_false, ↓reduceIte]
  · exact hstrength
  · split <;> assumption
  · exact hpost

end M0Crypto.Release.ConstantTime
