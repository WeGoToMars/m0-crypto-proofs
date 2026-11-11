import M0Crypto.Release.ConstantTime.SemValue

/-! Soundness of modular arithmetic on relational abstract values. -/
namespace M0Crypto.Release.ConstantTime.AbsVal
open M0Crypto.Armv6M (Word)

/-- Adding an immediate word preserves the relational interpretation. -/
theorem addK_sound {p : Params} {a : AbsVal} {x y : Word} (k : Nat)
    (h : Sem p a x y) :
    Sem p (a.addK k) (x + BitVec.ofNat 32 k) (y + BitVec.ofNat 32 k) := by
  cases a with
  | hi => simp [addK, Sem]
  | lo => simp_all [addK, Sem]
  | ret r => simp_all [addK, Sem]
  | lr0 => simp_all [addK, Sem]
  | num lo hi =>
    rcases h with ⟨hxy, hlo, hhi⟩
    subst y
    by_cases hb : hi + k < word
    · have hk : k < word := by omega
      have hx : x.toNat + k < 2 ^ 32 := by simp [word] at *; omega
      have hkn : (BitVec.ofNat 32 k).toNat = k := by
        exact Nat.mod_eq_of_lt hk
      have hadd : (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
        rw [BitVec.toNat_add, hkn, Nat.mod_eq_of_lt hx]
      simp only [addK, hb, ↓reduceIte, Sem]
      exact ⟨trivial, by rw [hadd]; omega, by rw [hadd]; omega⟩
    · simp [addK, hb, Sem]
  | sp lo hi =>
    rcases h with ⟨n, hnlo, hnhi, hx, hy⟩
    subst y
    refine ⟨n + (k : Int), by omega, by omega, ?_, rfl⟩
    rw [hx, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]

/-- Subtracting an immediate word preserves the relational interpretation. -/
theorem subK_sound {p : Params} {a : AbsVal} {x y : Word} (k : Nat)
    (h : Sem p a x y) :
    Sem p (a.subK k) (x - BitVec.ofNat 32 k) (y - BitVec.ofNat 32 k) := by
  cases a with
  | hi => simp [subK, Sem]
  | lo => simp_all [subK, Sem]
  | ret r => simp_all [subK, Sem]
  | lr0 => simp_all [subK, Sem]
  | num lo hi =>
    rcases h with ⟨hxy, hlo, hhi⟩
    subst y
    by_cases hb : k ≤ lo
    · have hxlt : x.toNat < 2 ^ 32 := x.isLt
      have hk : k < 2 ^ 32 := by omega
      have hkn : (BitVec.ofNat 32 k).toNat = k := Nat.mod_eq_of_lt hk
      have hle : BitVec.ofNat 32 k ≤ x := by
        rw [BitVec.le_def, hkn]; omega
      have hsub : (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
        rw [BitVec.toNat_sub_of_le hle, hkn]
      simp only [subK, hb, ↓reduceIte, Sem]
      exact ⟨trivial, by rw [hsub]; omega, by rw [hsub]; omega⟩
    · simp [subK, hb, Sem]
  | sp lo hi =>
    rcases h with ⟨n, hnlo, hnhi, hx, hy⟩
    subst y
    refine ⟨n - (k : Int), by omega, by omega, ?_, rfl⟩
    rw [hx, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- Adding two words preserves the relational interpretation. -/
theorem add_sound {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : Word}
    (ha : Sem p a x₁ x₂) (hb : Sem p b y₁ y₂) :
    Sem p (a.add b) (x₁ + y₁) (x₂ + y₂) := by
  have ea : a.pub = true → x₁ = x₂ := sem_public ha
  have eb : b.pub = true → y₁ = y₂ := sem_public hb
  cases a <;> cases b <;> simp_all [Sem, add, pub]
  case num.num al ah bl bh =>
    obtain ⟨hxe, hxl, hxh⟩ := ha
    obtain ⟨hye, hyl, hyh⟩ := hb
    subst x₁
    subst y₁
    by_cases hbound : ah + bh < word
    · have hsum : x₂.toNat + y₂.toNat < 2 ^ 32 := by
        simp [word] at hbound; omega
      have heq := BitVec.toNat_add_of_lt hsum
      simp only [hbound, ↓reduceIte, Sem]
      rw [heq]
      exact ⟨trivial, Nat.add_le_add hxl hyl, Nat.add_le_add hxh hyh⟩
    · simp [hbound, Sem]
  case num.sp al ah bl bh =>
    obtain ⟨hxe, hxl, hxh⟩ := ha
    subst x₁
    obtain ⟨n, hnlo, hnhi, hy⟩ := hb
    refine ⟨n + (x₂.toNat : Int), by omega, by omega, ?_⟩
    rw [hy, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    simp only [BitVec.setWidth_eq]
    rw [← BitVec.add_assoc, BitVec.add_comm x₂ p.sp0, BitVec.add_assoc,
      BitVec.add_comm x₂ (BitVec.ofInt 32 n)]
  case sp.num al ah bl bh =>
    obtain ⟨hye, hyl, hyh⟩ := hb
    subst y₁
    obtain ⟨n, hnlo, hnhi, hx⟩ := ha
    refine ⟨n + (y₂.toNat : Int), by omega, by omega, ?_⟩
    rw [hx, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    simp [BitVec.add_assoc]

/-- Subtracting two words preserves the relational interpretation. -/
theorem sub_sound {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : Word}
    (ha : Sem p a x₁ x₂) (hb : Sem p b y₁ y₂) :
    Sem p (a.sub b) (x₁ - y₁) (x₂ - y₂) := by
  have ea : a.pub = true → x₁ = x₂ := sem_public ha
  have eb : b.pub = true → y₁ = y₂ := sem_public hb
  cases a <;> cases b <;> simp_all [Sem, sub, pub]
  case num.num al ah bl bh =>
    obtain ⟨hxe, hxl, hxh⟩ := ha
    obtain ⟨hye, hyl, hyh⟩ := hb
    subst x₁
    subst y₁
    by_cases hbound : bh ≤ al
    · have hle : y₂ ≤ x₂ := by rw [BitVec.le_def]; omega
      have heq := BitVec.toNat_sub_of_le hle
      simp only [hbound, ↓reduceIte, Sem]
      rw [heq]
      exact ⟨trivial, by omega, by omega⟩
    · simp [hbound, Sem]
  case sp.num al ah bl bh =>
    obtain ⟨hye, hyl, hyh⟩ := hb
    subst y₁
    obtain ⟨n, hnlo, hnhi, hx⟩ := ha
    refine ⟨n - (y₂.toNat : Int), by omega, by omega, ?_⟩
    rw [hx, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    simp [BitVec.setWidth_eq]

/-- Applying the same word function to public operands yields a public result. -/
theorem ofPub_binary {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : Word}
    (f : Word → Word → Word) (ha : Sem p a x₁ x₂) (hb : Sem p b y₁ y₂) :
    Sem p (ofPub (a.pub && b.pub)) (f x₁ y₁) (f x₂ y₂) := by
  cases hpa : a.pub <;> cases hpb : b.pub <;> simp [hpa, hpb, ofPub, Sem]
  have hx := sem_public ha hpa
  have hy := sem_public hb hpb
  rw [hx, hy]

end M0Crypto.Release.ConstantTime.AbsVal
