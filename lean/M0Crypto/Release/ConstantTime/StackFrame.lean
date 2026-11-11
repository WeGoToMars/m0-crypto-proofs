import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.SemOffsets
import M0Crypto.Release.ConstantTime.SemStack
import M0Crypto.Armv6M.Memory

/-! Separation of tracked stack-word bytes inside a narrow window. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem read32 write32)

/-- Distinct aligned words in a narrow window do not share a byte address,
including when address arithmetic wraps around zero. -/
theorem stack_word_bytes_ne (w : StackWindow) (sp : Word) (o t : Int) (i j : Nat)
    (hwidth : w.below + w.above < 2 ^ 32)
    (ho : w.covers o (o + 4) = true) (ht : w.covers t (t + 4) = true)
    (hoa : o % 4 = 0) (hta : t % 4 = 0) (hne : o ≠ t)
    (hi : i < 4) (hj : j < 4) :
    sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i ≠
      sp + BitVec.ofInt 32 t + BitVec.ofNat 32 j := by
  intro heq
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at ho ht
  have hoff : BitVec.ofInt 32 (o + (i : Int)) = BitVec.ofInt 32 (t + (j : Int)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofInt_add, BitVec.ofInt_natCast]
    apply (BitVec.add_left_inj sp).mp
    simpa only [BitVec.add_comm sp, BitVec.add_assoc] using heq
  have heq' := ofInt32_injective_on_win w (o + (i : Int)) (t + (j : Int)) hwidth
    (by omega) (by omega) (by omega) (by omega) hoff
  omega

/-- Writing one aligned stack word leaves any other aligned word in the
window unchanged. -/
theorem read32_write32_stack_other (w : StackWindow) (sp : Word) (m : Mem) (v : Word)
    (o t : Int) (hwidth : w.below + w.above < 2 ^ 32)
    (ho : w.covers o (o + 4) = true) (ht : w.covers t (t + 4) = true)
    (hoa : o % 4 = 0) (hta : t % 4 = 0) (hne : o ≠ t) :
    read32 (write32 m (sp + BitVec.ofInt 32 t) v) (sp + BitVec.ofInt 32 o) =
      read32 m (sp + BitVec.ofInt 32 o) := by
  have hb : ∀ i, i < 4 →
      write32 m (sp + BitVec.ofInt 32 t) v
        (sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i) =
      m (sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i) := by
    intro i hi
    apply M0Crypto.Armv6M.write32_other
    intro j hj
    exact stack_word_bytes_ne w sp o t i j hwidth ho ht hoa hta hne hi hj
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read32]
  rw [h0, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, h1,
    show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, h2,
    show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, h3]

/-- A public tracked value must have an entry in the sparse stack. -/
theorem stkGet_public_mem (s : Stk) (o : Int) (h : (stkGet s o).pub = true) :
    ∃ v, (o, v) ∈ s := by
  induction s with
  | nil => simp [stkGet, AbsVal.pub] at h
  | cons a s ih =>
    rcases a with ⟨k, v⟩
    by_cases hok : o = k
    · subst k
      exact ⟨v, by simp⟩
    · have hb : (o == k) = false := by simp [hok]
      have hs : (stkGet s o).pub = true := by
        simpa [stkGet, List.lookup_cons, hb] using h
      obtain ⟨v, hv⟩ := ih hs
      exact ⟨v, by simp [hv]⟩

/-- Bounded tracked slots supply the frame premise for a concrete word store. -/
theorem stkSet_word_write_sem {p : Params} {s : Stk} {t : Int} {v : AbsVal}
    {m₁ m₂ : Mem} {x₁ x₂ : Word} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32)
    (hslots : s.slotsOk w) (ht : w.covers t (t + 4) = true) (hta : t % 4 = 0)
    (hs : StkSem p s m₁ m₂) (hv : AbsVal.Sem p v x₁ x₂) :
    StkSem p (stkSet s t v)
      (write32 m₁ (p.sp0 + BitVec.ofInt 32 t) x₁)
      (write32 m₂ (p.sp0 + BitVec.ofInt 32 t) x₂) := by
  apply stkSet_write_sem hs
  · simpa [M0Crypto.Armv6M.read32_write32_same] using hv
  · intro o hot hpub
    obtain ⟨value, hmem⟩ := stkGet_public_mem s o hpub
    have ⟨hoa, ho⟩ := hslots (o, value) hmem
    constructor <;> apply read32_write32_stack_other w p.sp0 _ _ o t hwidth ho ht hoa hta hot

/-- Replacing a tracked word preserves the bounded, aligned slot invariant. -/
theorem Stk.slotsOk_set {w : StackWindow} {s : Stk} {t : Int} {v : AbsVal}
    (hs : s.slotsOk w) (ha : t % 4 = 0) (ht : w.covers t (t + 4) = true) :
    (stkSet s t v).slotsOk w := by
  intro slot hmem
  simp only [stkSet] at hmem
  split at hmem
  · simp only [List.mem_cons, List.mem_filter] at hmem
    rcases hmem with heq | ⟨hold, _⟩
    · subst slot; exact ⟨ha, ht⟩
    · exact hs slot hold
  · simp only [List.mem_filter] at hmem
    exact hs slot hmem.1

/-- Abstract writes corresponding to consecutive machine-word stores. -/
def storeStackWords : Int → List AbsVal → Stk → Stk
  | _, [], stk => stk
  | off, v :: vs, stk => storeStackWords (off + 4) vs (stkSet stk off v)

/-- The analyzer's indexed fold writes the same words in the same order. -/
theorem storeStackWords_fold (g : Nat → AbsVal) (base : Int) (rs : List Nat)
    (k : Nat) (stk : Stk) :
    (rs.zip (List.range' k rs.length)).foldl
      (fun s (r, j) => stkSet s (base + (4 * j : Nat)) (g r)) stk =
    storeStackWords (base + (4 * k : Nat)) (rs.map g) stk := by
  induction rs generalizing k stk with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons,
      List.foldl_cons, List.map_cons, storeStackWords]
    rw [ih]
    have heq : base + (4 * (k + 1) : Nat) = base + (4 * k : Nat) + 4 := by omega
    rw [heq]

/-- Sequential word stores preserve the stack relation when every written
word is aligned, in the window, and related to its abstract value. -/
theorem storeStackWords_sound {p : Params} (w : StackWindow) (off : Int)
    (values : List (AbsVal × Word × Word)) (stk : Stk) (m₁ m₂ : Mem)
    (hwidth : w.below + w.above < 2 ^ 32)
    (hslots : stk.slotsOk w) (halign : off % 4 = 0)
    (hwin : ∀ k, k < values.length →
      w.covers (off + (4 * k : Nat)) (off + (4 * k : Nat) + 4) = true)
    (hvalues : ∀ v ∈ values, AbsVal.Sem p v.1 v.2.1 v.2.2)
    (hs : StkSem p stk m₁ m₂) :
    StkSem p (storeStackWords off (values.map (·.1)) stk)
      (M0Crypto.Thumb.storeWords m₁ (p.sp0 + BitVec.ofInt 32 off) (values.map (·.2.1)))
      (M0Crypto.Thumb.storeWords m₂ (p.sp0 + BitVec.ofInt 32 off) (values.map (·.2.2))) := by
  induction values generalizing off stk m₁ m₂ with
  | nil => exact hs
  | cons v vs ih =>
    have ht : w.covers off (off + 4) = true := by simpa using hwin 0 (by simp)
    have hv : AbsVal.Sem p v.1 v.2.1 v.2.2 := hvalues v (by simp)
    have hs' := stkSet_word_write_sem w hwidth hslots ht halign hs hv
    have hslots' := Stk.slotsOk_set (v := v.1) hslots halign ht
    have hwin' : ∀ k, k < vs.length →
        w.covers (off + 4 + (4 * k : Nat)) (off + 4 + (4 * k : Nat) + 4) = true := by
      intro k hk
      have h := hwin (k + 1) (by simp; omega)
      have heq : off + 4 + (4 * k : Nat) = off + (4 * (k + 1) : Nat) := by omega
      simpa only [heq] using h
    have hvalues' : ∀ x ∈ vs, AbsVal.Sem p x.1 x.2.1 x.2.2 := by
      intro x hx; exact hvalues x (by simp [hx])
    have ha : (off + 4) % 4 = 0 := by omega
    have hnext := ih (off + 4) _ _ _ hslots' ha hwin' hvalues' hs'
    have haddr : p.sp0 + BitVec.ofInt 32 (off + 4) =
        (p.sp0 + BitVec.ofInt 32 off) + 4#32 := by
      rw [BitVec.ofInt_add, BitVec.add_assoc]
      rfl
    simpa only [List.map_cons, storeStackWords, M0Crypto.Thumb.storeWords, haddr] using hnext

end M0Crypto.Release.ConstantTime
