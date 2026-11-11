import M0Crypto.Release.ConstantTime.StackFrame
import M0Crypto.Release.ConstantTime.SemStack
import M0Crypto.Release.ConstantTime.Transfer

/-! Frame properties for stack writes with an interval of possible addresses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem read32 write32)

private theorem forget_lookup (s : Stk) (o x y : Int)
    (h : o + 4 ≤ x ∨ y ≤ o) : (stkForget s x y).lookup o = s.lookup o := by
  induction s with
  | nil => simp [stkForget]
  | cons a s ih =>
    rcases a with ⟨k, v⟩
    by_cases hok : o = k
    · subst k; simp [stkForget, h]
    · have hbeq : (o == k) = false := by simp [hok]
      simp only [stkForget, List.filter_cons]
      split <;> simp [List.lookup_cons, hbeq] <;> simpa [stkForget] using ih

/-- Forgetting needs a frame condition only for public tracked slots. -/
theorem stkForget_public_frame {p : Params} {s : Stk} {x y : Int}
    {m₁ m₂ m₁' m₂' : Mem} (hs : StkSem p s m₁ m₂)
    (hf : ∀ o, (stkGet s o).pub = true → (o + 4 ≤ x ∨ y ≤ o) →
      read32 m₁' (p.sp0 + BitVec.ofInt 32 o) = read32 m₁ (p.sp0 + BitVec.ofInt 32 o) ∧
      read32 m₂' (p.sp0 + BitVec.ofInt 32 o) = read32 m₂ (p.sp0 + BitVec.ofInt 32 o)) :
    StkSem p (stkForget s x y) m₁' m₂' := by
  intro o
  by_cases hd : o + 4 ≤ x ∨ y ≤ o
  · have hg : stkGet (stkForget s x y) o = stkGet s o := by
      simp only [stkGet, forget_lookup s o x y hd]
    rw [hg]
    cases hp : (stkGet s o).pub with
    | false =>
      have hv : stkGet s o = .hi := by cases hv : stkGet s o <;> simp_all [AbsVal.pub]
      simp [hv, AbsVal.Sem]
    | true =>
      obtain ⟨h₁, h₂⟩ := hf o hp hd
      rw [h₁, h₂]
      exact hs o
  · have hn : (stkForget s x y).lookup o = none := by
      simp [stkForget]
      intro a b _ hk heq
      subst a
      exact hd (by simpa using hk)
    simp [stkGet, hn, AbsVal.Sem]

/-- Disjoint byte intervals within a narrow stack window have distinct addresses. -/
theorem stack_interval_bytes_ne (w : StackWindow) (sp : Word) (o t : Int) (i j : Nat)
    (hwidth : w.below + w.above < 2 ^ 32)
    (ho : w.covers o (o + 4) = true) (ht : w.covers t (t + 4) = true)
    (hd : o + 4 ≤ t ∨ t + 4 ≤ o) (hi : i < 4) (hj : j < 4) :
    sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i ≠
      sp + BitVec.ofInt 32 t + BitVec.ofNat 32 j := by
  intro heq
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at ho ht
  have hoff : BitVec.ofInt 32 (o + (i : Int)) = BitVec.ofInt 32 (t + (j : Int)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofInt_add, BitVec.ofInt_natCast]
    apply (BitVec.add_left_inj sp).mp
    simpa only [BitVec.add_comm sp, BitVec.add_assoc] using heq
  have := ofInt32_injective_on_win w (o + (i : Int)) (t + (j : Int)) hwidth
    (by omega) (by omega) (by omega) (by omega) hoff
  omega

/-- A word store at a disjoint stack interval leaves a tracked word unchanged. -/
theorem read32_write32_stack_interval_other (w : StackWindow) (sp : Word) (m : Mem) (v : Word)
    (o t : Int) (hwidth : w.below + w.above < 2 ^ 32)
    (ho : w.covers o (o + 4) = true) (ht : w.covers t (t + 4) = true)
    (hd : o + 4 ≤ t ∨ t + 4 ≤ o) :
    read32 (write32 m (sp + BitVec.ofInt 32 t) v) (sp + BitVec.ofInt 32 o) =
      read32 m (sp + BitVec.ofInt 32 o) := by
  have hb : ∀ i, i < 4 →
      write32 m (sp + BitVec.ofInt 32 t) v
        (sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i) =
      m (sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i) := by
    intro i hi
    apply M0Crypto.Armv6M.write32_other
    intro j hj
    exact stack_interval_bytes_ne w sp o t i j hwidth ho ht hd hi hj
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read32]
  rw [h0, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, h1,
    show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, h2,
    show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, h3]

/-- Forgetting the possible write interval soundly handles a word store at any
address in that interval, including modular address wraparound. -/
theorem stkForget_word_write_sem {p : Params} {s : Stk} {x y t : Int}
    {m₁ m₂ : Mem} {v₁ v₂ : Word} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : s.slotsOk w)
    (hwin : w.covers t (t + 4) = true) (hxt : x ≤ t) (hty : t ≤ y)
    (hs : StkSem p s m₁ m₂) :
    StkSem p (stkForget s x (y + 4))
      (write32 m₁ (p.sp0 + BitVec.ofInt 32 t) v₁)
      (write32 m₂ (p.sp0 + BitVec.ofInt 32 t) v₂) := by
  apply stkForget_public_frame hs
  intro o hpub hd
  obtain ⟨value, hmem⟩ := stkGet_public_mem s o hpub
  have ⟨_, ho⟩ := hslots (o, value) hmem
  have hdis : o + 4 ≤ t ∨ t + 4 ≤ o := by omega
  constructor <;> apply read32_write32_stack_interval_other w p.sp0 _ _ o t hwidth ho hwin hdis

/-- The analyzer's word-store update preserves the stack relation for any
concrete offset in its checked interval. -/
theorem stkStore_word_write_sem {p : Params} {st : AbsState} {x y t : Int}
    {m₁ m₂ : Mem} {v₁ v₂ : Word} {v : AbsVal} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : st.stk.slotsOk w)
    (hwin : w.covers t (t + 4) = true) (hxt : x ≤ t) (hty : t ≤ y)
    (hs : StkSem p st.stk m₁ m₂) (hv : AbsVal.Sem p v v₁ v₂) :
    StkSem p (stkStore st x y 4 v)
      (write32 m₁ (p.sp0 + BitVec.ofInt 32 t) v₁)
      (write32 m₂ (p.sp0 + BitVec.ofInt 32 t) v₂) := by
  unfold stkStore
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hxy : x = y := hc.1.1
    have ha : x % 4 = 0 := hc.2
    have htx : t = x := by omega
    subst t
    exact stkSet_word_write_sem w hwidth hslots hwin ha hs hv
  · exact stkForget_word_write_sem w hwidth hslots hwin hxt hty hs

/-- Disjoint stack intervals have distinct byte addresses for any access width. -/
theorem stack_bytes_disjoint (w : StackWindow) (sp : Word) (o t : Int) (width i j : Nat)
    (hwidth : w.below + w.above < 2 ^ 32)
    (ho : w.covers o (o + 4) = true) (ht : w.covers t (t + width) = true)
    (hd : o + 4 ≤ t ∨ t + width ≤ o) (hi : i < 4) (hj : j < width) :
    sp + BitVec.ofInt 32 o + BitVec.ofNat 32 i ≠
      sp + BitVec.ofInt 32 t + BitVec.ofNat 32 j := by
  intro heq
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at ho ht
  have hoff : BitVec.ofInt 32 (o + (i : Int)) = BitVec.ofInt 32 (t + (j : Int)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofInt_add, BitVec.ofInt_natCast]
    apply (BitVec.add_left_inj sp).mp
    simpa only [BitVec.add_comm sp, BitVec.add_assoc] using heq
  have := ofInt32_injective_on_win w (o + (i : Int)) (t + (j : Int)) hwidth
    (by omega) (by omega) (by omega) (by omega) hoff
  omega

/-- A memory update confined to the concrete write bytes preserves the stack
relation after forgetting the full possible write interval. -/
theorem stkForget_write_frame {p : Params} {s : Stk} {x y t : Int} {width : Nat}
    {m₁ m₂ m₁' m₂' : Mem} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : s.slotsOk w)
    (hwin : w.covers t (t + width) = true) (hxt : x ≤ t) (hty : t ≤ y)
    (hs : StkSem p s m₁ m₂)
    (hf : ∀ a, (∀ j, j < width → a ≠ p.sp0 + BitVec.ofInt 32 t + BitVec.ofNat 32 j) →
      m₁' a = m₁ a ∧ m₂' a = m₂ a) :
    StkSem p (stkForget s x (y + width)) m₁' m₂' := by
  apply stkForget_public_frame hs
  intro o hpub hd
  obtain ⟨value, hmem⟩ := stkGet_public_mem s o hpub
  have ⟨_, ho⟩ := hslots (o, value) hmem
  have hdis : o + 4 ≤ t ∨ t + width ≤ o := by omega
  have hb (i : Nat) (hi : i < 4) :
      m₁' (p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i) =
        m₁ (p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i) ∧
      m₂' (p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i) =
        m₂ (p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i) := by
    apply hf
    intro j hj
    exact stack_bytes_disjoint w p.sp0 o t width i j hwidth ho hwin hdis hi hj
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [BitVec.add_zero] at h0
  constructor <;> simp only [read32] <;>
    simp only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Byte stores forget every tracked word that may overlap the write. -/
theorem stkStore_byte_write_sem {p : Params} {st : AbsState} {x y t : Int}
    {m₁ m₂ : Mem} {v₁ v₂ : Word} {v : AbsVal} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : st.stk.slotsOk w)
    (hwin : w.covers t (t + 1) = true) (hxt : x ≤ t) (hty : t ≤ y)
    (hs : StkSem p st.stk m₁ m₂) :
    StkSem p (stkStore st x y 1 v)
      (M0Crypto.Thumb.write8 m₁ (p.sp0 + BitVec.ofInt 32 t) v₁)
      (M0Crypto.Thumb.write8 m₂ (p.sp0 + BitVec.ofInt 32 t) v₂) := by
  simp only [stkStore, show (1 == 4) = false from rfl, Bool.and_false, Bool.false_and]
  apply stkForget_write_frame (width := 1) w hwidth hslots hwin hxt hty hs
  intro a ha
  have h0 := ha 0 (by omega)
  simp only [BitVec.add_zero] at h0
  constructor <;> apply M0Crypto.Thumb.write8_other <;> exact h0

/-- Halfword stores forget every tracked word that may overlap the write. -/
theorem stkStore_half_write_sem {p : Params} {st : AbsState} {x y t : Int}
    {m₁ m₂ : Mem} {v₁ v₂ : Word} {v : AbsVal} (w : StackWindow)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : st.stk.slotsOk w)
    (hwin : w.covers t (t + 2) = true) (hxt : x ≤ t) (hty : t ≤ y)
    (hs : StkSem p st.stk m₁ m₂) :
    StkSem p (stkStore st x y 2 v)
      (M0Crypto.Thumb.write16 m₁ (p.sp0 + BitVec.ofInt 32 t) v₁)
      (M0Crypto.Thumb.write16 m₂ (p.sp0 + BitVec.ofInt 32 t) v₂) := by
  simp only [stkStore, show (2 == 4) = false from rfl, Bool.and_false, Bool.false_and]
  apply stkForget_write_frame (width := 2) w hwidth hslots hwin hxt hty hs
  intro a ha
  have h0 := ha 0 (by omega)
  have h1 := ha 1 (by omega)
  simp only [BitVec.add_zero] at h0
  constructor <;> apply M0Crypto.Thumb.write16_other <;> assumption

end M0Crypto.Release.ConstantTime
