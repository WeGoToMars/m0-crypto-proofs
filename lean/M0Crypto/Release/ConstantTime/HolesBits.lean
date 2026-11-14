import M0Crypto.Release.ConstantTime.Holes

/-! Bit facts about hole masks (`Holes.lean`). -/

namespace M0Crypto.Release.ConstantTime

/-- The bit of window offset `q`. -/
def holeBit (below : Nat) (q : Int) : Nat := (q + below).toNat

theorem rangeMask_testBit {below : Nat} {a b q : Int} (ha : -(below : Int) ≤ a)
    (hq : -(below : Int) ≤ q) :
    (rangeMask below a b).testBit (holeBit below q) = true ↔ a ≤ q ∧ q < b := by
  unfold rangeMask holeBit
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem maskOff_testBit (h m j : Nat) :
    (maskOff h m).testBit j = (h.testBit j && !m.testBit j) := by
  unfold maskOff
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases h.testBit j <;> cases m.testBit j <;> rfl

theorem sub_testBit {x y j : Nat} (h : (x &&& y == x) = true) (hx : x.testBit j = true) :
    y.testBit j = true := by
  have he : x &&& y = x := by simpa using h
  have := congrArg (fun n => n.testBit j) he
  simp only [Nat.testBit_and, hx, Bool.true_and] at this
  exact this

theorem meets_testBit {h r j : Nat} (hz : (h &&& r == 0) = true) (hr : r.testBit j = true) :
    h.testBit j = false := by
  have he : h &&& r = 0 := by simpa using hz
  have := congrArg (fun n => n.testBit j) he
  simp only [Nat.testBit_and, hr, Bool.and_true, Nat.zero_testBit] at this
  exact this

/-- Exact writes clear their bytes; nothing else does. -/
theorem foldl_holes_testBit (below : Nat) (q : Int) (hq : -(below : Int) ≤ q) :
    ∀ (accs : List SAcc) (h : Nat), (∀ a ∈ accs, -(below : Int) ≤ a.lo) →
      (accs.foldl (fun acc a => if !a.read && a.exact then maskOff acc (rangeMask below a.lo a.hi)
        else acc) h).testBit (holeBit below q) = false →
      h.testBit (holeBit below q) = false ∨
        ∃ a ∈ accs, a.read = false ∧ a.exact = true ∧ a.lo ≤ q ∧ q < a.hi
  | [], h, _, hf => Or.inl hf
  | a :: as, h, hlo, hf => by
    simp only [List.foldl_cons] at hf
    rcases foldl_holes_testBit below q hq as _ (fun x hx => hlo x (List.mem_cons_of_mem _ hx)) hf with
      h1 | ⟨x, hx, hx1⟩
    · by_cases hw : (!a.read && a.exact) = true
      · simp only [hw, ite_true, maskOff_testBit] at h1
        by_cases hr : (rangeMask below a.lo a.hi).testBit (holeBit below q) = true
        · have := (rangeMask_testBit (hlo a (List.mem_cons_self ..)) hq).1 hr
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
          exact Or.inr ⟨a, List.mem_cons_self .., hw.1, hw.2, this.1, this.2⟩
        · simp only [Bool.not_eq_true] at hr
          exact Or.inl (by simpa [hr] using h1)
      · simp only [Bool.not_eq_true] at hw
        exact Or.inl (by simpa [hw] using h1)
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hx1⟩

/-- A byte that is not a hole after a step was written exactly by the step, or was not a hole
before it and was not newly covered by a lower SP. -/
theorem holesAfter_testBit {below : Nat} {o o' q : Int} {accs : List SAcc} {h : Nat}
    (ho' : -(below : Int) ≤ o') (hq : o' ≤ q) (hlo : ∀ a ∈ accs, -(below : Int) ≤ a.lo)
    (hf : (holesAfter below o o' accs h).testBit (holeBit below q) = false) :
    (∃ a ∈ accs, a.read = false ∧ a.exact = true ∧ a.lo ≤ q ∧ q < a.hi) ∨
      (h.testBit (holeBit below q) = false ∧ o ≤ q) := by
  unfold holesAfter at hf
  rcases foldl_holes_testBit below q (by omega) accs _ hlo hf with h1 | h1
  · right
    by_cases hlt : o' < o
    · simp only [hlt, ite_true, Nat.testBit_or, Bool.or_eq_false_iff] at h1
      refine ⟨h1.1, ?_⟩
      by_cases hc : o ≤ q
      · exact hc
      · have := (rangeMask_testBit ho' (by omega) (b := o)).2 ⟨hq, by omega⟩
        rw [h1.2] at this
        cases this
    · simp only [hlt, ite_false] at h1
      exact ⟨h1, by omega⟩
  · exact Or.inl h1

end M0Crypto.Release.ConstantTime
