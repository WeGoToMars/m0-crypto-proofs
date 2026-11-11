import M0Crypto.Release.ConstantTime.SemStack

/-! Soundness of the sparse-stack abstract ordering. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Mem read32)

/-- If `stkLe a b` holds, every slot interpreted by `b` is covered by the
corresponding interpretation of `a`. The induction follows `List.lookup`'s
first-match behavior: a matching head supplies the bound; a nonmatching head
is skipped. Thus duplicate offsets are handled by the first occurrence, while
`stkLe`'s checks for later duplicates are harmless additional obligations. -/
theorem stkLe_sem {p : Params} {a b : Stk} {m₁ m₂ : Mem}
    (hle : stkLe a b = true)
    (hs : StkSem p a m₁ m₂) :
    StkSem p b m₁ m₂ := by
  change ∀ o : Int, AbsVal.Sem p (stkGet b o)
    (read32 m₁ (p.sp0 + BitVec.ofInt 32 o))
    (read32 m₂ (p.sp0 + BitVec.ofInt 32 o))
  intro o
  induction b with
  | nil =>
      simp [stkGet, AbsVal.Sem]
  | cons q qs ih =>
      rcases q with ⟨k, v⟩
      simp only [stkLe, List.all_cons, Bool.and_eq_true] at hle
      by_cases hko : k = o
      · subst o
        have hlookup : stkGet ((k, v) :: qs) k = v := by
          simp [stkGet]
        rw [hlookup]
        apply AbsVal.le_sem hle.1
        exact hs k
      · have htail := ih hle.2
        have hneq : (o == k) = false := by simp [Ne.symm hko]
        simpa [stkGet, List.lookup_cons, hneq] using htail

end M0Crypto.Release.ConstantTime
