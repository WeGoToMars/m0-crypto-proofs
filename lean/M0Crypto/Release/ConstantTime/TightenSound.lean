import M0Crypto.Release.ConstantTime.TightenFacts
import M0Crypto.Release.ConstantTime.TightenLinks

/-! Soundness of abstract-state interval tightening. -/
namespace M0Crypto.Release.ConstantTime

/-- Tightening preserves the concrete relational state when recorded register
indices are well-formed. This is a property of the abstract operation, not an
additional precondition on cryptographic callers. -/
theorem AbsState.tighten_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow)
    (h : LowEq p bytes off s s₁ s₂) (hidx : s.indicesOk) :
    LowEq p bytes off (AbsState.tighten w s) s₁ s₂ := by
  let afterLinks := s.lnk.foldl (tightenLink w) s
  have hl : LowEq p bytes off afterLinks s₁ s₂ :=
    tightenLinks_sound w s.lnk h (by intro l hl; exact hl) hidx.2.2
  have hr : afterLinks.rel = s.rel := tightenLinks_rel w s s.lnk
  have hf := tightenFacts_sound afterLinks.rel hl (by intro f hf; exact hf)
    (by intro f hf; rw [hr] at hf; exact hidx.2.1 f hf)
  change LowEq p bytes off (afterLinks.rel.foldl tightenFact afterLinks) s₁ s₂
  exact hf

end M0Crypto.Release.ConstantTime
