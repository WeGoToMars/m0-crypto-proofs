import M0Crypto.Release.ConstantTime.StateUpdate
import M0Crypto.Release.ConstantTime.SemTighten

/-! Preservation of relational state during affine-link narrowing. -/
namespace M0Crypto.Release.ConstantTime

def tightenLink (w : StackWindow) (s : AbsState) (l : Lnk) : AbsState :=
  match s.get l.i, ival (s.get l.j) with
  | .sp a b, some (nl, nh) =>
    let (x, y) := AbsState.lnkRange l.k l.c nl nh
    let a' := max a x
    let b' := min b y
    let bounded := decide (w.below + w.above < AbsVal.word) &&
      w.containsOffset a && w.containsOffset b && w.containsOffset x && w.containsOffset y
    if bounded && a' ≤ b' && (a < a' || b' < b) then
      { s with regs := regSet s.regs l.i (.sp a' b') }
    else s
  | _, _ => s

/-- One guarded affine-link refinement preserves the relational interpretation. -/
theorem tightenLink_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow) {l : Lnk}
    (h : LowEq p bytes off s s₁ s₂) (hmem : l ∈ s.lnk)
    (hidx : linkIndexOk l) : LowEq p bytes off (tightenLink w s l) s₁ s₂ := by
  rcases hidx with ⟨hi, hj⟩
  unfold tightenLink
  cases hv : s.get l.i with
  | hi | lo | num _ _ | ret _ | lr0 => simp [hv]; exact h
  | sp a b =>
    cases hjv : ival (s.get l.j) with
    | none => simp [hv, hjv]; exact h
    | some bounds =>
      rcases bounds with ⟨nl, nh⟩
      simp only [hv, hjv]
      split
      next hg =>
        apply h.withRegSet
        have ha := h.regs l.i hi.1 hi.2
        rw [hv] at ha
        have hb := h.regs l.j hj.1 hj.2
        have hbounds := interval_bounds hb hjv
        have hlink := (h.links l hmem).1
        simp only [LnkSem] at hlink
        simp only [Bool.and_eq_true, decide_eq_true_eq, StackWindow.containsOffset, AbsVal.word] at hg
        have hw := hg.1.1.1.1.1.1
        have halo := hg.1.1.1.1.1.2.1
        have hbhi := hg.1.1.1.1.2.2
        have hxlo := hg.1.1.1.2.1
        have hyhi := hg.1.1.2.2
        have hw' : w.below + w.above < 2 ^ 32 := of_decide_eq_true hw
        exact guarded_sp_intersection p w a b l.c l.k nl (regAt s₁ l.j).toNat nh
          (regAt s₁ l.i) (regAt s₂ l.i) hw' halo hbhi hxlo hyhi hbounds.1 hbounds.2.1 ha hlink
      next _ => exact h

theorem tightenLink_lnk (w : StackWindow) (s : AbsState) (l : Lnk) :
    (tightenLink w s l).lnk = s.lnk := by
  unfold tightenLink
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals dsimp only
  all_goals split <;> rfl

theorem tightenLink_rel (w : StackWindow) (s : AbsState) (l : Lnk) :
    (tightenLink w s l).rel = s.rel := by
  unfold tightenLink
  split <;> try rfl
  all_goals split <;> try rfl
  all_goals dsimp only
  all_goals split <;> rfl

theorem tightenLinks_rel (w : StackWindow) (s : AbsState) (ls : List Lnk) :
    (ls.foldl (tightenLink w) s).rel = s.rel := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih => simp only [List.foldl_cons, ih, tightenLink_rel]

theorem tightenLinks_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow) (ls : List Lnk)
    (h : LowEq p bytes off s s₁ s₂)
    (hmem : ∀ l ∈ ls, l ∈ s.lnk) (hidx : ∀ l ∈ ls, linkIndexOk l) :
    LowEq p bytes off (ls.foldl (tightenLink w) s) s₁ s₂ := by
  induction ls generalizing s with
  | nil => exact h
  | cons l ls ih =>
    simp only [List.foldl_cons]
    apply ih (tightenLink_sound w h (hmem l (by simp)) (hidx l (by simp)))
    · intro k hk
      rw [tightenLink_lnk]
      exact hmem k (by simp [hk])
    · intro k hk
      exact hidx k (by simp [hk])

end M0Crypto.Release.ConstantTime
