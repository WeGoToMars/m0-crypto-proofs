import M0Crypto.Release.ConstantTime.StateSem
import M0Crypto.Release.ConstantTime.SemIndex

/-! Soundness of affine-link entailment in the concrete state semantics. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State Word)

/-- Every link entailed by an abstract state holds in both concrete states related by
`LowEq`. The requested link's indices must name represented registers. -/
theorem AbsState.lnkEntails_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : State} {l : Lnk}
    (hlow : LowEq p bytes off s s₁ s₂)
    (hl : linkIndexOk l) (hent : s.lnkEntails l = true) :
    LnkSem p l s₁ ∧ LnkSem p l s₂ := by
  rcases hl with ⟨hi, hj⟩
  rcases hlow with ⟨_, _, _, _, hregs, _, _, _, _, hlinks, _, _⟩
  by_cases hmem : l ∈ s.lnk
  · simp [AbsState.lnkEntails, hmem] at hent
    exact hlinks l hmem
  · have hcontains : s.lnk.contains l = false := by
      simpa using hmem
    simp only [AbsState.lnkEntails, hcontains, Bool.false_or] at hent
    cases hx : spExact (s.get l.i) with
    | none => simp [hx] at hent
    | some x =>
      cases hn : (s.get l.j).exact? with
      | none => simp [hx, hn] at hent
      | some n =>
        have heq : x = l.c + l.k * n := of_decide_eq_true (by simpa [hx, hn] using hent)
        have hiVal : s.get l.i = .sp x x := by
          cases hv : s.get l.i with
          | hi => simp [spExact, hv] at hx
          | lo => simp [spExact, hv] at hx
          | num a b => simp [spExact, hv] at hx
          | sp a b =>
            simp [spExact, hv] at hx
            rcases hx with ⟨hab, hax⟩
            subst a
            subst b
            rfl
          | ret r => simp [spExact, hv] at hx
          | lr0 => simp [spExact, hv] at hx
        have hjVal : s.get l.j = .num n n := by
          cases hv : s.get l.j with
          | hi => simp [AbsVal.exact?, hv] at hn
          | lo => simp [AbsVal.exact?, hv] at hn
          | num a b =>
            by_cases hab : a = b
            · simp [AbsVal.exact?, hv, hab] at hn
              subst b
              have han : a = n := hn
              subst a
              rfl
            · simp [AbsVal.exact?, hv, hab] at hn
          | sp a b => simp [AbsVal.exact?, hv] at hn
          | ret r => simp [AbsVal.exact?, hv] at hn
          | lr0 => simp [AbsVal.exact?, hv] at hn
        have hsi₁ := hregs l.i hi.1 hi.2
        have hsj₁ := hregs l.j hj.1 hj.2
        change AbsVal.Sem p (s.get l.i) (regAt s₁ l.i) (regAt s₂ l.i) at hsi₁
        change AbsVal.Sem p (s.get l.j) (regAt s₁ l.j) (regAt s₂ l.j) at hsj₁
        rw [hiVal] at hsi₁
        rw [hjVal] at hsj₁
        rcases hsi₁ with ⟨k, hklo, hkhi, hri₁, hri₂⟩
        have hk : k = x := by omega
        subst k
        rcases hsj₁ with ⟨hregsEq, hnlo, hnhi⟩
        have hnat₁ : (regAt s₁ l.j).toNat = n := by omega
        have hnat₂ : (regAt s₂ l.j).toNat = n := by rw [← hregsEq]; exact hnat₁
        have hbase₁ : regAt s₁ l.i = p.sp0 + BitVec.ofInt 32 (l.c + l.k * n) := by
          rw [← heq]
          exact hri₁
        have hbase₂ : regAt s₂ l.i = p.sp0 + BitVec.ofInt 32 (l.c + l.k * n) := by
          rw [← heq]
          rw [hri₂]
          exact hri₁
        constructor
        · change regAt s₁ l.i = p.sp0 + BitVec.ofInt 32 (l.c + l.k * (regAt s₁ l.j).toNat)
          rw [hnat₁]
          exact hbase₁
        · change regAt s₂ l.i = p.sp0 + BitVec.ofInt 32 (l.c + l.k * (regAt s₂ l.j).toNat)
          rw [hnat₂]
          exact hbase₂

end M0Crypto.Release.ConstantTime
