import M0Crypto.Release.ConstantTime.StateSem
import M0Crypto.Release.ConstantTime.Transfer
import M0Crypto.Release.TraceSpec
import M0Crypto.Release.RunStates

/-! Stack-window facts implied by successful abstract instruction transfers. -/
namespace M0Crypto.Release.ConstantTime

/-- A successful transfer checks the current stack offset against the entry window. -/
theorem xfer_sp_bounds {env : Env} {off : Nat} {ctx : Option Nat}
    {i : M0Crypto.Thumb.Instr} {st : AbsState} {out : Out}
    (h : xfer env off ctx i st = .ok out) :
    -(env.win.below : Int) ≤ st.spOff ∧ st.spOff ≤ 0 ∧
      st.spOff ≤ (env.win.above : Int) := by
  unfold xfer at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, StackWindow.covers, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.2, hc.1.2⟩
  · contradiction

/-- The concrete SP in either related run has the checked offset. -/
theorem xfer_related_sp {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {i : M0Crypto.Thumb.Instr} {st : AbsState} {out : Out}
    {s₁ s₂ : M0Crypto.Armv6M.State}
    (h : LowEq p bytes off st s₁ s₂) (hx : xfer env off ctx i st = .ok out) :
    ∃ k : Int, -(env.win.below : Int) ≤ k ∧ k ≤ 0 ∧
      s₁.regs 13 = p.sp0 + BitVec.ofInt 32 k ∧
      s₂.regs 13 = p.sp0 + BitVec.ofInt 32 k := by
  have hb := xfer_sp_bounds hx
  exact ⟨st.spOff, hb.1, hb.2.1, h.sp, h.sp_eq.trans h.sp⟩

/-- A successfully checked transfer places the related concrete stack pointers
in the specification's stack window. -/
theorem xfer_stack_window {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {i : M0Crypto.Thumb.Instr} {st : AbsState} {out : Out}
    {s₁ s₂ : M0Crypto.Armv6M.State}
    (h : LowEq p bytes off st s₁ s₂) (hx : xfer env off ctx i st = .ok out) :
    M0Crypto.Release.TraceSpec.InStackWindow p.sp0 env.win.below (s₁.regs 13) ∧
    M0Crypto.Release.TraceSpec.InStackWindow p.sp0 env.win.below (s₂.regs 13) := by
  obtain ⟨k, hklo, hkhi, hs₁, hs₂⟩ := xfer_related_sp h hx
  let n := (-k).toNat
  have hn : (n : Int) = -k := Int.toNat_of_nonneg (by omega)
  have hnle : n ≤ env.win.below := by omega
  have heq : BitVec.ofInt 32 k = -BitVec.ofNat 32 n := by
    have hk : k = -(n : Int) := by omega
    rw [hk, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  constructor
  · refine ⟨n, hnle, ?_⟩
    rw [hs₁, heq, BitVec.sub_eq_add_neg]
  · refine ⟨n, hnle, ?_⟩
    rw [hs₂, heq, BitVec.sub_eq_add_neg]

end M0Crypto.Release.ConstantTime
