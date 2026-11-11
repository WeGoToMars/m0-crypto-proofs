import M0Crypto.Release.ConstantTime.SpSound

/-! Relational semantics for loading a sequence of stack words into registers. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg)
open M0Crypto.Thumb

/-- Abstract sequential register loads from a fixed stack snapshot. -/
def loadStackRegs (stk : Stk) : Int → List LowReg → AbsState → AbsState
  | _, [], st => st
  | off, r :: rs, st => loadStackRegs stk (off + 4) rs (st.set r.val (stkGet stk off))

/-- Loading the same sequence of stack slots preserves the paired relation,
including comparison, fact, and link invalidation on each register write. -/
theorem loadStackRegs_sound {p : Params} {bytes : List (BitVec 8)} {pc : Nat}
    (stk : Stk) (off : Int) (rs : List LowReg) (st : AbsState) (s₁ s₂ : State)
    (hidx : st.indicesOk) (hstack : st.stk = stk) (h : LowEq p bytes pc st s₁ s₂) :
    LowEq p bytes pc (loadStackRegs stk off rs st)
      (loadRegs s₁ (p.sp0 + BitVec.ofInt 32 off) (rs.map LowReg.toReg))
      (loadRegs s₂ (p.sp0 + BitVec.ofInt 32 off) (rs.map LowReg.toReg)) := by
  induction rs generalizing off st s₁ s₂ with
  | nil => exact h
  | cons r rs ih =>
    have hr : regIndexOk r.val := by
      constructor <;> have := r.isLt <;> simp [numRegs] <;> omega
    have hv := h.stack off
    rw [hstack] at hv
    have hw := paired_setReg_sound hr hidx h hv
    have hreg : (⟨r.val, by have := hr.1; simp [numRegs] at this; omega⟩ :
        M0Crypto.Armv6M.Reg) = r.toReg := by
      apply Fin.ext; rfl
    rw [hreg] at hw
    have hs : (st.set r.val (stkGet stk off)).stk = stk := by simpa [AbsState.set] using hstack
    have hn := ih (off + 4) (st.set r.val (stkGet stk off)) _ _
      (AbsState.indicesOk_set hidx) hs hw
    have haddr : p.sp0 + BitVec.ofInt 32 (off + 4) =
        (p.sp0 + BitVec.ofInt 32 off) + 4#32 := by
      rw [BitVec.ofInt_add, BitVec.add_assoc]
      rfl
    simpa [loadStackRegs, loadRegs, haddr] using hn

/-- The indexed fold used by the analyzer is the same sequential load. -/
theorem loadStackRegs_fold (stk : Stk) (base : Int) (rs : List LowReg) (k : Nat) (st : AbsState) :
    ((rs.map (fun r : LowReg => r.val)).zip (List.range' k rs.length)).foldl
      (fun s (r, j) => s.set r (stkGet stk (base + (4 * j : Nat)))) st =
    loadStackRegs stk (base + (4 * k : Nat)) rs st := by
  induction rs generalizing k st with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.zip_cons_cons,
      List.foldl_cons, loadStackRegs]
    rw [ih]
    have heq : base + (4 * (k + 1) : Nat) = base + (4 * k : Nat) + 4 := by omega
    rw [heq]

/-- The analyzer's pop fold agrees with the relational register-load model. -/
theorem pop_load_fold (stk : Stk) (base : Int) (l : BitVec 8) (st : AbsState) :
    ((regsOf l).zip (List.range (regsOf l).length)).foldl
      (fun s (r, k) => s.set r (stkGet stk (base + (4 * k : Nat)))) st =
    loadStackRegs stk base (listRegs l) st := by
  simpa [regsOf, List.length_map, List.range_eq_range'] using
    loadStackRegs_fold stk base (listRegs l) 0 st

/-- Loading tracked registers preserves index well-formedness. -/
theorem loadStackRegs_indices (stk : Stk) (off : Int) (rs : List LowReg) (st : AbsState)
    (h : st.indicesOk) : (loadStackRegs stk off rs st).indicesOk := by
  induction rs generalizing off st with
  | nil => exact h
  | cons r rs ih => exact ih (off + 4) _ (AbsState.indicesOk_set h)

end M0Crypto.Release.ConstantTime
