import SafegcdTermination.CodeWindow
import M0Crypto.Release.StackEffectSym

namespace SafegcdTermination.CodeStack

open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release (CodeBytes StepsOk runH_succ_ok)
open M0Crypto.Release.StackEffect (keep_sp exec_sp)

/-- Scan halfword offsets in the linked window for instructions that could change SP.
    Decoding the first instruction of each remaining suffix keeps the check linear. -/
def check : List (BitVec 8) → Bool
  | a :: b :: rest =>
    ((instrAt (a :: b :: rest) 0).all fun i => !(i.dsts.contains 13)) && check rest
  | _ => true

private theorem instr_keeps_sp (bytes : List (BitVec 8)) (off : Nat) (i : Instr)
    (h : check bytes = true) (he : off % 2 = 0) (hl : off + i.size ≤ bytes.length)
    (hi : instrAt bytes off = some i) : (!(i.dsts.contains 13)) = true := by
  have hWidth : 2 ≤ i.size := by cases i <;> simp [Instr.size]
  induction bytes using check.induct generalizing off with
  | case1 a b rest ih =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hZero : off = 0
    · subst off
      rw [hi] at h
      exact h.1
    · have hOff : off = 2 + (off - 2) := by omega
      have hAt : instrAt rest (off - 2) = some i := by
        have hShift : instrAt ((a :: b :: rest).drop 2) (off - 2) =
            instrAt (a :: b :: rest) (2 + (off - 2)) := by
          simp only [instrAt, hwAt_drop, Nat.add_assoc]
        rw [← hOff, hi] at hShift
        exact hShift
      have hBound : off - 2 + i.size ≤ rest.length := by
        simp only [List.length_cons] at hl
        omega
      exact ih (off-2) h.2 (by omega) hBound hAt
  | case2 bytes hRest =>
    cases bytes with
    | nil => simp only [List.length_nil] at hl; omega
    | cons a tail =>
      cases tail with
      | nil => change off + i.size ≤ 1 at hl; omega
      | cons b rest => exact False.elim (hRest a b rest rfl)

theorem step_instruction {bytes : List (BitVec 8)} {base : Word} {s t : State} {e : Event}
    (h : stepH bytes base s = .ok (t,e)) :
    e.instr.exec s = .ok t ∧ ¬ s.pc.getLsbD 0 = true ∧
      instrAt bytes (s.pc-base).toNat = some e.instr ∧ (s.pc-base).toNat + e.instr.size ≤ bytes.length := by
  unfold stepH at h
  simp only at h
  split at h
  · cases h
  · rename_i hOdd
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hBound
        split at h
        · split at h
          · rename_i t' hExec
            cases h
            exact ⟨hExec,hOdd,hi,hBound⟩
          · cases h
        · cases h
      · cases h

theorem step_keeps_sp {bytes : List (BitVec 8)} {base : Word} {s t : State} {e : Event}
    (hChk : check bytes = true) (hBase : base.toNat % 2 = 0)
    (h : stepH bytes base s = .ok (t,e)) :
    (!(e.instr.dsts.contains 13)) = true ∧ t.sp = s.sp := by
  obtain ⟨hExec,hOdd,hAt,hBound⟩ := step_instruction h
  have hp : s.pc.toNat % 2 = 0 := by
    simp only [BitVec.getLsbD,Nat.testBit_zero,decide_eq_true_eq] at hOdd
    omega
  have ho : (s.pc-base).toNat % 2 = 0 := by bv_omega
  have hI := instr_keeps_sp bytes _ e.instr hChk ho hBound hAt
  have hS := keep_sp hI s.sp
  exact ⟨hI,(exec_sp hS.2 hExec).trans hS.1⟩

/-- Every recorded instruction keeps SP. The proof uses the checked bytes, including
    for branch and return events that are outside straight-line block checks. -/
theorem trace_keeps_sp {bytes : List (BitVec 8)} {base : Word} {s t : State} {k : Nat} {tr : List Event}
    (hChk : check bytes = true) (hBase : base.toNat % 2 = 0)
    (h : runH bytes base k s = .ok (t,tr)) :
    ∀ e ∈ tr, (!(e.instr.dsts.contains 13)) = true := by
  induction k generalizing s t tr with
  | zero => cases h; intro e he; exact False.elim (List.not_mem_nil he)
  | succ k ih =>
    simp only [runH] at h
    split at h
    · cases h
    · rename_i u e hU
      split at h
      · cases h
      · rename_i v es hV
        cases h
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact (step_keeps_sp hChk hBase hU).1
        · exact ih hV f hf

/-- A fixed-SP run with proved event bounds satisfies the stepwise release judgment. -/
theorem steps_of_run {bytes : List (BitVec 8)} {sz : Nat} [CodeBytes bytes sz]
    {base : Word} {s t : State} {k : Nat} {tr : List Event} {P : Event → Prop}
    (h : runH bytes base k s = .ok (t,tr)) (hP : ∀ e ∈ tr, P e)
    (hSp : ∀ e ∈ tr, (!(e.instr.dsts.contains 13)) = true) :
    StepsOk base (fun u e => P e ∧ u.sp = s.sp) k s := by
  induction k generalizing s t tr with
  | zero => trivial
  | succ k ih =>
    obtain ⟨u,e,tail,hU,hTail,rfl⟩ := runH_succ_ok h
    have hE := List.mem_cons_self (a := e) (l := tail)
    have hs := keep_sp (hSp e hE) s.sp
    have hkeep : u.sp = s.sp := (exec_sp hs.2 (step_instruction hU).1).trans hs.1
    have hOk := ih hTail (fun e he => hP e (List.mem_cons_of_mem _ he))
      (fun e he => hSp e (List.mem_cons_of_mem _ he))
    rw [hkeep] at hOk
    exact StepsOk.cons hU ⟨hP e hE,rfl⟩ hOk

end SafegcdTermination.CodeStack
