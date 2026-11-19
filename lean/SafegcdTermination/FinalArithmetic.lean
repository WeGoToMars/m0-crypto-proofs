import SafegcdTermination.FinalWords
import SafegcdTermination.FieldInverse
import SafegcdTermination.InitWords

namespace SafegcdTermination.FinalArithmetic

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.FinalCode
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.InitWords (storeExprWords denote_storeExprWords)
open M0Crypto.Armv6M (State Mem)
open M0Crypto.Thumb
open M0Crypto.Sym M0Crypto.Release.BlockEffect
open M0Crypto.Release.Frame (read32_storeWords_same)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)

set_option maxHeartbeats 700000
set_option maxRecDepth 13000
set_option linter.unusedSimpArgs false

def zeroEffect : Eff :=
  let a := SExpr.add (.reg0 13) (.const (BitVec.ofNat 32 bankG))
  { regs := [(0,a), (1,.const 0)]
    mem := some (storeExprWords a .mem0 (List.replicate 8 (.const 0))) }

theorem zero_effect : effOk clearZero zeroEffect = true := by decide +kernel

theorem clear_zero (s : State) :
    let t := execAll clearZero s
    t.mem = storeWords s.mem (addr s.sp bankG) (List.replicate 8 0) ∧ t.sp = s.sp := by
  have h := eff_run zero_effect s
  have hM := h.mem _ rfl
  rw [denote_storeExprWords] at hM
  refine ⟨?_, h.reg 13 (by decide) (by decide)⟩
  exact hM

theorem zero_feVal (m : Mem) (a : Word) :
    feVal (storeWords m a (List.replicate 8 0)) a = 0 := by
  rw [feVal_psum]
  have h := psum_congr (f := fun i => (vec (storeWords m a (List.replicate 8 0)) a i).toNat)
    (g := fun _ => 0) (j := 8) (fun i hi => by
      have hr := read32_storeWords_same m a (List.replicate 8 (0 : Word)) i
        (by simpa only [List.length_replicate]) (by decide)
      have hh : vec (storeWords m a (List.replicate 8 0)) a i = 0#32 := by
        have hz : (List.replicate 8 (0 : Word))[i] = 0#32 := by exact List.getElem_replicate _
        rw [hz] at hr
        exact hr
      rw [hh]
      rfl)
  exact h.trans rfl

theorem sign_word (w : Word) : w.sshiftRight 31 = if w.toInt < 0 then -1#32 else 0#32 := by
  have hInt : (w.sshiftRight 31).toInt = w.toInt / 2147483648 := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    rfl
  have hLo : -2147483648 ≤ w.toInt := by
    have e := @BitVec.le_two_mul_toInt 32 w
    omega
  have hHi : w.toInt < 2147483648 := by
    have e := @BitVec.two_mul_toInt_lt 32 w
    omega
  apply BitVec.eq_of_toInt_eq
  rw [hInt]
  split
  · change w.toInt / 2147483648 = -1
    omega
  · change w.toInt / 2147483648 = 0
    omega

end SafegcdTermination.FinalArithmetic
