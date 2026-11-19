import SafegcdTermination.InitWords
import SafegcdTermination.Bank
import M0Crypto.Release.Field25519Mul128

namespace SafegcdTermination.Canon

open SafegcdRow
open SafegcdTermination.InitCode
open SafegcdTermination.Bank
open M0Crypto.Armv6M (State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr read32_storeWords_same ne_of_disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)
open M0Crypto.Release.Field25519Mem
open M0Crypto.Release.Field25519Comb (listRegs_3c)

set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 12000

def sourceWords (s : State) (n : Nat) : List Word :=
  (List.range n).map fun i => read32 s.mem (slot (s.regs 1) i)

open M0Crypto.Sym M0Crypto.Release.BlockEffect
open SafegcdTermination.InitWords (storeExprWords denote_storeExprWords)

def readExpressions : List SExpr :=
  (List.range 4).map fun i => .ld32 .mem0 (.add (.reg0 1) (.const (BitVec.ofNat 32 (4*i))))

def copyEffect : Eff :=
  { regs := [(0,.add (.reg0 0) (.const 16)),(1,.add (.reg0 1) (.const 16))]
    clob := [2,3,4,5]
    mem := some (storeExprWords (.reg0 0) .mem0 readExpressions) }

theorem copy_effect : effOk copyBlock copyEffect = true := by decide +kernel

theorem copy_four (s : State) :
    let t := execAll copyBlock s
    t.regs 0 = s.regs 0 + 16#32 ∧ t.regs 1 = s.regs 1 + 16#32 ∧
      t.mem = storeWords s.mem (s.regs 0) (sourceWords s 4) ∧ t.sp = s.sp := by
  have h := eff_run copy_effect s
  have hmem := h.mem _ rfl
  rw [denote_storeExprWords] at hmem
  refine ⟨h.reg 0 (by decide) (by decide),h.reg 1 (by decide) (by decide),?_,h.reg 13 (by decide) (by decide)⟩
  simpa only [readExpressions,List.map_map,Function.comp_def,SExpr.denote,SMem.denote,sourceWords,slot] using hmem

private theorem twice_copied (s u v : State)
    (hd : (s.regs 0).toNat+32 ≤ 2^32) (hs : (s.regs 1).toNat+32 ≤ 2^32)
    (hSep : (s.regs 0).toNat+32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat+32 ≤ (s.regs 0).toNat)
    (u0 : u.regs 0 = s.regs 0 + 16#32) (u1 : u.regs 1 = s.regs 1 + 16#32)
    (um : u.mem = storeWords s.mem (s.regs 0) (sourceWords s 4))
    (vm : v.mem = storeWords u.mem (u.regs 0) (sourceWords u 4)) :
    v.mem = storeWords s.mem (s.regs 0) (sourceWords s 8) := by
  have hRead (i : Nat) (hi : i < 4) :
      read32 u.mem (slot (u.regs 1) i) = read32 s.mem (slot (s.regs 1) (4+i)) := by
    have hAddr : slot (u.regs 1) i = slot (s.regs 1) (4+i) := by
      rw [u1]
      simp only [slot, Nat.mul_add, Nat.mul_comm 4 i]
      rw [ofNat_add_assoc]
    rw [hAddr,um]
    apply read32_congr
    intro j hj
    apply storeWords_other
    intro k l hk hl
    have hLen : (sourceWords s 4).length = 4 := by simp [sourceWords]
    rw [hLen] at hk
    simp only [slot, ofNat_add_assoc]
    exact (ne_of_disj hd hs hSep (by omega : 4*k+l < 32) (by omega : 4*(4+i)+j < 32)).symm
  have hWords : sourceWords u 4 = ((List.range 4).map fun i => read32 s.mem (slot (s.regs 1) (4+i))) := by
    unfold sourceWords
    apply List.map_congr_left
    intro i hi
    exact hRead i (List.mem_range.mp hi)
  have eWords : sourceWords s 4 ++ sourceWords u 4 = sourceWords s 8 := by
    rw [hWords]
    rfl
  have hL : (sourceWords s 4).length = 4 := by simp [sourceWords]
  rw [vm,um,u0,← eWords,M0Crypto.Release.Field25519Mul128.storeWords_append,hL]

private theorem reset_destination (s v : State)
    (h0 : v.regs 0 = s.regs 0 + 32#32) (hSp : v.sp = s.sp)
    (hm : v.mem = storeWords s.mem (s.regs 0) (sourceWords s 8)) :
    let t := execAll [.subImm8 0 32] v
    t.regs 0 = s.regs 0 ∧ t.sp = s.sp ∧
      t.mem = storeWords s.mem (s.regs 0) (sourceWords s 8) := by
  have hReg : (execAll [.subImm8 0 32] v).regs 0 = v.regs 0 - 32#32 := by
    row_simps
    exact M0Crypto.Release.sub_flags (v.regs 0) 32#32
  refine ⟨?_,hSp,hm⟩
  rw [hReg,h0]
  bv_omega

theorem copy_words (s : State)
    (hd : (s.regs 0).toNat+32 ≤ 2^32) (hs : (s.regs 1).toNat+32 ≤ 2^32)
    (hSep : (s.regs 0).toNat+32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat+32 ≤ (s.regs 0).toNat) :
    let t := execAll copyWords s
    t.regs 0 = s.regs 0+32#32 ∧ t.sp = s.sp ∧
      t.mem = storeWords s.mem (s.regs 0) (sourceWords s 8) := by
  let u := execAll copyBlock s
  let v := execAll copyBlock u
  obtain ⟨u0,u1,um,usp⟩ := copy_four s
  obtain ⟨v0,_,vm,vsp⟩ := copy_four u
  have hO : v.regs 0 = s.regs 0 + 32#32 := by rw [v0,u0]; bv_omega
  have hM := twice_copied s u v hd hs hSep u0 u1 um vm
  simpa only [copyWords,execAll_append] using And.intro hO (And.intro (vsp.trans usp) hM)

theorem copy_eight (s : State)
    (hd : (s.regs 0).toNat+32 ≤ 2^32) (hs : (s.regs 1).toNat+32 ≤ 2^32)
    (hSep : (s.regs 0).toNat+32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat+32 ≤ (s.regs 0).toNat) :
    let t := execAll copyPrefix s
    t.regs 0 = s.regs 0 ∧ t.sp = s.sp ∧
      t.mem = storeWords s.mem (s.regs 0) (sourceWords s 8) := by
  obtain ⟨h0,hSp,hM⟩ := copy_words s hd hs hSep
  simpa only [copyPrefix,execAll_append] using reset_destination s (execAll copyWords s) h0 hSp hM

theorem copy_value (s : State) :
    feVal (storeWords s.mem (s.regs 0) (sourceWords s 8)) (s.regs 0) = feVal s.mem (s.regs 1) := by
  simp only [feVal_psum]
  apply psum_congr
  intro i hi
  have hLen : i < (sourceWords s 8).length := by simpa [sourceWords] using hi
  have hRead := read32_storeWords_same s.mem (s.regs 0) (sourceWords s 8) i hLen (by simp [sourceWords])
  have hw : (sourceWords s 8)[i] = read32 s.mem (slot (s.regs 1) i) := by
    simp [sourceWords]
  rw [hw] at hRead
  exact congrArg BitVec.toNat hRead

private theorem canon_after_copy (s u : State)
    (h0 : u.regs 0 = s.regs 0)
    (hm : u.mem = storeWords s.mem (s.regs 0) (sourceWords s 8)) :
    feVal (execAll M0Crypto.Release.Field25519Canon.body u).mem (s.regs 0) =
      feVal s.mem (s.regs 1) % M0Crypto.Release.Field25519Reduce.pN := by
  rw [← h0, (M0Crypto.Release.Field25519Canon.body_val u).1, h0, hm, copy_value s]

theorem body_value (s : State)
    (hd : (s.regs 0).toNat+32 ≤ 2^32) (hs : (s.regs 1).toNat+32 ≤ 2^32)
    (hSep : (s.regs 0).toNat+32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat+32 ≤ (s.regs 0).toNat) :
    feVal (execAll canonBody s).mem (s.regs 0) = feVal s.mem (s.regs 1) % M0Crypto.Release.Field25519Reduce.pN := by
  obtain ⟨h0,_,hm⟩ := copy_eight s hd hs hSep
  rw [canonBody,execAll_append]
  exact canon_after_copy s (execAll copyPrefix s) h0 hm

end SafegcdTermination.Canon
