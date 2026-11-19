import SafegcdTermination.FinalArithmetic
import SafegcdTermination.FrameWords

namespace SafegcdTermination.FinalPrepare

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open SafegcdTermination.FinalCode SafegcdTermination.FinalWords SafegcdTermination.FinalArithmetic
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.FoldRefine (vec value)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519Routines (feVal)

set_option maxHeartbeats 900000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

abbrev signAt : Nat := temp+vectorBytes-4

def subPrep : List Instr := pack ++ clearZero ++ subArgs

theorem at_base (sp : Word) : addr sp bankF = sp := by simp [bankF,addr]

theorem pack_frame (s : State) : WritesOnly s.mem (execAll pack s).mem (addr s.sp bankF) 32 := by
  rw [(show (execAll pack s).mem = _ from (pack_exec s 8 (by decide)).2), at_base]
  have hLen : (packedWords s 8).length = 8 := by simp [packedWords]
  have h := store_frame (m := s.mem) (sp := s.sp) (dst := bankF) (frame := 32)
    (vs := packedWords s 8) (by rw [hLen]; decide)
  rwa [at_base] at h

theorem zero_frame (s : State) : WritesOnly s.mem (execAll clearZero s).mem (addr s.sp bankG) 32 := by
  rw [(show (execAll clearZero s).mem = _ from (clear_zero s).1)]
  intro a ha
  apply storeWords_other
  intro i j hi hj
  rw [List.length_replicate] at hi
  rw [ofNat_add_assoc]
  exact ha (4*i+j) (by omega)

structure Ready (root t : State) (d : Int) : Prop where
  sp : t.sp = root.sp
  r0 : t.regs 0 = addr t.sp bankE
  r1 : t.regs 1 = addr t.sp bankG
  r2 : t.regs 2 = t.sp
  packed : (feVal t.mem t.sp : Int) = d
  zero : feVal t.mem (addr t.sp bankG) = 0
  outside : WritesOnly root.mem t.mem root.sp frameBytes
  sign : stackWord t signAt = stackWord root signAt
  output : stackWord t outputAt = stackWord root outputAt
  ret : stackWord t returnAt = stackWord root returnAt

private theorem add_arguments (root t : State) (d : Int) (hSp : t.sp = root.sp)
    (hPos : (feVal t.mem t.sp : Int) = d) (hNeg : feVal t.mem (addr t.sp bankG) = 0)
    (hW : WritesOnly root.mem t.mem root.sp frameBytes)
    (hSign : stackWord t signAt = stackWord root signAt)
    (hOut : stackWord t outputAt = stackWord root outputAt)
    (hRet : stackWord t returnAt = stackWord root returnAt) : Ready root (execAll subArgs t) d := by
  obtain ⟨h0,h1,h2,hM,hS⟩ := sub_args t
  have word (o : Nat) : stackWord (execAll subArgs t) o = stackWord t o := by
    unfold stackWord stackAddr
    rw [hS,hM]
  refine ⟨hS.trans hSp,?_,?_,?_,?_,?_,?_,(word _).trans hSign,(word _).trans hOut,(word _).trans hRet⟩ <;>
    simp only [hS,h0,h1,h2,hM,hPos,hNeg,hW]

/-- The in-place pack leaves the sign alone, and the subsequent zero buffer is
    disjoint from the packed positive value and the saved control words. -/
theorem sub_ready (s : State) (hf : VecWellFormed (vec s.mem s.sp)) (hz : vec s.mem s.sp 16 = 0#32) :
    Ready s (execAll subPrep s) (value s.mem s.sp) := by
  let a := execAll pack s
  let b := execAll clearZero a
  have aS : a.sp = s.sp := (pack_exec s 8 (by decide)).1
  have aW := pack_frame s
  have aV : (feVal a.mem a.sp : Int) = value s.mem s.sp := by rw [aS]; exact pack_value s hf hz
  obtain ⟨bM,bS⟩ := clear_zero a
  have bW := zero_frame a
  have bV0 : feVal b.mem (addr b.sp bankG) = 0 := by rw [bM,bS]; exact zero_feVal _ _
  have bV : (feVal b.mem b.sp : Int) = value s.mem s.sp := by
    have e := keep_field (off := bankF) bS bW (by decide) (by decide) (.inl (by decide))
    rw [at_base,at_base] at e
    rw [e,aV]
  have bFrame : WritesOnly a.mem b.mem s.sp frameBytes := by
    rw [← aS]
    exact restrict_frame (by decide : bankG+32 ≤ frameBytes) bW
  have hFrame := WritesOnly.trans (restrict_frame (by decide : bankF+32 ≤ frameBytes) aW) bFrame
  have hWords (off : Nat) (h0 : off+4 ≤ 2^32) (h1 : bankG+32 ≤ off) (h2 : bankF+32 ≤ off) :
      stackWord b off = stackWord s off :=
    (keep_stack_word bS bW h0 (by decide) (.inr h1)).trans (keep_stack_word aS aW h0 (by decide) (.inr h2))
  simp only [subPrep,execAll_append]
  exact add_arguments s b _ (bS.trans aS) bV bV0 hFrame
    (hWords signAt (by decide) (by decide) (by decide))
    (hWords outputAt (by decide) (by decide) (by decide))
    (hWords returnAt (by decide) (by decide) (by decide))

end SafegcdTermination.FinalPrepare
