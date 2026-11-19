import SafegcdTermination.Invert
import SafegcdTermination.LoopFootprint

namespace SafegcdTermination.EndFootprint

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.PublicTrace SafegcdTermination.TraceWrites
open SafegcdTermination.InitCode SafegcdTermination.ClearLoop SafegcdTermination.RunInit
open SafegcdTermination.Leaf (callTrace leafTrace)
open SafegcdTermination.FinalCode SafegcdTermination.FinalPrepare SafegcdTermination.FinalSub
open SafegcdTermination.FinalSelect SafegcdTermination.RunFinal
open SafegcdTermination.LoopFootprint (FrameWrites fold_writes loop_writes)
open M0Crypto.Thumb
open M0Crypto.Sym (writeChk)
open M0Crypto.Armv6M (State)
open M0Crypto.Release (Region WritesTo)

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

private theorem clear_step_writes (base a : Word) (off : Nat) :
    WritesTo (Region a 16) (clearStepTrace base off a) := by
  unfold clearStepTrace
  exact (frame (r := 0) (by decide) (by decide +kernel)).append (event rfl)

theorem clear_writes (base a : Word) (off n : Nat) : WritesTo (Region a (16*n)) (clearTrace base off a n) := by
  induction n generalizing a with
  | zero => exact WritesTo.nil _
  | succ n ih =>
    have h0 := (clear_step_writes base a off).mono (fun w h => Nat.lt_of_lt_of_le h (by omega : 16 ≤ 16*(n+1)))
    have h1 := (ih (a+16#32)).mono (fun w h => subregion (by omega : 16+16*n ≤ 16*(n+1)) h)
    exact h0.append h1

private theorem call_writes {is : List Instr} {base : Word} {off dest n : Nat} {s : State}
    (hf : is.all Instr.falls = true) (h : writeChk [(0,0,n)] is = true) :
    WritesTo (Region (s.regs 0) n) (callTrace is base off dest s) := by
  unfold callTrace leafTrace
  exact (event rfl).append ((frame (r := 0) hf h).append (event rfl))

theorem init_writes (base sp src : Word) (start canon : Nat) :
    FrameWrites sp (initTrace base sp src start canon) := by
  unfold initTrace
  have hSave : FrameWrites sp (traceAll saveAndCall (stackState (base+BitVec.ofNat 32 start) sp)) :=
    frame (r := 13) (by decide) (by decide +kernel)
  have hCanon : FrameWrites sp (callTrace canonBody base (canonSite start) canon
      (publicState [(15,base+BitVec.ofNat 32 canon),(0,addr sp temp),(1,src)])) :=
    (call_writes (n := 32) (by decide) (by decide +kernel)).mono
      (fun _ h => subregion (by decide : temp+32 ≤ frameBytes) h)
  have hClear : FrameWrites sp (clearTrace base (clearSite start) sp clearIterations) :=
    (clear_writes base sp _ _).mono (fun _ h => Nat.lt_of_lt_of_le h (by decide : 16*clearIterations ≤ frameBytes))
  have hSetup (pc : Word) : FrameWrites sp (traceAll clearSetup (stackState pc sp)) :=
    TraceWrites.quiet (by decide) (by decide +kernel)
  have hTail (pc : Word) : FrameWrites sp (traceAll InitCode.tail (stackState pc sp)) :=
    frame (r := 13) (by decide) (by decide +kernel)
  exact ((((hSave.append hCanon).append (hSetup _)).append hClear).append (hTail _))

abbrev OutWrites (sp dst : Word) := WritesTo (fun a => Region sp frameBytes a ∨ Region dst 32 a)

theorem final_writes (q : Targets) (base sp dst : Word) (off sub select : Nat) :
    OutWrites sp dst (finalTrace q base sp dst off sub select) := by
  unfold finalTrace
  have hFold : OutWrites sp dst (FoldCode.predictedTrace (base+BitVec.ofNat 32 q.fold) sp) :=
    (fold_writes _ _).mono (fun x h => .inl (Nat.lt_of_lt_of_le h (by decide : vectorBytes ≤ frameBytes)))
  have hSubPrep : FrameWrites sp (traceAll subPrep (stackState (base+BitVec.ofNat 32 (packSite off)) sp)) :=
    frame (r := 13) (by decide) (by decide +kernel)
  have hSub : OutWrites sp dst (subTrace base sp (subSite off) sub) :=
    (call_writes (n := 32) (by decide) (by decide +kernel)).mono
      (fun _ h => .inl (subregion (by decide : bankE+32 ≤ frameBytes) h))
  have hSelect : OutWrites sp dst (selectTrace base sp dst (selectSite off) select) := by
    unfold selectTrace pickTrace
    exact (TraceWrites.quiet (by decide) (by decide +kernel)).append
      ((call_writes (n := 32) (by decide) (by decide +kernel)).mono (fun _ h => .inr h))
  have hRet : OutWrites sp dst (retTrace base sp (retSite off)) := by
    unfold retTrace
    exact (TraceWrites.quiet (by decide) (by decide +kernel)).append (event rfl)
  have hFoldPre (pc : Word) : OutWrites sp dst (traceAll (prepareFold finalRow) (stackState pc sp)) :=
    TraceWrites.quiet (by decide) (by decide +kernel)
  have hFoldCall : OutWrites sp dst (⟨base+BitVec.ofNat 32 (foldSite off),callTo (foldSite off) q.fold,[]⟩ ::
      FoldCode.predictedTrace (base+BitVec.ofNat 32 q.fold) sp) :=
    (branch (base+BitVec.ofNat 32 (foldSite off)) (callTo (foldSite off) q.fold)).append hFold
  exact (((((hFoldPre _).append hFoldCall).append (hSubPrep.mono (fun _ h => .inl h))).append hSub).append hSelect).append hRet

theorem writes (q : Targets) (base sp dst src : Word) (start canon entry done sub select : Nat) :
    OutWrites sp dst (Invert.inversionTrace q base sp dst src start canon entry done sub select) := by
  exact (((init_writes base sp src start canon).append (loop_writes q base sp entry done)).mono
    (fun _ h => Or.inl h)).append (final_writes q base sp dst done sub select)

end SafegcdTermination.EndFootprint
