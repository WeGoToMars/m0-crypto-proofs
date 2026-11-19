import SafegcdTermination.EndFootprint
import SafegcdTermination.CodeWindow

namespace SafegcdTermination.Invert

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.CodeWindow (fetched_inside run_length)
open SafegcdTermination.EndFootprint (OutWrites writes)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
open M0Crypto.Release (Region)
open M0Crypto.Release.Field25519Routines (feVal)

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Correct inversion in the release model with unified code and data memory.
    The exact trace reveals only the public code, stack, input and output addresses. -/
theorem verified {code : List (BitVec 8)} {q : Targets} {base : Word} {s : State} {fuel : Nat}
    {start canon entry done sub select : Nat}
    (linked : Place code q start canon entry done sub select) (h : Pre s base code start)
    (hRet : ¬ Region base code.length (s.regs 14 &&& ~~~1#32))
    (hFuel : (inversionTrace q base s.sp (s.regs 0) (s.regs 1) start canon entry done sub select).length ≤ fuel) :
    let tr := inversionTrace q base s.sp (s.regs 0) (s.regs 1) start canon entry done sub select
    ∃ t, runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t,tr) ∧
      RunFinal.Result s t (s.regs 0) (s.regs 14) (feVal s.mem (s.regs 1)) ∧
      CodeAt t.mem base code ∧ OutWrites s.sp (s.regs 0) tr := by
  obtain ⟨t,n,hH,hResult,hCode⟩ := functional linked h
  have hW := writes q base s.sp (s.regs 0) (s.regs 1) start canon entry done sub select
  have hMiss := TraceWrites.noCode h.codeFrame h.codeOutput hW
  refine ⟨t,?_,hResult,hCode,hW⟩
  refine runUntil_of_runH n fuel s t _ h.bytes hH hMiss ?_ hResult.pc ?_
  · intro e he eq
    exact hRet (eq ▸ fetched_inside hH e he)
  · rwa [run_length hH]

end SafegcdTermination.Invert
