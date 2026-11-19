import SafegcdTermination.LinkedInversion
import M0Crypto.Thumb.SeqScan
import M0Crypto.Thumb.Diagnose

namespace SafegcdTermination.LinkedInversion

open M0Crypto.Thumb
open SafegcdRow
open SafegcdTermination.LoopControl SafegcdTermination.LoopLinks

/-- Prove a concrete layout from the artifact. The byte checks run the model's
    decoder. Each instruction list has offsets derived from the surrounding lists.
    Diagnose instruction mismatches with `seqAtFailure` on `Layout.window`. -/
macro "check_safegcd_link" : tactic => `(tactic|
  (refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
   refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel, ?_, ?_, ?_⟩
   · apply SafegcdTermination.RunInit.place_of_link
     · rw [seqAt_eq_scan]; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · decide +kernel
   · refine ⟨⟨?_, ?_, ?_, ?_, by decide +kernel⟩, ?_, ?_, ?_, ?_, ?_⟩
     · rw [seqAt_eq_scan]; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · intro i
       rcases SafegcdRow.BatchCode.phase_cases i with h | h | h <;> subst i <;> dsimp only <;> rw [seqAt_eq_scan] <;> decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · unfold TargetMatches; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · unfold TargetMatches; decide +kernel
   · refine ⟨by decide +kernel, by decide +kernel, ?_⟩
     decide +kernel
   · apply SafegcdTermination.RunFinal.place_of_link
     · rw [seqAt_eq_scan]; decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · decide +kernel
     · rw [seqAt_eq_scan]; decide +kernel
     · decide +kernel))

end SafegcdTermination.LinkedInversion
