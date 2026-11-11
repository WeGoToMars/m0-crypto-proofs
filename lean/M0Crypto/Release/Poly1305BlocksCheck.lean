import M0Crypto.Release.Poly1305BlocksCode
import M0Crypto.Thumb.SeqScan

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option cbv.maxSteps 10000000

/-!
Byte checks for the release Poly1305 block code: each fact says that the frozen
artifact at an offset decodes to an instruction list defined in `Poly1305BlocksCode`,
and the four straight-line blocks are checked to be fall-through with frame
properties. They are kept out of the definitions module, so modules that need only
the instruction lists do not wait for them. The byte facts evaluate `seqScan`
through `seqAt_eq_scan`, which is linear in the artifact instead of quadratic.

Offsets are the derived names of `Poly1305BlocksCode`, not literals.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

theorem segments_at : seqAt B testAt testAlign = true ∧ seqAt B loadAAt loadA = true ∧
    seqAt B loadUAt loadU = true ∧ seqAt B bodyAt body = true ∧
    seqAt B decAt dec = true ∧ seqAt B publishAt publish = true := by
  simp only [seqAt_eq_scan]; cbv

theorem body_stable : stable body = true := by cbv
theorem body_frame : frameWB slotCount body = true := by cbv
theorem body_falls : body.all Instr.falls = true := by cbv

theorem prologue_at : seqAt B entryAt prologue = true := by simp only [seqAt_eq_scan]; cbv
theorem setup_at : seqAt B setupAt setup = true := by simp only [seqAt_eq_scan]; cbv
theorem epilogue_at : seqAt B epilogueAt epilogue = true := by simp only [seqAt_eq_scan]; cbv

end M0Crypto.Release.Poly1305Blocks
