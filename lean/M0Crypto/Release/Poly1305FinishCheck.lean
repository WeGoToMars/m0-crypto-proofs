import M0Crypto.Release.Poly1305FinishCode
import M0Crypto.Release.Poly1305BlocksCode
import M0Crypto.Thumb.SeqScan

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000

/-!
Byte checks for the release Poly1305 finish code: the four segments and the trap
return of `m0c_poly1305_finish` decode to the instruction lists in `Poly1305FinishCode`,
and the arithmetic block is fall-through, store-free and stable. Kept apart from the
definitions so that the arithmetic lists do not wait for the byte checks. The byte
fact evaluates `seqScan` through `seqAt_eq_scan`.
-/
namespace M0Crypto.Release.Poly1305Finish
open M0Crypto.Thumb

theorem segments_at : seqAt B entryAt header = true ∧ seqAt B arithAt arithmetic = true ∧
    seqAt B emitAt emit = true ∧ seqAt B clearAt clear = true ∧ instrAt B popAt = some (.pop 0xf0 true) := by
  simp only [seqAt_eq_scan]; cbv

theorem calc_stable : Poly1305Blocks.stable arithmetic = true := by cbv
theorem calc_falls : arithmetic.all Instr.falls = true := by cbv
theorem calc_noW : arithmetic.all (!·.writesMem) = true := by cbv

end M0Crypto.Release.Poly1305Finish
