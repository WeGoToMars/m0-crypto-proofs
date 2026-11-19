import M0Crypto.Release.Ed25519Build
import SafegcdTermination.CheckLink

namespace M0Crypto.Release.Ed25519SafegcdLink

open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact
open M0Crypto.Thumb
open SafegcdTermination.LinkedInversion

/-- All offsets are extracted from the library object used to build the archive. -/
def layout : Layout where
  first := inv_canon
  length := inv_fold - inv_canon + seqSize (SafegcdRow.FoldCode.body ++ [.bx 14])
  targets := ⟨inv_matrix-inv_canon, inv_row_exact-inv_canon, inv_row_mod-inv_canon,
    inv_fold-inv_canon, inv_correction-inv_canon⟩
  start := fe_inv_shared-inv_canon
  canon := 0
  loop := inv_phase0-inv_canon
  final := inv_final-inv_canon
  sub := inv_sub-inv_canon
  select := inv_select-inv_canon

set_option maxRecDepth 40000 in
set_option maxHeartbeats 3500000 in
theorem checked (b : Build) : Checked layout b.bytes := by
  cases b <;> check_safegcd_link

end M0Crypto.Release.Ed25519SafegcdLink
