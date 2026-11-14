import Lean
import M0Crypto.Release.ConstantTime.Holes

/-!
# Build-time hole map generation

`hole_map% e` evaluates `e : HoleMap` while the file is elaborated and splices the result in as
a literal term, as `ct_cert%` does for certificates. Nothing here is trusted: the kernel checks
the map with `certHoleFailure`.
-/

namespace M0Crypto.Release.ConstantTime

open Lean Elab Term Meta

deriving instance ToExpr for HEnt
deriving instance ToExpr for HTree
deriving instance ToExpr for HoleMap

syntax (name := holeMapStx) "hole_map% " term : term

@[term_elab holeMapStx] unsafe def elabHoleMap : TermElab := fun stx _ => do
  let ty := Lean.mkConst ``HoleMap
  let e ← elabTermEnsuringType stx[1] ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  return toExpr (← evalExpr HoleMap ty e)

end M0Crypto.Release.ConstantTime
