import Lean
import M0Crypto.Release.ConstantTime.Cert

/-!
# Build-time constant-time certificate generation

`ct_cert% e` evaluates `e : Except String Cert` while the file is elaborated and splices
the resulting certificate in as a literal term. An error from the analysis becomes an
elaboration error.

Nothing here is trusted. The kernel checks the certificate with `certOk`, a plain
function (`ConstantTime/Entries.lean`), so a wrong generator only makes that check fail. The
evaluation uses the compiled code of `gen`; it is the reason this file needs `unsafe`.
-/

namespace M0Crypto.Release.ConstantTime

open Lean Elab Term Meta
open M0Crypto.Thumb

deriving instance ToExpr for M0Crypto.Thumb.DpOp
deriving instance ToExpr for M0Crypto.Thumb.MemOp
deriving instance ToExpr for M0Crypto.Thumb.Instr
deriving instance ToExpr for AbsVal
deriving instance ToExpr for AbsFlags
deriving instance ToExpr for Opnd
deriving instance ToExpr for Cmp
deriving instance ToExpr for AFl
deriving instance ToExpr for Lnk
deriving instance ToExpr for AbsState
deriving instance ToExpr for Blk

syntax (name := ctCertStx) "ct_cert% " term : term

@[term_elab ctCertStx] unsafe def elabCtCert : TermElab := fun stx _ => do
  let ty := mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String)
    (mkConst ``Cert)
  let e ← elabTermEnsuringType stx[1] ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← evalExpr (Except String Cert) ty e with
  | .error msg => throwError "Constant-time analysis failed: {msg}"
  | .ok c => return toExpr c

end M0Crypto.Release.ConstantTime
