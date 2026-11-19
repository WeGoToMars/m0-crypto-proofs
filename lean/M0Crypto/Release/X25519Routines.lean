import M0Crypto.Release.X25519Contract
import M0Crypto.Release.Field25519Routines

/-!
# Contract of `m0c_fe_mulc_add` (internal)

Not an audited statement: the contract the entry's proof uses for `m0c_fe_mulc_add`, proved as
an ordinary lemma (`X25519MulcAdd`), in the form of `Field25519Routines.Spec`. The routine takes
`r0 = dst`, `r1 = a`, `r2 = b` and uses 4 bytes below SP (`push {lr}`).
-/

namespace M0Crypto.Release.X25519Routines

open M0Crypto.Release.Field25519Routines (Spec)

/-- Stack bytes of `m0c_fe_mulc_add`. -/
def mulcFrame : Nat := 4

/-- `m0c_fe_mulc_add` at `off`: `dst ≡ 121666 * a + b`. -/
def MulcAddSpec (off size : Nat) : Prop :=
  Spec off size mulcFrame true fun a b => 121666 * a + b

end M0Crypto.Release.X25519Routines
