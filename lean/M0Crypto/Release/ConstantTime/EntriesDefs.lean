import M0Crypto.Release.ConstantTime.Elab
import M0Crypto.Release.TraceSpecDefs
import M0Crypto.Release.AeadCode

/-!
# Entry environments and states

Shared by the certificate files `ChaCha20Entry`, `AeadEncryptEntry` and `AeadDecryptEntry`.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

/-- Stack arguments of `m0c_chacha20_xor`: `nonce` and `ctr`. -/
def chacha20ArgWords : Nat := 2

/-- Stack arguments of the AEAD entries: `aad`, `alen`, `key`, `nonce`. -/
def aeadArgWords : Nat := 4

def chacha20Env : Env := ⟨⟨TraceSpec.chacha20StackBytes, 4 * chacha20ArgWords⟩, Release.size, none, [], false⟩

def encryptEnv : Env := ⟨⟨TraceSpec.aeadStackBytes, 4 * aeadArgWords⟩, Release.size, none, [], false⟩

def decryptEnv : Env :=
  ⟨⟨TraceSpec.aeadStackBytes, 4 * aeadArgWords⟩, Release.size, some Aead.decRejectBrAt, [], false⟩

/-- Entry registers: the first `np` register arguments are public, LR is the entry LR, all other
registers (including unused argument registers) are secret. -/
def entryRegsP (np : Nat) : List AbsVal :=
  (List.range numRegs).map fun r => if r < np then .lo else if r == 14 then .lr0 else .hi

/-- Entry state with `np` public register arguments and `args` public stack arguments at
`sp0 + 4k`. -/
def entryStateP (np args : Nat) : AbsState :=
  ⟨entryRegsP np, 0, AFl.all .hi, (List.range args).map fun k => ((4 * k : Nat), AbsVal.lo), [], []⟩

/-- Entry registers: the four register arguments are public, LR is the entry LR. -/
def entryRegs : List AbsVal := entryRegsP 4

/-- Entry state with `args` public stack arguments at `sp0 + 4k`. -/
def entryState (args : Nat) : AbsState := entryStateP 4 args

/-- Fuel of the generator's worklist. -/
def genFuel : Nat := 400000

end M0Crypto.Release.ConstantTime
