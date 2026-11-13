import M0Crypto.Release.Blake2sContract

/-!
# Frame numbers of the BLAKE2s routines

The frame sizes are named in the contract (`Blake2sContract.lean`: `compressLocalsBytes`,
`compressSavedBytes`, `streamSavedBytes`, `streamPadBytes`, `streamStackBytes`); every frame size
and slot the proofs use (`Blake2sFrames.lean`) is computed from them. The one slot named here is
internal to the compression. Changing `LOCALS` in `src/blake2s_compress.S` means changing
`compressLocalsBytes` (and regenerating the artifact), not editing the proofs that use the slots.
-/

/-- Byte offset of the saved `H_PTR` word in the compression's locals (`H_PTR` of
`src/blake2s_compress.S`). -/
def hptrBytes : Nat := 96
