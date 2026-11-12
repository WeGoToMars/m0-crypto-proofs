/-!
# The one number the BLAKE2s frame sizes derive from

`src/blake2s_compress.S` reserves `LOCALS` bytes of locals and saves r4-r11 and lr (36 bytes).
Every frame size and frame slot the proofs name (`Blake2sFrames.lean`) is computed from the
value here. Changing `LOCALS` in the assembly means changing this number (and regenerating the
artifact), not editing the proofs that use the slots.
-/

/-- `LOCALS` of `src/blake2s_compress.S`, in bytes. -/
def localsBytes : Nat := 100

/-- Registers saved by the compression prologue (r4-r11, lr), in bytes. -/
def savedBytes : Nat := 36

/-- Offset of the saved `H_PTR` word (`H_PTR` in the assembly). -/
def hptrBytes : Nat := 96
