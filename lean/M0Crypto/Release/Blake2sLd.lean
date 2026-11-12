import M0Crypto.Thumb.SeqScan

/-!
# The BLAKE2s load-site instructions

`ldAll` is the set of instructions at the load sites of the five BLAKE2s entries: the loads
through a caller pointer. Every entry's read-bound proof keys its per-event predicate on this one
set, so a callee's bound lifts into its caller by the same key. An entry proves its read region
for each of these instructions it contains; the symbolic read check fails for any other entry
that contains one outside its load sites.
-/

namespace M0Crypto.Release.Blake2sLd

open M0Crypto.Thumb

def ldAll (i : Instr) : Bool :=
  match i with
  -- compress: the block and the chain words
  | .memImm .ldr 1 4 0 | .memImm .ldr 2 4 1 | .memImm .ldr 3 4 2 | .memImm .ldr 5 4 3
  | .ldm 4 0x0f | .ldm 1 0x4d
  -- copy: the source bytes
  | .memImm .ldrb 3 1 0 | .memImm .ldrh 6 7 0 | .memImm .ldrb 6 1 3 | .memImm .ldrh 3 1 0
  | .memImm .ldrh 6 1 1 | .memImm .ldr 3 1 0 | .ldm 1 0x78
  -- update and final: the context fields and the buffer
  | .memImm .ldr 2 4 8 | .memImm .ldr 3 4 9 | .memImm .ldr 7 4 26 | .memImm .ldr 6 4 26
  | .memReg .ldrb 0 4 6 => true
  | _ => false

end M0Crypto.Release.Blake2sLd
