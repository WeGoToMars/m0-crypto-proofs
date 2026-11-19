import M0Crypto.Release.Contract

/-!
# The code bytes of the routine tooling

The judgments of the routine tooling (`Reach`, `ReachS`, `ReachT`, `Routine` and the rules over
them) and the `Field25519` proofs are stated over a byte list `B` of length `BS`, fixed by an
instance of `CodeBytes B BS`. Both are output parameters: a judgment written without them takes
the bytes of the instance in scope. The instance `release` below is the workspace's release
bytes, so a single-build asset's proofs elaborate to `Release.B` and `Artifacts.Release.size` as
before. A proof about another byte list (each build of the Ed25519 asset) brings its own instance
into scope with `letI`/`haveI`; a local instance takes precedence over `release`.
-/

namespace M0Crypto.Release

/-- `B` is the code: `size` bytes, fewer than 2^32. -/
class CodeBytes (B : outParam (List (BitVec 8))) (size : outParam Nat) : Prop where
  len : B.length = size
  lt : size < 2 ^ 32

/-- The workspace's release bytes. -/
instance release : CodeBytes B Artifacts.Release.size := ⟨Artifacts.Release.bytes_length, by decide⟩

end M0Crypto.Release
