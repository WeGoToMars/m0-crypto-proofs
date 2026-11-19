import M0Crypto.Thumb.RangeDecode
import M0Crypto.Release.Ed25519Build

/-!
Every code range of both Ed25519 builds decodes in the model and is tiled exactly by its
instructions (`decodeRanges_isSome`): no undecodable halfword, no instruction running into a
literal pool. Evaluated by the kernel, one build per declaration.
-/

namespace M0Crypto.Release.Ed25519CodeDecode

open M0Crypto.Thumb M0Crypto.Release.Ed25519

theorem compact_decodes :
    (decodeRanges 0 Build.compact.codeRanges Build.compact.bytes).isSome = true := by
  decide +kernel

theorem fast_decodes : (decodeRanges 0 Build.fast.codeRanges Build.fast.bytes).isSome = true := by
  decide +kernel

/-- Each code range of build `b` holds model instructions that tile it. -/
theorem decodes : ∀ b : Build, ∃ iss, RangesAt b.bytes b.codeRanges iss
  | .compact => decodeRanges_isSome compact_decodes
  | .fast => decodeRanges_isSome fast_decodes

end M0Crypto.Release.Ed25519CodeDecode
