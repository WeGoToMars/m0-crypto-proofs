import M0Crypto.Release.AeadCode
import M0Crypto.Thumb.SeqScan

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000

/-!
Byte correspondence for the release AEAD code: the instruction lists of
`m0c_chacha20poly1305_encrypt` and `m0c_chacha20poly1305_decrypt` (defined in
`AeadCode`) sit at their offsets in the frozen artifact, and the `bl` targets are the
expected entry points. Kept apart from the definitions, so that the AEAD proof chain
can start before these checks finish. The sequence facts evaluate `seqScan` through
`seqAt_eq_scan`, and the single-instruction facts evaluate `instrScan` through
`instrAt_eq_scan`; both are linear in the artifact instead of quadratic.
-/
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

theorem enc_at :
    seqAt B encOff pro = true ∧ instrAt B encXorAt = some (.bl (blImm encXorAt xorOff)) ∧
    seqAt B encCopyAt copy = true ∧ instrAt B encInitAt = some (.bl (blImm encInitAt initOff)) ∧
    seqAt B encCryptAt crypt = true ∧ instrAt B encXor1At = some (.bl (blImm encXor1At xorOff)) ∧
    seqAt B encLoadAadAt loadAad = true ∧
      MacAt encMac0At (blImm (encMac0At + macBlOff) blocksOff) (blImm (encMac0At + macBl2Off) blocksOff) ∧
    seqAt B encLoadOutAt loadOut = true ∧
      MacAt encMac1At (blImm (encMac1At + macBlOff) blocksOff) (blImm (encMac1At + macBl2Off) blocksOff) ∧
    seqAt B encLengthsAt lengths = true ∧
      instrAt B encBlocksAt = some (.bl (blImm encBlocksAt blocksOff)) ∧
    seqAt B encFinEAt finE = true ∧ instrAt B encFinishAt = some (.bl (blImm encFinishAt finishOff)) ∧
    seqAt B encClrAAt clrA = true ∧ seqAt B encClrLAt clrL = true ∧
    instrAt B encLoopBrAt = some (.bcond 1 (brImm8 encLoopBrAt encClrLAt)) ∧
    seqAt B encEpiAt epiE = true ∧ instrAt B encPopAt = some (.pop 0xf0 true) := by
  simp only [MacAt, seqAt_eq_scan, instrAt_eq_scan]; cbv; decide

theorem enc_calls :
    blTarget encXorAt (blImm encXorAt xorOff) = BitVec.ofNat 32 xorOff ∧
    blTarget encInitAt (blImm encInitAt initOff) = BitVec.ofNat 32 initOff ∧
    blTarget encXor1At (blImm encXor1At xorOff) = BitVec.ofNat 32 xorOff ∧
    blTarget encBlocksAt (blImm encBlocksAt blocksOff) = BitVec.ofNat 32 blocksOff ∧
    blTarget encFinishAt (blImm encFinishAt finishOff) = BitVec.ofNat 32 finishOff := by decide

theorem dec_at :
    seqAt B decOff pro = true ∧ instrAt B decXorAt = some (.bl (blImm decXorAt xorOff)) ∧
    seqAt B decCopyAt copy = true ∧ instrAt B decInitAt = some (.bl (blImm decInitAt initOff)) ∧
    seqAt B decLoadAadAt loadAad = true ∧
      MacAt decMac0At (blImm (decMac0At + macBlOff) blocksOff) (blImm (decMac0At + macBl2Off) blocksOff) ∧
    seqAt B decLoadInAt loadIn = true ∧
      MacAt decMac1At (blImm (decMac1At + macBlOff) blocksOff) (blImm (decMac1At + macBl2Off) blocksOff) ∧
    seqAt B decLengthsAt lengths = true ∧
      instrAt B decBlocksAt = some (.bl (blImm decBlocksAt blocksOff)) ∧
    seqAt B decFinDAt finD = true ∧ instrAt B decFinishAt = some (.bl (blImm decFinishAt finishOff)) ∧
    seqAt B decCmpAAt cmpA = true ∧ seqAt B decCmpLAt cmpL = true ∧
    instrAt B decCmpBrAt = some (.bcond 1 (brImm8 decCmpBrAt decCmpLAt)) ∧
    seqAt B decVerdictAt verdict = true ∧ instrAt B decRejectBrAt = some (.bcond 1 (brImm8 decRejectBrAt decRejectAt)) ∧
    seqAt B decCryptAt crypt = true ∧ instrAt B decXor1At = some (.bl (blImm decXor1At xorOff)) ∧
    seqAt B decAcceptAt accept = true ∧ instrAt B decSkipAt = some (.b (brImm11 decSkipAt decClrAAt)) ∧
    seqAt B decRejectAt reject = true ∧
    seqAt B decClrAAt clrA = true ∧ seqAt B decClrLAt clrL = true ∧
    instrAt B decLoopBrAt = some (.bcond 1 (brImm8 decLoopBrAt decClrLAt)) ∧
    seqAt B decEpiAt epiD = true ∧ instrAt B decPopAt = some (.pop 0xf0 true) := by
  simp only [MacAt, seqAt_eq_scan, instrAt_eq_scan]; cbv; decide

theorem dec_calls :
    blTarget decXorAt (blImm decXorAt xorOff) = BitVec.ofNat 32 xorOff ∧
    blTarget decInitAt (blImm decInitAt initOff) = BitVec.ofNat 32 initOff ∧
    blTarget decBlocksAt (blImm decBlocksAt blocksOff) = BitVec.ofNat 32 blocksOff ∧
    blTarget decFinishAt (blImm decFinishAt finishOff) = BitVec.ofNat 32 finishOff ∧
    blTarget decXor1At (blImm decXor1At xorOff) = BitVec.ofNat 32 xorOff := by decide

/-- The two functions are contiguous and end where the BLAKE2s code (padded to a 4-byte
boundary) begins. -/
theorem aead_end : encEnd = decOff ∧ decEnd ≤ Artifacts.Release.blake2s_compress := by decide

end M0Crypto.Release.Aead
