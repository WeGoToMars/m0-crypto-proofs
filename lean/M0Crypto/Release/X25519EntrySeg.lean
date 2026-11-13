import M0Crypto.Release.X25519EntryCode

/-!
The segments of `m0c_x25519` at their offsets (plan `x25519-proofs.md`, phase 9).

Each `*_seg` lemma gives the `seqAt` of one segment of `X25519EntryCode.entryList` at its
offset, from the single byte check `entry_at`, and `segs_end` orders the offsets up to the
end of the artifact. No segment is checked against the bytes a second time.
-/

namespace M0Crypto.Release.X25519EntrySeg
open M0Crypto.Thumb
open M0Crypto.Release (B)
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Chain (invChain)

theorem all_seg : seqAt B Artifacts.Release.x25519 prologue = true ∧
    seqAt B oLadder (ladderAt oLadder) = true ∧ seqAt B oSwap (swapAt oSwap) = true ∧
    seqAt B oDbl (dblAt oDbl) = true ∧ seqAt B oChain (chainAt oChain invChain) = true ∧
    seqAt B oFinish (finishAt oFinish) = true ∧ seqAt B oStore storeOut = true ∧
    seqAt B oWipe wipe = true ∧ seqAt B oEpi epilogue = true := by
  have h := entry_at
  simp only [entryList, seqAt_append, seqSize_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [oSwap, oLadder, Nat.add_assoc] using h3
  · simpa [oDbl, oSwap, oLadder, Nat.add_assoc] using h4
  · simpa [oChain, oDbl, oSwap, oLadder, Nat.add_assoc] using h5
  · simpa [oFinish, oChain, oDbl, oSwap, oLadder, Nat.add_assoc] using h6
  · simpa [oStore, oFinish, oChain, oDbl, oSwap, oLadder, Nat.add_assoc] using h7
  · simpa [oWipe, oStore, oFinish, oChain, oDbl, oSwap, oLadder, Nat.add_assoc] using h8
  · simpa [oEpi, oWipe, oStore, oFinish, oChain, oDbl, oSwap, oLadder, Nat.add_assoc] using h9

theorem prologue_seg : seqAt B Artifacts.Release.x25519 prologue = true := all_seg.1
theorem ladder_seg : seqAt B oLadder (ladderAt oLadder) = true := all_seg.2.1
theorem swap_seg : seqAt B oSwap (swapAt oSwap) = true := all_seg.2.2.1
theorem dbl_seg : seqAt B oDbl (dblAt oDbl) = true := all_seg.2.2.2.1
theorem chain_seg : seqAt B oChain (chainAt oChain invChain) = true := all_seg.2.2.2.2.1
theorem finish_seg : seqAt B oFinish (finishAt oFinish) = true := all_seg.2.2.2.2.2.1
theorem store_seg : seqAt B oStore storeOut = true := all_seg.2.2.2.2.2.2.1
theorem wipe_seg : seqAt B oWipe wipe = true := all_seg.2.2.2.2.2.2.2.1
theorem epi_seg : seqAt B oEpi epilogue = true := all_seg.2.2.2.2.2.2.2.2

/-- The epilogue ends at the end of the artifact; with the definitions of the offsets this
bounds every segment. -/
theorem epi_end : oEpi + seqSize epilogue = Artifacts.Release.size := by
  have h := entry_size
  simp only [entryList, seqSize_append] at h
  simp only [oEpi, oWipe, oStore, oFinish, oChain, oDbl, oSwap, oLadder] at h ⊢
  omega

end M0Crypto.Release.X25519EntrySeg
