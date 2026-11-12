import M0Crypto.Release.Blake2sTail
import M0Crypto.Release.Blake2sCompressCode
import M0Crypto.Release.Blake2sStreamSites

/-!
# Output-store sites of `m0c_blake2s_compress`

The compression writes the chain window `h` with two four-word `stm`s through a register the
constant-time analysis does not track: the first instruction of `S2b` and the single `stm`
of `S3b` in the tail. Every other store is `sp`-tracked. `compressSites` lists their code
offsets; the proofs bound the bytes written at these pcs by the chain window.
-/

namespace M0Crypto.Release.Blake2sCode

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sTail

/-- Code offsets of the two untracked `stm`s. -/
def compressSites : List Nat :=
  let s2b := tailOff + seqSize S1 + seqSize S2a
  [s2b, s2b + seqSize S2b + seqSize S3a]

theorem compressSites_ge : ∀ off ∈ compressSites, tailOff ≤ off := by
  decide +kernel

theorem compressSites_lt : ∀ off ∈ compressSites, off < Artifacts.Release.size := by
  decide +kernel

open M0Crypto.Release.Blake2sStreamCode (initSites copySites updateSites finalSites)

/-- Every untracked store of the library that a streaming entry can reach, by code offset. The
write bounds of `compress` and `copy` are stated against this list, so that a caller can reuse
them for its own: at a listed pc the run writes only the destination the store addresses. -/
def allSites : List Nat := compressSites ++ initSites ++ copySites ++ updateSites ++ finalSites

theorem allSites_ge : ∀ off ∈ allSites, tailOff ≤ off := by decide +kernel

theorem allSites_lt : ∀ off ∈ allSites, off < Artifacts.Release.size := by decide +kernel

/-- Program counters of the sites in an artifact loaded at `base`. -/
def SiteAt (base : Word) (pc : Word) : Prop :=
  ∃ off ∈ allSites, pc = base + BitVec.ofNat 32 off

theorem siteAt_of_compress {base pc : Word} {off : Nat} (h : off ∈ compressSites)
    (he : pc = base + BitVec.ofNat 32 off) : SiteAt base pc :=
  ⟨off, by simp [allSites, h], he⟩

theorem siteAt_of_init {base pc : Word} {off : Nat} (h : off ∈ initSites)
    (he : pc = base + BitVec.ofNat 32 off) : SiteAt base pc :=
  ⟨off, by simp [allSites, h], he⟩

theorem siteAt_of_copy {base pc : Word} {off : Nat} (h : off ∈ copySites)
    (he : pc = base + BitVec.ofNat 32 off) : SiteAt base pc :=
  ⟨off, by simp [allSites, h], he⟩

theorem siteAt_of_update {base pc : Word} {off : Nat} (h : off ∈ updateSites)
    (he : pc = base + BitVec.ofNat 32 off) : SiteAt base pc :=
  ⟨off, by simp [allSites, h], he⟩

theorem siteAt_of_final {base pc : Word} {off : Nat} (h : off ∈ finalSites)
    (he : pc = base + BitVec.ofNat 32 off) : SiteAt base pc :=
  ⟨off, by simp [allSites, h], he⟩

/-- No site lies in the code offsets `[a, a + n)`. -/
theorem not_siteAt_range {base : Word} {a n j : Nat} (ha : a + n ≤ Artifacts.Release.size)
    (hr : ∀ off ∈ allSites, off < a ∨ a + n ≤ off)
    (hj : j < n) : ¬ SiteAt base (base + BitVec.ofNat 32 (a + j)) := by
  rintro ⟨off, hm, he⟩
  have h1 := hr off hm
  have h2 := allSites_lt off hm
  have hb := base.isLt
  have h4 := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h4
  have : Artifacts.Release.size < 2 ^ 32 := by decide
  omega

theorem not_siteAt {base : Word} {j : Nat} (h : j < tailOff) :
    ¬ SiteAt base (base + BitVec.ofNat 32 j) := by
  have := @not_siteAt_range base 0 tailOff j (by decide +kernel) (fun off hm => Or.inr (by simpa using allSites_ge off hm)) h
  simpa using this

end M0Crypto.Release.Blake2sCode
