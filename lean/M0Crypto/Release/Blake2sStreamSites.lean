import M0Crypto.Release.Blake2sStreamCode

/-!
# Untracked store sites of the BLAKE2s streaming entries

The constant-time certificates track `sp`-relative stores. Every other store (a store through a
context or buffer pointer) must lie at a listed code offset, where the proofs bound the written
bytes by the buffer the store targets. The lists are derived from the instruction lists and
checked against the generated certificates (`certSites`).
-/

namespace M0Crypto.Release.Blake2sStreamCode

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode (B)

/-- Code offset of instruction `k` of the list `is` placed at `start`. -/
def siteOf (start : Nat) (is : List Instr) (k : Nat) : Nat := start + seqSize (is.take k)

/-- `init`: the three `stm r0!` and the two `str` through `r0`. -/
def initSites : List Nat := [4, 8, 12, 13, 14].map (siteOf iStart iA)


/-- A store site is a nonempty `stm` or a memory store through an immediate offset. -/
def isStoreSite : Option Instr → Bool
  | some (.stm _ l) => decide (0 < bitCount l)
  | some (.memImm op _ _ _) => !op.isLoad
  | _ => false

theorem initSites_store : initSites.all (fun off => isStoreSite (instrAt B off)) = true := by
  decide +kernel

theorem initSites_ge : ∀ off ∈ initSites, iStart + 2 ≤ off := by decide +kernel
theorem initSites_lt : ∀ off ∈ initSites, off < Artifacts.Release.size := by decide +kernel

/-! ## `copy` -/

open M0Crypto.Release.Blake2sCopyCode in
/-- `copy`: the byte store of the alignment loop, the `stm` and `str` of the word loops, the two
`stm`s of the packing loops and the byte store of the tail. -/
def copySites : List Nat :=
  [siteOf oAlBody byteB 1, siteOf oW16Body w16B 1, siteOf oW4Body w4B 1, siteOf oPB pbB 8,
   siteOf oPH phB 4, siteOf oBL byteB 1]


theorem copySites_store : copySites.all (fun off => isStoreSite (instrAt B off)) = true := by
  decide +kernel

theorem copySites_ge : ∀ off ∈ copySites, Blake2sCopyCode.oTst ≤ off := by decide +kernel
theorem copySites_lt : ∀ off ∈ copySites, off < Artifacts.Release.size := by decide +kernel

/-! ## `update` -/

/-- `update`: the two count stores of each `NONFINAL_BLOCK` (the flush and the direct block), the
byte store of the tail loop and the store of `used`. The compress and `copy` stores it reaches
are listed with those functions. -/
def updateSites : List Nat :=
  [siteOf oFlush flushPre 7, siteOf oFlush flushPre 8, siteOf oDirect dirPre 6,
   siteOf oDirect dirPre 7, siteOf oBytesL byteLoop 1, siteOf oOut storeUsed 0]


theorem updateSites_store : updateSites.all (fun off => isStoreSite (instrAt B off)) = true := by
  decide +kernel

theorem updateSites_ge : ∀ off ∈ updateSites, uStart ≤ off := by decide +kernel
theorem updateSites_lt : ∀ off ∈ updateSites, off < Artifacts.Release.size := by decide +kernel

/-! ## `final` -/

/-- `final`: the padding byte and word stores into `buf`, and the `stm`s and byte store that
write `out`. -/
def finalSites : List Nat :=
  [siteOf oPadBBody padB 0, siteOf oPadWBody padW 0, siteOf oOutW outW 1, siteOf oOutW outW 3,
   siteOf oOutB outB 1]


/-- `isStoreSite`, also accepting a store through a register offset. -/
def isStoreSiteR : Option Instr → Bool
  | some (.memReg op _ _ _) => !op.isLoad
  | i => isStoreSite i

theorem finalSites_store : finalSites.all (fun off => isStoreSiteR (instrAt B off)) = true := by
  decide +kernel

theorem finalSites_ge : ∀ off ∈ finalSites, fStart ≤ off := by decide +kernel
theorem finalSites_lt : ∀ off ∈ finalSites, off < Artifacts.Release.size := by decide +kernel

end M0Crypto.Release.Blake2sStreamCode
