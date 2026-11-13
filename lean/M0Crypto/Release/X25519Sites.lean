import M0Crypto.Thumb.SeqScan
import M0Crypto.Artifacts.Release
import M0Crypto.Release.Contract

/-!
# Pointer-access sites of `m0c_x25519`

The constant-time certificate of `m0c_x25519` tracks every stack access. Its only other
accesses are the byte loads that decode `scalar` and `point` and the byte stores that encode
`out` (plan `x25519-proofs.md`, R3). This file names them by what they are, the `ldrb` and
`strb` instructions of the entry, not by offset, so a change of the code moves the lists with
it.

`entryCode` decodes the entry from its symbol to the end of the artifact (the entry is the last
function of the release unit). `x25519_code_decodes` checks that this walk covers the entry
exactly and finds no undecodable halfword.

The two site statements (`LoadSiteOk`, `StoreSiteOk`) say what a run must do at these pcs:
read only from `scalar` and `point`, write only to `out`. They are definitions here. Phase 10 of
the plan proves them for every event of a run from a valid entry state, using the generic
region lemmas (`EntryReads.certificate_run_reads`, `RegionStores.bufferStoreOk_of_region`).
-/

namespace M0Crypto.Release.X25519Code

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Artifacts

/-- Decode `n` instructions of an artifact cut at its first one, with their offsets from
`off`. Stops at the end of the bytes; `none` if a halfword does not decode or an instruction
runs past the end. -/
def scanFrom : Nat → Nat → List (BitVec 8) → Option (List (Nat × Instr))
  | 0, _, bs => if bs.isEmpty then some [] else none
  | fuel + 1, off, bs =>
    if bs.isEmpty then some [] else
    match instrScan bs with
    | none => none
    | some i =>
      if i.size ≤ bs.length then (scanFrom fuel (off + i.size) (bs.drop i.size)).map ((off, i) :: ·)
      else none

/-- Every instruction of the entry with its offset: from the symbol to the end of the artifact.
The fuel is one step per halfword, enough for any instruction mix. -/
def entryCode : List (Nat × Instr) :=
  (scanFrom ((Release.size - Release.x25519) / 2 + 1) Release.x25519
    (Release.bytes.drop Release.x25519)).getD []

/-- Offsets of the entry's byte loads: the decode of `scalar` and `point`. -/
def loadSites : List Nat :=
  entryCode.filterMap fun (off, i) => match i with
    | .memImm .ldrb .. => some off
    | _ => none

/-- Offsets of the entry's byte stores: the encode of `out`. -/
def storeSites : List Nat :=
  entryCode.filterMap fun (off, i) => match i with
    | .memImm .strb .. => some off
    | _ => none

/-- The walk decodes the whole entry. -/
theorem x25519_code_decodes :
    (scanFrom ((Release.size - Release.x25519) / 2 + 1) Release.x25519
      (Release.bytes.drop Release.x25519)).isSome = true := by
  decide +kernel

/-- One load per byte of `scalar` and `point`, one store per byte of `out`. -/
theorem sites_length : loadSites.length = 2 * 32 ∧ storeSites.length = 32 := by
  decide +kernel

theorem loadSites_lt : ∀ off ∈ loadSites, off < Release.size := by decide +kernel

theorem storeSites_lt : ∀ off ∈ storeSites, off < Release.size := by decide +kernel

/-! ## Site statements (proved in phase 10) -/

/-- The run is at a listed site. -/
def AtSite (sites : List Nat) (base pc : Word) : Prop :=
  ∃ off ∈ sites, pc = base + BitVec.ofNat 32 off

/-- At a load site, an event reads only `scalar` (`r1` at entry) and `point` (`r2`). -/
def LoadSiteOk (base : Word) (s : State) (e : Event) : Prop :=
  AtSite loadSites base e.pc →
    ∀ y, Reads e.accesses y → Region (s.regs 1) 32 y ∨ Region (s.regs 2) 32 y

/-- At a store site, an event writes only `out` (`r0` at entry). -/
def StoreSiteOk (base : Word) (s : State) (e : Event) : Prop :=
  AtSite storeSites base e.pc → ∀ y, Writes e.accesses y → Region (s.regs 0) 32 y

end M0Crypto.Release.X25519Code
