import M0Crypto.Release.X25519Sites
import M0Crypto.Release.X25519PrologueWords

/-!
The event condition of a whole `m0c_x25519` run.

`Ev c`: every event is at a PC of the artifact, writes only `X25519.WrOk c`, reads only the
inputs at a load site (`X25519Code.loadSites`) and writes only `out` at a store site
(`X25519Code.storeSites`). The run is proved in three bands, each with its own PC region:

* prologue `[x25519, oLadder)`, with every read in the inputs (`liftPro`);
* middle: the field routines below `x25519` and `[oLadder, oStore)` (`MidPc`, `liftMid`);
* tail: the output stores `[oStore, oWipe)` writing `out` (`liftS`), then wipe and epilogue
  `[oWipe, size)` writing the stack window (`liftW`).

The load sites lie in the prologue band and the store sites in the store band
(`loadSites_in`, `storeSites_in`, checked on the decoded entry), so a band that excludes a
site list says nothing about it (`not_site`).
-/

namespace M0Crypto.Release.X25519Ev
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release (Region RegionWrites InRegion)
open M0Crypto.Release.X25519Code (AtSite loadSites storeSites)
open M0Crypto.Release.X25519EntryCode (oLadder oStore oWipe)
open M0Crypto.Release.X25519Prologue (InpR)
open M0Crypto.Release.X25519Block (RegionRW)

/-- The event condition of a run. -/
def Ev (c : X25519.Ctx) (_ : State) (e : Event) : Prop :=
  Region c.base Artifacts.Release.size e.pc ∧ (∀ y, Writes e.accesses y → X25519.WrOk c y) ∧
    (AtSite loadSites c.base e.pc → ∀ y, Reads e.accesses y → InpR c y) ∧
    (AtSite storeSites c.base e.pc → ∀ y, Writes e.accesses y → Region c.out 32 y)

/-! ## Bands and sites -/

theorem bands : Artifacts.Release.x25519 ≤ oLadder ∧ oLadder ≤ oStore ∧ oStore ≤ oWipe ∧
    oWipe ≤ Artifacts.Release.size ∧ Artifacts.Release.size < 2 ^ 32 := by
  decide +kernel

theorem loadSites_in : ∀ o ∈ loadSites, Artifacts.Release.x25519 ≤ o ∧ o < oLadder := by
  decide +kernel

theorem storeSites_in : ∀ o ∈ storeSites, oStore ≤ o ∧ o < oWipe := by
  decide +kernel

/-- A PC in the band `[F, F + S)` of the code is at no site outside the band. -/
theorem not_site {sites : List Nat} {base pc : Word} {F S : Nat}
    (hs : ∀ o ∈ sites, o < Artifacts.Release.size ∧ (o < F ∨ F + S ≤ o))
    (hFS : F + S ≤ Artifacts.Release.size) (hpc : Region (base + BitVec.ofNat 32 F) S pc) :
    ¬ AtSite sites base pc := by
  rintro ⟨o, ho, rfl⟩
  obtain ⟨h1, h2⟩ := hs o ho
  have := bands.2.2.2.2
  simp only [Region] at hpc
  bv_omega

/-- A band of the code is in the code. -/
theorem band_code {base pc : Word} {F S : Nat} (hFS : F + S ≤ Artifacts.Release.size)
    (hpc : Region (base + BitVec.ofNat 32 F) S pc) : Region base Artifacts.Release.size pc := by
  have := bands.2.2.2.2
  simp only [Region] at hpc ⊢
  bv_omega

theorem band0 {base pc : Word} {S : Nat} (h : Region base S pc) :
    Region (base + BitVec.ofNat 32 0) S pc := by
  simpa using h

/-! ## The three bands -/

/-- PCs of the prologue. -/
abbrev ProPc (c : X25519.Ctx) : Word → Prop :=
  Region (c.base + BitVec.ofNat 32 Artifacts.Release.x25519) (oLadder - Artifacts.Release.x25519)

/-- PCs of the middle: the field routines and the entry from the ladder to the stores. -/
def MidPc (c : X25519.Ctx) (y : Word) : Prop :=
  Region c.base Artifacts.Release.x25519 y ∨ Region (c.base + BitVec.ofNat 32 oLadder) (oStore - oLadder) y

theorem proPc (c : X25519.Ctx) : ∀ o n, Artifacts.Release.x25519 ≤ o → o + n ≤ oLadder →
    InRegion (ProPc c) c.base o n := fun _ _ h1 h2 => by
  have := bands
  exact X25519MulcFacts.inReg ⟨h1, by omega, by omega⟩

theorem midPcOk (c : X25519.Ctx) : X25519Op.PcOk c.base oLadder oStore (MidPc c) := by
  have := bands
  exact ⟨fun _ h => Or.inl h, fun j hj => Or.inr (X25519MulcFacts.inReg ⟨Nat.le_refl _, by omega, by omega⟩ j hj),
    this.1, by omega⟩

theorem liftPro {c : X25519.Ctx} {z : State} {e : Event}
    (h : RegionRW (ProPc c) (X25519.WrOk c) (InpR c) z e) : Ev c z e := by
  have := bands
  refine ⟨band_code (by omega) h.1, h.2.1, fun _ => h.2.2, fun hs => absurd hs (not_site ?_ (by omega) h.1)⟩
  intro o ho; have := storeSites_in o ho; omega

theorem liftMid {c : X25519.Ctx} {z : State} {e : Event}
    (h : RegionWrites (MidPc c) (X25519.WrOk c) z e) : Ev c z e := by
  have := bands
  have hl : ∀ o ∈ loadSites, o < Artifacts.Release.size ∧ (o < oLadder ∨ oLadder + (oStore - oLadder) ≤ o) ∧
      (o < 0 ∨ 0 + Artifacts.Release.x25519 ≤ o) := fun o ho => by
    have := loadSites_in o ho; omega
  have hs : ∀ o ∈ storeSites, o < Artifacts.Release.size ∧ (o < oLadder ∨ oLadder + (oStore - oLadder) ≤ o) ∧
      (o < 0 ∨ 0 + Artifacts.Release.x25519 ≤ o) := fun o ho => by
    have := storeSites_in o ho; omega
  refine ⟨?_, h.2, fun hx => absurd hx ?_, fun hx => absurd hx ?_⟩
  · rcases h.1 with h1 | h1
    · exact band_code (F := 0) (by omega) (band0 h1)
    · exact band_code (by omega) h1
  · rcases h.1 with h1 | h1
    · exact not_site (fun o ho => ⟨(hl o ho).1, (hl o ho).2.2⟩) (by omega) (band0 h1)
    · exact not_site (fun o ho => ⟨(hl o ho).1, (hl o ho).2.1⟩) (by omega) h1
  · rcases h.1 with h1 | h1
    · exact not_site (fun o ho => ⟨(hs o ho).1, (hs o ho).2.2⟩) (by omega) (band0 h1)
    · exact not_site (fun o ho => ⟨(hs o ho).1, (hs o ho).2.1⟩) (by omega) h1

theorem liftS {c : X25519.Ctx} {z : State} {e : Event}
    (h : RegionWrites (Region (c.base + BitVec.ofNat 32 oStore) (oWipe - oStore)) (Region c.out 32) z e) :
    Ev c z e := by
  have := bands
  refine ⟨band_code (by omega) h.1, fun y hy => Or.inr (h.2 y hy),
    fun hx => absurd hx (not_site ?_ (by omega) h.1), fun _ => h.2⟩
  intro o ho; have := loadSites_in o ho; omega

theorem liftW {c : X25519.Ctx} {z : State} {e : Event}
    (h : RegionWrites (Region (c.base + BitVec.ofNat 32 oWipe) (Artifacts.Release.size - oWipe))
      (Region c.fp X25519.stackBytes) z e) : Ev c z e := by
  have := bands
  refine ⟨band_code (by omega) h.1, fun y hy => Or.inl (h.2 y hy),
    fun hx => absurd hx (not_site ?_ (by omega) h.1), fun hx => absurd hx (not_site ?_ (by omega) h.1)⟩
  · intro o ho; have := loadSites_in o ho; omega
  · intro o ho; have := storeSites_in o ho; omega

end M0Crypto.Release.X25519Ev
