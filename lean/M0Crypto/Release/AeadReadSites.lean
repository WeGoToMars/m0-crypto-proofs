import M0Crypto.Release.TraceSpec

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read sites of the AEAD functions

The AEAD routines load from caller memory through a non-stack address at three kinds of
instructions: the ChaCha input/key/nonce loads, the message loads of the Poly1305 block loop, and
the byte-copy and tag-compare loops of the AEAD functions themselves. `rdSiteB` lists their
offsets; `RdP` is the step condition "a load at a read site reads only bytes of `Rd`". Every
other load reads the stack window or the code, which the certificate bounds.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-! ### Naming the regions of `AeadEncryptReadRegion` / `AeadDecryptReadRegion`

The proofs pick a region by name, so reordering or extending the regions only touches these
constructors. -/

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.inp {c : ACall} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.inp + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inl ⟨o, h, e⟩

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.aad {c : ACall} {y : Word} {o : Nat}
    (h : o < c.alen.toNat) (e : y = c.aad + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inl ⟨o, h, e⟩)

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.key {c : ACall} {y : Word} {o : Nat}
    (h : o < 32) (e : y = c.key + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inl ⟨o, h, e⟩))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.nonce {c : ACall} {y : Word} {o : Nat}
    (h : o < 12) (e : y = c.nonce + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨o, h, e⟩)))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.out {c : ACall} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.out + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, h, e⟩))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.code {c : ACall} {y : Word} {o : Nat}
    (h : o < Artifacts.Release.size) (e : y = c.base + BitVec.ofNat 32 o) :
    TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, h, e⟩)))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.stack {c : ACall} {y : Word} {o : Nat}
    (h : o < TraceSpec.aeadStackBytes + 16)
    (e : y = c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 o) :
    TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨o, h, e⟩)))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadDecryptReadRegion.enc {c : ACall} {y : Word}
    (h : TraceSpec.AeadEncryptReadRegion c y) : TraceSpec.AeadDecryptReadRegion c y := Or.inl h

theorem _root_.M0Crypto.Release.TraceSpec.AeadDecryptReadRegion.tag {c : ACall} {y : Word} {o : Nat}
    (h : o < 16) (e : y = c.tag + BitVec.ofNat 32 o) : TraceSpec.AeadDecryptReadRegion c y :=
  Or.inr ⟨o, h, e⟩

/-- Stack offset, from `sp0 - aeadStackBytes`, of the 16-byte Poly1305 block at `A + 72`. -/
def blkStackOff : Nat := TraceSpec.aeadStackBytes - aeadFrame + 72

/-- Stack offset of the ChaCha input copy at `A + 8`. -/
def inpStackOff : Nat := TraceSpec.aeadStackBytes - aeadFrame + 8

/-- Instructions that load through an address register (`ldm`, `ldr*` with a register base). -/
def isLoadInstr : Instr → Bool
  | .memImm op _ _ _ => op.isLoad
  | .memReg op _ _ _ => op.isLoad
  | .ldm _ _ => true
  | _ => false

/-- Offsets of the load instructions of a sequence placed at `start`. -/
def loadOffsets (start : Nat) : List Instr → List Nat
  | [] => []
  | i :: is => (if isLoadInstr i then [start] else []) ++ loadOffsets (start + i.size) is

/-- Offsets of the message loads of `m0c_poly1305_blocks`: the aligned `ldm` and the unaligned
byte-load sequence. -/
def polySiteB (off : Nat) : Bool :=
  (loadOffsets Poly1305Blocks.loadAAt Poly1305Blocks.loadA ++
    loadOffsets Poly1305Blocks.loadUAt Poly1305Blocks.loadU).contains off

/-- Offsets of the loads of the AEAD functions that read caller memory: the tail-copy load of
each `MAC_PADDED` loop and the tag-compare load. -/
def ownSiteB (off : Nat) : Bool :=
  [encMac0At + macLOff, encMac1At + macLOff, decMac0At + macLOff, decMac1At + macLOff,
    decCmpLAt].contains off

/-- Offsets of every caller-memory load instruction reachable from an AEAD function. -/
def rdSiteB (off : Nat) : Bool := decide (ChaCha20Policy.SiteOff off) || polySiteB off || ownSiteB off

def SiteRd (base : Word) (pc : Word) : Prop := ∃ o, rdSiteB o = true ∧ pc = base + BitVec.ofNat 32 o

/-- The read policy: a load at a read site reads only bytes of `Rd`. -/
def RdP (base : Word) (Rd : Word → Prop) (_ : State) (e : Event) : Prop :=
  SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y

theorem pc_inj {base : Word} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : base + BitVec.ofNat 32 a = base + BitVec.ofNat 32 b) : a = b :=
  ChaCha20Policy.pc_off_inj ha hb h

/-- The first read site in `[off, off + n)`. Region checks state `firstReadSite off n = none`, so
a failing `decide +kernel` can be diagnosed with `#eval firstReadSite off n`. -/
def firstReadSite (off n : Nat) : Option Nat :=
  ((List.range n).map (off + ·)).find? rdSiteB

theorem no_readSite {off n : Nat} (h : firstReadSite off n = none) :
    ∀ j < n, rdSiteB (off + j) = false := by
  intro j hj
  have := List.find?_eq_none.mp h (off + j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simpa using this

theorem polySiteB_lt (q : Nat) (h : polySiteB q = true) : q < 2 ^ 32 := by
  have key : ∀ x ∈ loadOffsets Poly1305Blocks.loadAAt Poly1305Blocks.loadA ++
      loadOffsets Poly1305Blocks.loadUAt Poly1305Blocks.loadU, x < 2 ^ 32 := by decide +kernel
  exact key q (List.contains_iff_mem.mp h)

theorem ownSiteB_lt (q : Nat) (h : ownSiteB q = true) : q < 2 ^ 32 := by
  have key : ∀ x ∈ [encMac0At + macLOff, encMac1At + macLOff, decMac0At + macLOff,
      decMac1At + macLOff, decCmpLAt], x < 2 ^ 32 := by decide +kernel
  exact key q (List.contains_iff_mem.mp h)

theorem rdSiteB_lt {q : Nat} (hq : rdSiteB q = true) : q < 2 ^ 32 := by
  simp only [rdSiteB, Bool.or_eq_true, decide_eq_true_eq, ChaCha20Policy.SiteOff] at hq
  have := ChaCha20Policy.site_order
  rcases hq with (h | h) | h
  · omega
  · exact polySiteB_lt _ h
  · exact ownSiteB_lt _ h

theorem not_siteRd {base : Word} {o : Nat} (ho : o < 2 ^ 32) (h : rdSiteB o = false) :
    ¬ SiteRd base (base + BitVec.ofNat 32 o) := by
  rintro ⟨q, hq, e⟩
  have hq32 : q < 2 ^ 32 := rdSiteB_lt hq
  have := pc_inj ho hq32 e
  subst this
  rw [h] at hq
  cases hq

/-- A region with no read site satisfies the read policy. -/
theorem rdP_of_free {base : Word} {Rd Pn Wr : Word → Prop}
    (hn : ∀ pc, Pn pc → ¬ SiteRd base pc) (x : State) (e : Event)
    (h : RegionWrites Pn Wr x e) : RdP base Rd x e :=
  fun hs => absurd hs (hn _ h.1)

/-- A read-free `ReachW` judgment is a `RdP` judgment. -/
theorem _root_.M0Crypto.Release.ReachW.toRd {base : Word} {Rd Pn Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pn Wr s Q) (hn : ∀ pc, Pn pc → ¬ SiteRd base pc) :
    ReachS base (RdP base Rd) s Q :=
  h.mono (fun x e hh => rdP_of_free hn x e hh) (fun _ h => h)

/-- Program counters of a code interval that holds no read site. -/
def NoSite (base : Word) (pc : Word) : Prop := ¬ SiteRd base pc

theorem inRegion_noSite {base : Word} {Pc : Word → Prop} {lo hi off n : Nat}
    (hP : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween base lo hi pc → Pc pc) (h1 : lo ≤ off) (h2 : off + n ≤ hi)
    (hh : hi ≤ 2 ^ 32) (hs : ∀ j < n, rdSiteB (off + j) = false) :
    InRegion (fun pc => Pc pc ∧ NoSite base pc) base off n :=
  fun j hj => ⟨hP _ ⟨off + j, by omega, by omega, rfl⟩, not_siteRd (by omega) (hs j hj)⟩

theorem pc_noSite {base : Word} {Pc : Word → Prop} {lo hi off : Nat}
    (hP : ∀ pc, M0Crypto.Release.ConstantTime.PCBetween base lo hi pc → Pc pc) (h1 : lo ≤ off) (h2 : off < hi)
    (hh : hi ≤ 2 ^ 32) (hs : rdSiteB off = false) :
    (fun pc => Pc pc ∧ NoSite base pc) (base + BitVec.ofNat 32 off) :=
  ⟨hP _ ⟨off, h1, h2, rfl⟩, not_siteRd (by omega) hs⟩

end M0Crypto.Release.Aead
