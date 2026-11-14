import M0Crypto.Release.TraceSpec
import M0Crypto.Release.ChaCha20Frame
import M0Crypto.Release.ChaCha20Setup
import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.AeadPrologue
import M0Crypto.Release.AeadCrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.RunStates
import M0Crypto.Release.ChaCha20TraceSpecDefs
import M0Crypto.Release.ConstantTime.ChaCha20OutputAccess

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read sites of the AEAD functions

The AEAD routines load through a non-stack address at three kinds of instructions: the ChaCha
key, nonce and input loads, the message loads of the Poly1305 block loop, and the byte-copy and
tag-compare loops of the AEAD functions themselves. `rdSiteB` lists their offsets; `RdP` is the
step condition "a load at a read site reads only bytes of `Rd`, and only bytes of `Kn` inside the
ChaCha code". Every other load reads the stack window or the code, which the certificate bounds.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-! ### Naming the regions of `AeadEncryptReadRegion` / `AeadDecryptReadRegion`

The proofs pick a region by name, so reordering or extending the regions only touches these
constructors. -/

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.inp {c : ACall} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.inp + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inl (Region.mk h e)

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.aad {c : ACall} {y : Word} {o : Nat}
    (h : o < c.alen.toNat) (e : y = c.aad + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inl (Region.mk h e))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.key {c : ACall} {y : Word} {o : Nat}
    (h : o < 32) (e : y = c.key + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inl (Region.mk h e)))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.nonce {c : ACall} {y : Word} {o : Nat}
    (h : o < 12) (e : y = c.nonce + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.out {c : ACall} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.out + BitVec.ofNat 32 o) : TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e)))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.code {c : ACall} {y : Word} {o : Nat}
    (h : o < Artifacts.Release.size) (e : y = c.base + BitVec.ofNat 32 o) :
    TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e))))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.stack {c : ACall} {y : Word} {o : Nat}
    (h : o < TraceSpec.aeadStackBytes + 16)
    (e : y = c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 o) :
    TraceSpec.AeadEncryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Region.mk h e))))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadDecryptReadRegion.tag {c : ACall} {y : Word} {o : Nat}
    (h : o < 16) (e : y = c.tag + BitVec.ofNat 32 o) : TraceSpec.AeadDecryptReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e)))))

/-- The regions both AEAD functions may read: `in`, AAD, key, nonce, code and the stack window.
The phases the two functions share are proved against it. -/
def AeadCommonReadRegion (c : ACall) (y : Word) : Prop :=
  Region c.inp c.len.toNat y ∨ Region c.aad c.alen.toNat y ∨ Region c.key 32 y ∨
  Region c.nonce 12 y ∨ Region c.base Artifacts.Release.size y ∨
  Region (c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes) (TraceSpec.aeadStackBytes + 16) y

theorem AeadCommonReadRegion.inp {c : ACall} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.inp + BitVec.ofNat 32 o) : AeadCommonReadRegion c y :=
  Or.inl (Region.mk h e)

theorem AeadCommonReadRegion.aad {c : ACall} {y : Word} {o : Nat}
    (h : o < c.alen.toNat) (e : y = c.aad + BitVec.ofNat 32 o) : AeadCommonReadRegion c y :=
  Or.inr (Or.inl (Region.mk h e))

theorem AeadCommonReadRegion.key {c : ACall} {y : Word} {o : Nat}
    (h : o < 32) (e : y = c.key + BitVec.ofNat 32 o) : AeadCommonReadRegion c y :=
  Or.inr (Or.inr (Or.inl (Region.mk h e)))

theorem AeadCommonReadRegion.nonce {c : ACall} {y : Word} {o : Nat}
    (h : o < 12) (e : y = c.nonce + BitVec.ofNat 32 o) : AeadCommonReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e))))

theorem AeadCommonReadRegion.code {c : ACall} {y : Word} {o : Nat}
    (h : o < Artifacts.Release.size) (e : y = c.base + BitVec.ofNat 32 o) : AeadCommonReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e)))))

theorem AeadCommonReadRegion.stack {c : ACall} {y : Word} {o : Nat}
    (h : o < TraceSpec.aeadStackBytes + 16)
    (e : y = c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 o) :
    AeadCommonReadRegion c y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Region.mk h e)))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadEncryptReadRegion.common {c : ACall} {y : Word}
    (h : AeadCommonReadRegion c y) : TraceSpec.AeadEncryptReadRegion c y := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem _root_.M0Crypto.Release.TraceSpec.AeadDecryptReadRegion.common {c : ACall} {y : Word}
    (h : AeadCommonReadRegion c y) : TraceSpec.AeadDecryptReadRegion c y := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

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

/-- Offsets of every load instruction reachable from an AEAD function whose address the
certificate does not track: the ChaCha key, nonce and input loads, the Poly1305 message loads and
the AEAD's own loads. -/
def rdSiteB (off : Nat) : Bool :=
  decide (ChaCha20Policy.KNOff off) || ConstantTime.inputLoadOff off || polySiteB off || ownSiteB off

def SiteRd (base : Word) (pc : Word) : Prop := ∃ o, rdSiteB o = true ∧ pc = base + BitVec.ofNat 32 o

/-- The read policy: a load at a read site reads only bytes of `Rd`, and only bytes of `Kn` when
it lies in the ChaCha code. -/
def RdP (base : Word) (Rd Kn : Word → Prop) (_ : State) (e : Event) : Prop :=
  SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y ∧ (ChaCha20Policy.ChaPc base e.pc → Kn y)

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
  simp only [rdSiteB, Bool.or_eq_true, decide_eq_true_eq, ChaCha20Policy.KNOff] at hq
  have := ChaCha20Policy.site_order
  rcases hq with ((h | h) | h) | h
  · omega
  · exact (ConstantTime.inputLoadOff_bounds _ h).2.2
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
theorem rdP_of_free {base : Word} {Rd Kn Pn Wr : Word → Prop}
    (hn : ∀ pc, Pn pc → ¬ SiteRd base pc) (x : State) (e : Event)
    (h : RegionWrites Pn Wr x e) : RdP base Rd Kn x e :=
  fun hs => absurd hs (hn _ h.1)

/-- A read-free `ReachW` judgment is a `RdP` judgment. -/
theorem _root_.M0Crypto.Release.ReachW.toRd {base : Word} {Rd Kn Pn Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pn Wr s Q) (hn : ∀ pc, Pn pc → ¬ SiteRd base pc) :
    ReachS base (RdP base Rd Kn) s Q :=
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

/-- A fall-through block placed after the ChaCha code meets the read policy when its loads at read
sites read only bytes of `Rd`. -/
theorem blockOk_rdP {base : Word} {Rd Kn : Word → Prop} {is : List Instr} {u : State} {off : Nat}
    (hf : is.all Instr.falls = true) (hp : u.pc = base + BitVec.ofNat 32 off)
    (h1 : ChaCha20Policy.chaEnd ≤ off) (h2 : off + seqSize is ≤ 2 ^ 32)
    (h : ∀ e ∈ traceAll is u, SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y) :
    BlockOk (RdP base Rd Kn) is u := by
  have := (blockOk_events_iff (p := fun e => SiteRd base e.pc → ∀ y, Reads e.accesses y →
    Rd y ∧ (ChaCha20Policy.ChaPc base e.pc → Kn y)) is u).mpr ?_
  · exact this
  intro e he hs y hy
  refine ⟨h e he hs y hy, fun hc => ?_⟩
  obtain ⟨j, hj, hpc⟩ := traceAll_pc_offset is u hf e he
  obtain ⟨o, -, ho, e'⟩ := hc
  have hce : ChaCha20Policy.chaEnd < 2 ^ 32 := by decide +kernel
  have := pc_inj (a := off + j) (b := o) (by omega) (by omega)
    (by rw [← ofNat_add_assoc, ← hp, ← hpc, e'])
  omega

/-! ### The bytes that loads at read sites read

The caller buffers, and two stack ranges written before they are read: the ChaCha input copy at
`A + 8` (key derivation) followed by the Poly1305 block at `A + 72`. -/

/-- Bytes of the ChaCha input copy. -/
def copyLen : Nat := blkStackOff - inpStackOff

/-- Bytes of the input copy and the Poly1305 block. -/
def siteLen : Nat := blkStackOff + 16 - inpStackOff

/-- The caller buffers `in`, AAD, key and nonce, and the first `n` stack bytes from the input
copy. -/
def AeadSiteRegion (c : ACall) (n : Nat) (y : Word) : Prop :=
  Region c.inp c.len.toNat y ∨ Region c.aad c.alen.toNat y ∨ Region c.key 32 y ∨
  Region c.nonce 12 y ∨
  Region (c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 inpStackOff) n y

theorem AeadSiteRegion.inp {c : ACall} {n : Nat} {y : Word} {o : Nat}
    (h : o < c.len.toNat) (e : y = c.inp + BitVec.ofNat 32 o) : AeadSiteRegion c n y :=
  Or.inl (Region.mk h e)

theorem AeadSiteRegion.aad {c : ACall} {n : Nat} {y : Word} {o : Nat}
    (h : o < c.alen.toNat) (e : y = c.aad + BitVec.ofNat 32 o) : AeadSiteRegion c n y :=
  Or.inr (Or.inl (Region.mk h e))

theorem AeadSiteRegion.key {c : ACall} {n : Nat} {y : Word} {o : Nat}
    (h : o < 32) (e : y = c.key + BitVec.ofNat 32 o) : AeadSiteRegion c n y :=
  Or.inr (Or.inr (Or.inl (Region.mk h e)))

theorem AeadSiteRegion.nonce {c : ACall} {n : Nat} {y : Word} {o : Nat}
    (h : o < 12) (e : y = c.nonce + BitVec.ofNat 32 o) : AeadSiteRegion c n y :=
  Or.inr (Or.inr (Or.inr (Or.inl (Region.mk h e))))

/-- Byte `o` of the stack range from the input copy. -/
theorem AeadSiteRegion.stack {c : ACall} {n : Nat} {y : Word} {o : Nat} (h : o < n)
    (e : y = c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 (inpStackOff + o)) :
    AeadSiteRegion c n y :=
  Or.inr (Or.inr (Or.inr (Or.inr (Region.mk h (by rw [e, ofNat_add_assoc])))))

/-- The entry-relative stack range a load site at `off` may read: the input copy inside the ChaCha
code, the input copy and the Poly1305 block elsewhere. The hole-map check proves these bytes
written at every load site. -/
def siteRange (off : Nat) : Option (Int × Int) :=
  some ((inpStackOff : Int) - TraceSpec.aeadStackBytes,
    ((inpStackOff + if off < ChaCha20Policy.chaEnd then copyLen else siteLen : Nat) : Int) -
      TraceSpec.aeadStackBytes)

theorem AeadSiteRegion.common {c : ACall} {n : Nat} {y : Word} (hn : n ≤ siteLen)
    (h : AeadSiteRegion c n y) : AeadCommonReadRegion c y := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨o, ho, rfl⟩ := Region.exists h
    refine .stack (o := inpStackOff + o) ?_ (ofNat_add_assoc _ _ _)
    simp only [siteLen, blkStackOff, inpStackOff, aeadFrame, TraceSpec.aeadStackBytes] at hn ⊢
    omega

end M0Crypto.Release.Aead
