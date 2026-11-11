import M0Crypto.Thumb.Decode
import M0Crypto.Thumb.Seq

/-!
Shared helpers for derived code layout. A release function starts at its symbol in
`Artifacts.Release`; each later piece starts where the previous one ends, so offsets are
sums of `seqSize` (list pieces) and `brSize` (short branches). Branch immediates are
computed from the same offsets by `brImm8` / `brImm11` / `blImm`, so moving a piece moves the
branches that reach it. Each module's layout section uses these helpers; nothing here
depends on any particular artifact.
-/

namespace M0Crypto.Release

open M0Crypto.Thumb

/-- Size of a 16-bit Thumb branch (`B` or `B<cond>`). -/
def brSize : Nat := (Instr.b 0).size

theorem brSize_eq : brSize = 2 := by decide

/-- Size of a `bl` call (32-bit). -/
def blSize : Nat := (Instr.bl 0).size

theorem blSize_eq : blSize = 4 := by decide

/-- Halfword displacement of a branch at `off` to `tgt`: `(tgt - (off + 4)) / 2`. -/
def brDisp (off tgt : Nat) : Int := ((tgt : Int) - ((off : Int) + 4)) / 2

/-- The `imm8` field of a conditional branch at `off` reaching `tgt`. -/
def brImm8 (off tgt : Nat) : BitVec 8 := BitVec.ofInt 8 (brDisp off tgt)

/-- A branch at `m + a` back to `m` has the `imm8` of a branch at `a` back to `0`: the
displacement depends only on the distance from branch to target. -/
theorem brImm8_base (m a : Nat) : brImm8 (m + a) m = brImm8 a 0 := by
  unfold brImm8 brDisp; congr 1; omega

/-- A branch at `m + a` to `m + b` has the `imm8` of a branch at `a` to `b`: the displacement
depends only on the distance from branch to target. -/
theorem brImm8_shift (m a b : Nat) : brImm8 (m + a) (m + b) = brImm8 a b := by
  unfold brImm8 brDisp; congr 1; omega

/-- The `imm11` field of an unconditional branch at `off` reaching `tgt`. -/
def brImm11 (off tgt : Nat) : BitVec 11 := BitVec.ofInt 11 (brDisp off tgt)

/-- The `imm25` field of a `bl` at `off` reaching `tgt`: the byte displacement
`tgt - (off + 4)` in 25-bit two's complement, the form `blTarget` reads back. -/
def blImm (off tgt : Nat) : BitVec 25 := BitVec.ofInt 25 ((tgt : Int) - ((off : Int) + 4))

/-- Size of a literal-pool load `ldr Rd, [pc, #imm]`; the immediate does not change it. -/
def litSize : Nat := seqSize [.ldrLit 4 0]

/-- Immediate of a literal-pool load at `off` reading the word at `pool`: the word distance
from the word-aligned PC `(off + 4) / 4 * 4`. -/
def litImm (off pool : Nat) : Nat := (pool - (off + 4) / 4 * 4) / 4

/-- The literal load at `off` reads `pool`, when `pool` is a word address above the PC. -/
theorem litImm_target (off pool : Nat) (hp : pool % 4 = 0) (hle : (off + 4) / 4 * 4 ≤ pool) :
    (off + 4) / 4 * 4 + litImm off pool * 4 = pool := by
  unfold litImm; omega

/-! Poly1305 blocks frame (`Poly1305BlocksCode` uses it). It is defined here, below `Poly1305Mac`, so
that `Poly1305Mac`'s column-end lemma can state its frame bound by name without an import cycle. -/
namespace Poly1305Blocks

/-- Frame size in words. The ChaCha save area starts `frameBytes` above `fp`. -/
def frameWords : Nat := 7

/-- Frame size in bytes: `frameWords` words. -/
def frameBytes : Nat := 4 * frameWords

end Poly1305Blocks

end M0Crypto.Release
