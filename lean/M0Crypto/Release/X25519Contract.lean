import M0Crypto.Release.ChaCha20Contract
import M0Crypto.Spec.X25519

/-!
# Contract of `m0c_x25519`

Statement file: definitions only, no proofs (see `Contract.lean`). In reading order: the stack
sizes, the call (`Ctx`), its preconditions (`Valid`), the entry state (`Entry`), the two
bundled as the hypothesis of every top-level theorem (`Pre`), and what a returned call
guarantees (`Result`, `WrOk`). Compare with `include/m0crypto/x25519.h` and with
`docs/design/x25519-freeze.md` (dev repository) section 4.

C prototype: `int m0c_x25519(uint8_t out[32], const uint8_t scalar[32],
const uint8_t point[32])`, always returning `M0C_OK` (0).

Stack, from the entry SP `sp0` down: 36 bytes of saved registers (`r4`-`r11`, `lr`), the
entry's 332-byte frame, and 148 bytes used by a callee: 516 bytes in all. Before returning, the
entry zeroes the 480 bytes below the saved registers.

The buffers may be unaligned and may overlap each other in any way: the entry reads all of
`scalar` and `point` before it writes `out`. `out` must not overlap the code; no buffer may
overlap the stack window.
-/

namespace M0Crypto.Release.X25519

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)

/-! ## Sizes -/

/-- Stack bytes of the call below the entry SP. -/
def stackBytes : Nat := 516

/-- Bytes the entry zeroes before returning: from `sp0 - stackBytes` up to the saved
registers. -/
def wipeBytes : Nat := 480

/-! ## The call -/

structure Ctx where
  /-- Address of the release artifact's first byte. -/
  base : Word
  /-- SP at entry. -/
  sp0 : Word
  out : Word
  scalar : Word
  point : Word
  /-- Memory at entry. -/
  m0 : Mem
  /-- Registers at entry. -/
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Lowest stack address the call uses. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 stackBytes

def scalarB : List Spec.X25519.Byte := Frame.Ctx.bytesAt c.m0 c.scalar 32
def pointB : List Spec.X25519.Byte := Frame.Ctx.bytesAt c.m0 c.point 32

/-- Expected output byte `i`: RFC 7748 `X25519(scalar, point)`. -/
def outB (i : Nat) : Spec.X25519.Byte := (Spec.X25519.x25519 c.scalarB c.pointB)[i]!

/-- Output index of address `y`. -/
def oidx (y : Word) : Nat := (y - c.out).toNat

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32

end Ctx

/-! ## Preconditions -/

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  /-- the stack window does not wrap -/
  spLo : stackBytes ≤ c.sp0.toNat
  /-- code vs. stack window -/
  codeS : Disj c.base Artifacts.Release.size c.fp stackBytes
  /-- code vs. output -/
  codeO : Disj c.base Artifacts.Release.size c.out 32
  /-- output vs. stack window -/
  outS : Disj c.out 32 c.fp stackBytes
  /-- scalar vs. stack window -/
  scalarS : Disj c.scalar 32 c.fp stackBytes
  /-- point vs. stack window -/
  pointS : Disj c.point 32 c.fp stackBytes
  /-- the artifact is in memory at `base` -/
  code : Thumb.CodeAt c.m0 c.base B

/-! ## Entry state -/

/-- Entry state of a call described by `c` (AAPCS: r0-r2 = out, scalar, point). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 Artifacts.Release.x25519
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.out
  r1 : c.regs0 1 = c.scalar
  r2 : c.regs0 2 = c.point

/-! ## Hypothesis of the top-level theorems -/

/-- A valid call of `m0c_x25519` entered in state `s`. The correctness, trace, read and stack
theorems assume exactly this. -/
structure Pre (c : Ctx) (s : State) : Prop where
  valid : Valid c
  entry : Entry c s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-! ## Postconditions -/

/-- The final state of a call. -/
structure Result (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.ret
  sp : t.regs 13 = c.sp0
  /-- r4-r11 restored. -/
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  /-- r0 = `M0C_OK`; r1-r3 and r12 cleared. -/
  r0 : t.regs 0 = 0
  r1 : t.regs 1 = 0
  r2 : t.regs 2 = 0
  r3 : t.regs 3 = 0
  r12 : t.regs 12 = 0
  /-- Outside the stack window: `out` holds the RFC 7748 result, all else is unchanged. -/
  mem : ∀ y, ¬ Region c.fp stackBytes y →
    t.mem y = if Region c.out 32 y then c.outB (c.oidx y) else c.m0 y
  /-- The stack the call used, below the saved registers, is zero. -/
  wipe : ∀ y, Region c.fp wipeBytes y → t.mem y = 0

/-- Writes allowed to a call: its stack window and `out`. -/
def WrOk (c : Ctx) (y : Word) : Prop :=
  Region c.fp stackBytes y ∨ Region c.out 32 y

/-! ## Functional statement (claims X1-X3) -/

/-- Every valid call returns, with `Result` and only allowed writes. -/
def Correct : Prop :=
  ∀ c s, Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      Result c t ∧ WritesTo (WrOk c) tr

end M0Crypto.Release.X25519
