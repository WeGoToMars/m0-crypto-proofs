import M0Crypto.Release.Contract
import M0Crypto.Spec.Aead

/-!
# Contract of `m0c_chacha20_xor`

Statement file: definitions only, no proofs (see `Contract.lean`). In reading order: the stack
sizes, the call (`Ctx`), its preconditions (`Valid`), the entry state (`Entry`), the two
bundled as the hypothesis of every top-level theorem (`Pre`), and what a returned call
guarantees (`Result`, `WrOk`). Compare with `include/m0crypto/chacha20.h`.
-/

namespace M0Crypto.Release.ChaCha20Layout

/-- Words of the frame (`FRAME`). -/
def chFrameWords : Nat := 35
/-- Words of the frame plus saved registers: the stack words of the call. -/
def chStackWords : Nat := 44
/-- Stack bytes of the call: `sp0 - fp`, that is `FRAME` plus `SAVED`. -/
def chStackBytes : Nat := 4 * chStackWords

end M0Crypto.Release.ChaCha20Layout

namespace M0Crypto.Release.Frame

open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (Byte)
open M0Crypto.Spec.Aead (chacha20)
open M0Crypto.Release.ChaCha20Layout (chStackBytes chFrameWords)

/-! ## The call -/

structure Ctx where
  base : Word
  sp0 : Word
  out : Word
  inp : Word
  len : Word
  key : Word
  nonce : Word
  ctr : Word
  m0 : Mem
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Frame pointer after the prologue. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 chStackBytes

/-- `n` bytes of `m` from `a`. -/
def bytesAt (m : Mem) : Word → Nat → List Byte
  | _, 0 => []
  | a, n + 1 => m a :: bytesAt m (a + 1#32) n

def keyB : List Byte := bytesAt c.m0 c.key 32
def nonceB : List Byte := bytesAt c.m0 c.nonce 12
def msg : List Byte := bytesAt c.m0 c.inp c.len.toNat

/-- Expected output byte `i`. -/
def outB (i : Nat) : Byte := (chacha20 c.keyB c.ctr.toNat c.nonceB c.msg)[i]!

/-- Output index of address `y`. -/
def oidx (y : Word) : Nat := (y - c.out).toNat

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32

end Ctx

/-! ## Preconditions -/

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 176 ≤ c.sp0.toNat
  /-- code vs. the 184 bytes of frame, saved registers and stack arguments -/
  codeF : Disj c.base Artifacts.Release.size c.fp 184
  /-- code vs. output -/
  codeO : Disj c.base Artifacts.Release.size c.out c.len.toNat
  /-- output vs. frame, saved registers and stack arguments -/
  outF : Disj c.out c.len.toNat c.fp 184
  /-- input vs. frame and saved registers -/
  inF : Disj c.inp c.len.toNat c.fp 176
  /-- exact in-place or disjoint -/
  inOut : c.inp = c.out ∨ Disj c.inp c.len.toNat c.out c.len.toNat
  keyF : Disj c.key 32 c.fp chStackBytes
  nonceF : Disj c.nonce 12 c.fp chStackBytes
  /-- the artifact is in memory at `base` -/
  code : CodeAt c.m0 c.base B

end M0Crypto.Release.Frame

namespace M0Crypto.Release.ChaCha20Setup

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Release.Frame

/-! ## Entry state -/

/-- Entry state of a call described by `c` (AAPCS: r0-r3 = out, in, len, key;
`[sp] = nonce`, `[sp + 4] = counter`). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.out
  r1 : c.regs0 1 = c.inp
  r2 : c.regs0 2 = c.len
  r3 : c.regs0 3 = c.key
  argN : read32 c.m0 c.sp0 = c.nonce
  argC : read32 c.m0 (c.sp0 + 4#32) = c.ctr

end M0Crypto.Release.ChaCha20Setup

namespace M0Crypto.Release.ChaCha20Xor

open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Layout (chStackBytes chFrameWords)

/-! ## Hypothesis of the top-level theorems -/

/-- A valid call of `m0c_chacha20_xor` entered in state `s`. The correctness, trace, read and
stack theorems of the function assume exactly this. -/
structure Pre (c : Ctx) (s : State) : Prop where
  valid : Valid c
  entry : ChaCha20Setup.Entry c s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-! ## Postconditions -/

/-- Outside the function's `chStackBytes` stack bytes. -/
def OutS (c : Ctx) (y : Word) : Prop := ¬ Region c.fp chStackBytes y

/-- The final state of a call. `ok` is the counter check of the C contract. -/
structure Result (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.regs0 14 &&& ~~~1#32
  sp : t.regs 13 = c.sp0
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  r0 : t.regs 0 = if M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat then 0 else ~~~0
  mem : ∀ y, OutS c y → t.mem y =
    if M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat ∧ Region c.out c.len.toNat y
    then c.outB (c.oidx y) else c.m0 y
  wipe : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true → c.len ≠ 0 →
    ∀ i < chFrameWords, read32 t.mem (slot c.fp i) = 0

/-- Writes allowed to a call: its 176 stack bytes, and the output buffer only if the call is
accepted. -/
def WrOk (c : Ctx) (y : Word) : Prop :=
  Region c.fp chStackBytes y ∨
    (M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true ∧ Region c.out c.len.toNat y)

end M0Crypto.Release.ChaCha20Xor
