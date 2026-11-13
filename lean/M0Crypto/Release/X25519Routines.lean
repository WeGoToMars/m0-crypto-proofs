import M0Crypto.Release.X25519Contract
import M0Crypto.Release.X25519Congr

/-!
# Contracts of the X25519 field routines (internal)

Not audited statements: these are the contracts the entry's proof uses
for `m0c_fe_mul`, `m0c_fe_sqr` and `m0c_fe_mulc_add`, proved as ordinary lemmas. They are not
callable from C.

Each routine takes `r0 = dst`, `r1 = a`, `r2 = b` (`m0c_fe_sqr` ignores `b`): 8 little-endian
words, any value below 2^256. The result is congruent modulo `p` to the routine's function of
the inputs. `dst` may equal `a` or `b`, otherwise it does not overlap them. `r0` to `r12` are
scratch; SP is restored. The routine uses `frame` bytes below SP: 148 for multiply and
square (`push {lr}` and a 144-byte frame), 4 for `mulc_add` (`push {lr}`).

The routine's offset and byte size in the artifact are parameters here: the routines are not
exported, and the release artifact names only exported functions. The routine proofs
(`X25519FeMul`, `X25519FeSqr`, `X25519MulcAdd`) bind them to the code. The return address must lie
outside the routine's bytes, not outside the artifact: every call comes from a `bl` in
`m0c_x25519`.
-/

namespace M0Crypto.Release.X25519Routines

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Congr (ModP)

/-- Value of the 8 little-endian words at `a`. -/
def feVal (m : Mem) (a : Word) : Nat :=
  ((List.range 8).map fun i => (read32 m (a + BitVec.ofNat 32 (4 * i))).toNat * 2 ^ (32 * i)).sum

/-- Stack bytes of `m0c_fe_mul` and `m0c_fe_sqr`. -/
def mulFrame : Nat := 148
/-- Stack bytes of `m0c_fe_mulc_add`. -/
def mulcFrame : Nat := 4

/-- A call of a field routine. -/
structure Call where
  base : Word
  sp0 : Word
  dst : Word
  a : Word
  b : Word
  m0 : Mem
  regs0 : Reg → Word

namespace Call

variable (c : Call)

def fp (frame : Nat) : Word := c.sp0 - BitVec.ofNat 32 frame
def ret : Word := c.regs0 14 &&& ~~~1#32

end Call

/-- A valid call of the routine at offset `off`, `size` bytes long, using `frame` stack bytes,
entered in `s`. `useB` says whether the routine reads `b`. -/
structure Pre (off size frame : Nat) (useB : Bool) (c : Call) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 off
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.dst
  r1 : c.regs0 1 = c.a
  r2 : useB = true → c.regs0 2 = c.b
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The routine returns to an address outside its own bytes. -/
  retOut : ¬ Region (c.base + BitVec.ofNat 32 off) size c.ret
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  spLo : frame ≤ c.sp0.toNat
  al : c.dst.toNat % 4 = 0 ∧ c.a.toNat % 4 = 0 ∧ (useB = true → c.b.toNat % 4 = 0)
  code : Thumb.CodeAt c.m0 c.base B
  codeS : Disj c.base Artifacts.Release.size (c.fp frame) frame
  codeD : Disj c.base Artifacts.Release.size c.dst 32
  dstS : Disj c.dst 32 (c.fp frame) frame
  aS : Disj c.a 32 (c.fp frame) frame
  bS : useB = true → Disj c.b 32 (c.fp frame) frame
  dstA : c.dst = c.a ∨ Disj c.dst 32 c.a 32
  dstB : useB = true → c.dst = c.b ∨ Disj c.dst 32 c.b 32

/-- The final state: back at the return address with SP restored, `dst` holding a value
congruent to `f a b`, and memory outside `dst` and the routine's stack unchanged. -/
structure Post (frame : Nat) (f : Int → Int → Int) (c : Call) (t : State) : Prop where
  pc : t.pc = c.ret
  sp : t.regs 13 = c.sp0
  val : ModP (feVal t.mem c.dst) (f (feVal c.m0 c.a) (feVal c.m0 c.b))
  mem : ∀ y, ¬ Region (c.fp frame) frame y → ¬ Region c.dst 32 y → t.mem y = c.m0 y

/-- The routine at `off` returns with `Post`, writing only `dst` and its stack. -/
def Spec (off size frame : Nat) (useB : Bool) (f : Int → Int → Int) : Prop :=
  ∀ c s, Pre off size frame useB c s →
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      Post frame f c t ∧ WritesTo (fun y => Region (c.fp frame) frame y ∨ Region c.dst 32 y) tr

/-- `m0c_fe_mul` at `off`: `dst ≡ a * b`. -/
def MulSpec (off size : Nat) : Prop := Spec off size mulFrame true fun a b => a * b

/-- `m0c_fe_sqr` at `off`: `dst ≡ a * a`. -/
def SqrSpec (off size : Nat) : Prop := Spec off size mulFrame false fun a _ => a * a

/-- `m0c_fe_mulc_add` at `off`: `dst ≡ 121666 * a + b`. -/
def MulcAddSpec (off size : Nat) : Prop :=
  Spec off size mulcFrame true fun a b => 121666 * a + b

end M0Crypto.Release.X25519Routines
