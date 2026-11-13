import M0Crypto.Spec.Blake2s
import M0Crypto.Release.Contract

/-!
# Contract of `m0c_blake2s_init`, `m0c_blake2s_update` and `m0c_blake2s_final`

Statement file: definitions only, no proofs (see `Contract.lean`). In reading order: the sizes,
the context and what it means for it to hold a streaming state (`ContextHolds`), then for each
of the three exported functions the call (`Ctx`), its preconditions (`Valid`), the entry state
(`Entry`), the two bundled as the hypothesis of every top-level theorem (`Pre`), and what a
returned call guarantees (`Result`, `WrOk`, `Correct`). Compare with
`include/m0crypto/blake2s.h` and `src/blake2s_internal.h`.

C prototypes:

    void m0c_blake2s_init(m0c_blake2s_ctx *c);
    void m0c_blake2s_update(m0c_blake2s_ctx *c, const uint8_t *p, size_t n);
    void m0c_blake2s_final(m0c_blake2s_ctx *c, uint8_t out[32]);

The context is 112 bytes, word aligned: `h[8]` at 0, the 64-bit `count` at 32, `buf[64]` at 40
and `used` at 104 (the `CTX_*` offsets of `src/blake2s_stream.S`, pinned by the
`_Static_assert`s of `src/blake2s_internal.h`). Input and output may be at any byte address.
The stream the context holds is a specification state (`Spec.Blake2s.State`): `update` absorbs
its input into it, `final` emits the RFC 7693 digest of it. The internal routines
`m0c_blake2s_compress` and `m0c_blake2s_copy` are local symbols and have no contract here; their
frames are part of the stack bounds below.
-/

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Mem read32)

/-! ## Sizes -/

/-- Bytes of `m0c_blake2s_ctx`. -/
def contextBytes : Nat := 112

/-- Bytes of the digest `final` writes. -/
def digestBytes : Nat := 32

/-- Stack bytes of `init`: its `push {lr}`. -/
def initStackBytes : Nat := 4

/-- Local bytes of `m0c_blake2s_compress` (`LOCALS` of `src/blake2s_compress.S`). -/
def compressLocalsBytes : Nat := 100

/-- Bytes `m0c_blake2s_compress` saves (r4-r11, lr). -/
def compressSavedBytes : Nat := 36

/-- Frame of `m0c_blake2s_compress` below its entry SP. -/
def compressFrameBytes : Nat := compressLocalsBytes + compressSavedBytes

/-- Bytes `update` and `final` save (`push {r4-r7, lr}`). -/
def streamSavedBytes : Nat := 20

/-- `FRAME_PAD` of `update` and `final`: the slot of compress's stacked `f0` argument. -/
def streamPadBytes : Nat := 4

/-- Stack bytes of `update` and `final` below the entry SP: their own frame and the deeper of
their callees' frames (compress; the 20-byte frame of copy is smaller). -/
def streamStackBytes : Nat := streamSavedBytes + streamPadBytes + compressFrameBytes

/-! ## The context -/

/-- The `n` bytes of `m` starting at `p`. -/
def bytesAt (m : Mem) (p : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m (p + BitVec.ofNat 32 i)

/-- The context at `c` holds the chain value, byte count and pending bytes of the stream `st`
(every field except `used`). -/
structure ContextHoldsExceptUsed (m : Mem) (c : Word) (st : Spec.Blake2s.State) : Prop where
  hSize : st.h.size = 8
  /-- `h[i]` at offset `4 i`. -/
  h : ∀ i < 8, read32 m (c + BitVec.ofNat 32 (4 * i)) = st.h[i]!
  /-- `count`, little-endian 64 bits at offset 32. -/
  countLow : read32 m (c + 32#32) = BitVec.ofNat 32 st.count
  countHigh : read32 m (c + 36#32) = BitVec.ofNat 32 (st.count / 2 ^ 32)
  countLt : st.count < 2 ^ 64
  pendingLe : st.pending.length ≤ 64
  /-- The pending bytes at the start of `buf` (offset 40). -/
  buf : bytesAt m (c + 40#32) st.pending.length = st.pending

/-- The context at `c` holds the stream `st`, including `used` (offset 104), the number of
pending bytes. -/
structure ContextHolds (m : Mem) (c : Word) (st : Spec.Blake2s.State) : Prop
    extends ContextHoldsExceptUsed m c st where
  used : read32 m (c + 104#32) = BitVec.ofNat 32 st.pending.length

end M0Crypto.Release.Blake2s

/-! ## `m0c_blake2s_init` -/

namespace M0Crypto.Release.Blake2s.Init

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2s (contextBytes initStackBytes ContextHolds)

/-- One call of `init`. -/
structure Ctx where
  /-- Address of the release artifact's first byte. -/
  base : Word
  /-- SP at entry. -/
  sp0 : Word
  /-- The context pointer `c`. -/
  context : Word
  /-- Memory at entry. -/
  m0 : Mem
  /-- Registers at entry. -/
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Lowest stack address the call uses. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 initStackBytes

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32

end Ctx

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  /-- the stack window does not wrap -/
  spLo : initStackBytes ≤ c.sp0.toNat
  context4 : c.context.toNat % 4 = 0
  /-- code vs. context -/
  codeC : Disj c.base Artifacts.Release.size c.context contextBytes
  /-- code vs. stack window -/
  codeS : Disj c.base Artifacts.Release.size c.fp initStackBytes
  /-- context vs. stack window -/
  contextS : Disj c.context contextBytes c.fp initStackBytes
  /-- the artifact is in memory at `base` -/
  code : Thumb.CodeAt c.m0 c.base B

/-- Entry state of a call described by `c` (AAPCS: r0 = c). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 Artifacts.Release.blake2s_init
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.context

/-- A valid call of `m0c_blake2s_init` entered in state `s`. The correctness, trace, read and
stack theorems assume exactly this. -/
structure Pre (c : Ctx) (s : State) : Prop where
  valid : Valid c
  entry : Entry c s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-- Writes allowed to a call: its stack window and the context. -/
def WrOk (c : Ctx) (y : Word) : Prop :=
  Region c.fp initStackBytes y ∨ Region c.context contextBytes y

/-- The final state of a call: the context holds the empty stream. -/
structure Result (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.ret
  sp : t.regs 13 = c.sp0
  /-- r4-r11 restored. -/
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  holds : ContextHolds t.mem c.context Spec.Blake2s.State.init
  /-- Memory outside the allowed writes is unchanged. -/
  mem : ∀ y, ¬ WrOk c y → t.mem y = c.m0 y

/-- Every valid call returns, with `Result` and only allowed writes. -/
def Correct : Prop :=
  ∀ c s, Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      Result c t ∧ WritesTo (WrOk c) tr

end M0Crypto.Release.Blake2s.Init

/-! ## `m0c_blake2s_update` -/

namespace M0Crypto.Release.Blake2s.Update

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2s (contextBytes streamStackBytes ContextHolds bytesAt)

/-- One call of `update`. -/
structure Ctx where
  /-- Address of the release artifact's first byte. -/
  base : Word
  /-- SP at entry. -/
  sp0 : Word
  /-- The context pointer `c`. -/
  context : Word
  /-- The input pointer `p`. -/
  input : Word
  /-- The input length `n`. -/
  len : Word
  /-- The stream the context holds at entry. -/
  stream : Spec.Blake2s.State
  /-- Memory at entry. -/
  m0 : Mem
  /-- Registers at entry. -/
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Lowest stack address the call (with its callees) uses. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 streamStackBytes

/-- The input bytes. -/
def inputB : List Spec.Blake2s.Byte := bytesAt c.m0 c.input c.len.toNat

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32

end Ctx

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  /-- the stack window does not wrap -/
  spLo : streamStackBytes ≤ c.sp0.toNat
  context4 : c.context.toNat % 4 = 0
  /-- the context holds `stream` -/
  holds : ContextHolds c.m0 c.context c.stream
  /-- the cumulative length stays below 2^64 bytes -/
  lengthLt : c.stream.count + c.stream.pending.length + c.len.toNat < 2 ^ 64
  /-- code vs. context -/
  codeC : Disj c.base Artifacts.Release.size c.context contextBytes
  /-- code vs. stack window -/
  codeS : Disj c.base Artifacts.Release.size c.fp streamStackBytes
  /-- context vs. stack window -/
  contextS : Disj c.context contextBytes c.fp streamStackBytes
  /-- input vs. context -/
  inputC : Disj c.input c.len.toNat c.context contextBytes
  /-- input vs. stack window -/
  inputS : Disj c.input c.len.toNat c.fp streamStackBytes
  /-- the artifact is in memory at `base` -/
  code : Thumb.CodeAt c.m0 c.base B

/-- Entry state of a call described by `c` (AAPCS: r0-r2 = c, p, n). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 Artifacts.Release.blake2s_update
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.context
  r1 : c.regs0 1 = c.input
  r2 : c.regs0 2 = c.len

/-- A valid call of `m0c_blake2s_update` entered in state `s`. The correctness, trace, read and
stack theorems assume exactly this. -/
structure Pre (c : Ctx) (s : State) : Prop where
  valid : Valid c
  entry : Entry c s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-- Writes allowed to a call: its stack window and the context. -/
def WrOk (c : Ctx) (y : Word) : Prop :=
  Region c.fp streamStackBytes y ∨ Region c.context contextBytes y

/-- The final state of a call: the context holds the stream with the input absorbed. -/
structure Result (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.ret
  sp : t.regs 13 = c.sp0
  /-- r4-r11 restored. -/
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  holds : ContextHolds t.mem c.context (Spec.Blake2s.absorb c.stream c.inputB)
  /-- Memory outside the allowed writes is unchanged. -/
  mem : ∀ y, ¬ WrOk c y → t.mem y = c.m0 y
  /-- r0-r3 are zero: no input byte stays in a scratch register. -/
  scratch : ∀ r : Reg, r.val < 4 → t.regs r = 0

/-- Every valid call returns, with `Result` and only allowed writes. -/
def Correct : Prop :=
  ∀ c s, Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      Result c t ∧ WritesTo (WrOk c) tr

end M0Crypto.Release.Blake2s.Update

/-! ## `m0c_blake2s_final` -/

namespace M0Crypto.Release.Blake2s.Final

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2s (contextBytes digestBytes streamStackBytes ContextHolds bytesAt)

/-- One call of `final`. -/
structure Ctx where
  /-- Address of the release artifact's first byte. -/
  base : Word
  /-- SP at entry. -/
  sp0 : Word
  /-- The context pointer `c`. -/
  context : Word
  /-- The output pointer `out`. -/
  out : Word
  /-- The stream the context holds at entry. -/
  stream : Spec.Blake2s.State
  /-- Memory at entry. -/
  m0 : Mem
  /-- Registers at entry. -/
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Lowest stack address the call (with its callee) uses. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 streamStackBytes

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32

end Ctx

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  /-- the stack window does not wrap -/
  spLo : streamStackBytes ≤ c.sp0.toNat
  context4 : c.context.toNat % 4 = 0
  /-- the context holds `stream` -/
  holds : ContextHolds c.m0 c.context c.stream
  /-- the cumulative length stays below 2^64 bytes -/
  lengthLt : c.stream.count + c.stream.pending.length < 2 ^ 64
  /-- code vs. context -/
  codeC : Disj c.base Artifacts.Release.size c.context contextBytes
  /-- code vs. stack window -/
  codeS : Disj c.base Artifacts.Release.size c.fp streamStackBytes
  /-- code vs. output -/
  codeO : Disj c.base Artifacts.Release.size c.out digestBytes
  /-- context vs. stack window -/
  contextS : Disj c.context contextBytes c.fp streamStackBytes
  /-- output vs. stack window -/
  outS : Disj c.out digestBytes c.fp streamStackBytes
  /-- context vs. output -/
  contextO : Disj c.context contextBytes c.out digestBytes
  /-- the artifact is in memory at `base` -/
  code : Thumb.CodeAt c.m0 c.base B

/-- Entry state of a call described by `c` (AAPCS: r0-r1 = c, out). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 Artifacts.Release.blake2s_final
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.context
  r1 : c.regs0 1 = c.out

/-- A valid call of `m0c_blake2s_final` entered in state `s`. The correctness, trace, read and
stack theorems assume exactly this. -/
structure Pre (c : Ctx) (s : State) : Prop where
  valid : Valid c
  entry : Entry c s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-- Writes allowed to a call: its stack window, the context (`final` consumes it) and `out`. -/
def WrOk (c : Ctx) (y : Word) : Prop :=
  Region c.fp streamStackBytes y ∨ Region c.context contextBytes y ∨ Region c.out digestBytes y

/-- The final state of a call: `out` holds the RFC 7693 digest of the stream. -/
structure Result (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.ret
  sp : t.regs 13 = c.sp0
  /-- r4-r11 restored. -/
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  out : bytesAt t.mem c.out digestBytes = Spec.Blake2s.finish c.stream
  /-- Memory outside the allowed writes is unchanged. -/
  mem : ∀ y, ¬ WrOk c y → t.mem y = c.m0 y
  /-- r0-r3 are zero: no digest word stays in a scratch register. -/
  scratch : ∀ r : Reg, r.val < 4 → t.regs r = 0

/-- Every valid call returns, with `Result` and only allowed writes. -/
def Correct : Prop :=
  ∀ c s, Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧
      Result c t ∧ WritesTo (WrOk c) tr

end M0Crypto.Release.Blake2s.Final
