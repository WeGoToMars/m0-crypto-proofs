import M0Crypto.Spec.Ed25519
import M0Crypto.Release.Contract
import M0Crypto.Release.Ed25519Build

/-!
# Contract of `m0c_ed25519_pubkey`, `m0c_ed25519_sign` and `m0c_ed25519_verify`

Statement file: definitions only, no proofs (see `Contract.lean`). Every statement is quantified
over the build `b : Build` (`Ed25519Build`): the code is `b.bytes` at the call's code base, and
the call enters at that build's offset of the function.

C prototypes (`sk = seed ‖ pk`, libsodium's layout):

    void m0c_ed25519_pubkey(uint8_t pk[32], const uint8_t seed[32]);
    void m0c_ed25519_sign(uint8_t sig[64], const uint8_t *m, size_t n, const uint8_t sk[64]);
    int  m0c_ed25519_verify(const uint8_t sig[64], const uint8_t *m, size_t n,
                            const uint8_t pk[32]);     /* 0 or -1 */

The lengths are fixed: `seed` and `pk` 32 bytes, `sk` and `sig` 64, the message `n` bytes with
`n < 2^32 - 64` (the 32-bit SHA-512 byte counter covers `R ‖ A ‖ M`).

Stack, from the entry SP `sp0` down: 36 bytes of saved registers (`r4`-`r11`, `lr`), the
entry's frame, then the deepest callee: 1,060 bytes for pubkey, 1,260 for sign and 1,764 for
verify. Before returning, pubkey and sign zero every byte of the window below the saved
registers (C7). Verify zeroes nothing.

Buffers may be unaligned and may overlap each other in any way. Every input byte is read before
the first write of the output: pubkey hashes `seed` before it writes `pk`, and sign writes `sig`
only after its last hash of `sk` and the message. Inputs may lie in the code. An output must not
overlap the code, and no buffer may overlap the stack window.
-/

namespace M0Crypto.Release.Ed25519

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Artifacts

abbrev Byte := Spec.Ed25519.Byte

/-! ## Entry offsets -/

namespace Build

def pubkeyAt : Build → Nat
  | compact => Ed25519Compact.ed25519_pubkey
  | fast => Ed25519Fast.ed25519_pubkey

def signAt : Build → Nat
  | compact => Ed25519Compact.ed25519_sign
  | fast => Ed25519Fast.ed25519_sign

def verifyAt : Build → Nat
  | compact => Ed25519Compact.ed25519_verify
  | fast => Ed25519Fast.ed25519_verify

end Build

/-! ## What the three entries share -/

/-- Bytes of saved registers at the top of every entry's stack window. -/
def savedBytes : Nat := 36

/-- The registers an entry saves, one word each, from `sp0 - 36` up: `push {r4-r7, lr}` at
`sp0 - 20`, then `push {r4-r7}` of copies of `r8`-`r11` at `sp0 - 36`. -/
def savedRegs : List Reg := [8, 9, 10, 11, 4, 5, 6, 7, 14]

/-- The part of a call that does not depend on the entry. -/
structure Call where
  /-- Address of the build's first byte. -/
  base : Word
  /-- SP at entry. -/
  sp0 : Word
  /-- Memory at entry. -/
  m0 : Mem
  /-- Registers at entry. -/
  regs0 : Reg → Word

namespace Call

variable (k : Call)

/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := k.regs0 14 &&& ~~~1#32

/-- Lowest address of an `n`-byte stack window. -/
def fp (n : Nat) : Word := k.sp0 - BitVec.ofNat 32 n

/-- The `n` bytes at `a` at entry. -/
def bytes (a : Word) (n : Nat) : List Byte := Frame.Ctx.bytesAt k.m0 a n

/-- Preconditions of a call of build `b` with an `n`-byte stack window that involve no buffer. -/
structure Valid (b : Build) (n : Nat) : Prop where
  base4 : k.base.toNat % 4 = 0
  sp4 : k.sp0.toNat % 4 = 0
  /-- the stack window does not wrap -/
  spLo : n ≤ k.sp0.toNat
  /-- code vs. stack window -/
  codeS : Disj k.base b.size (k.fp n) n
  /-- the build is in memory at `base` -/
  code : Thumb.CodeAt k.m0 k.base b.bytes
  /-- LR is a Thumb address. -/
  thumb : (k.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the build. -/
  retOut : ¬ Region k.base b.size k.ret

/-- Entry state at offset `off` of the build. -/
structure Entry (off : Nat) (s : State) : Prop where
  regs : s.regs = k.regs0
  mem : s.mem = k.m0
  pc : k.regs0 15 = k.base + BitVec.ofNat 32 off
  sp : k.regs0 13 = k.sp0

/-- The call has returned: PC at the return address, SP and r4-r11 restored. -/
structure Returned (t : State) : Prop where
  pc : t.pc = k.ret
  sp : t.regs 13 = k.sp0
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = k.regs0 r

/-- Outside the `n`-byte stack window, the `len` bytes at `out` hold `bs` and every other byte is
unchanged. -/
def MemOut (n : Nat) (out : Word) (len : Nat) (bs : List Byte) (t : State) : Prop :=
  ∀ y, ¬ Region (k.fp n) n y →
    t.mem y = if Region out len y then bs[(y - out).toNat]! else k.m0 y

/-- C7 for an `n`-byte window: the bytes below the saved registers are zero, and the 36 bytes
above them hold the caller's registers as saved at entry (word `i` is `savedRegs[i]`), so every
byte of the window is fixed. r1-r3 and r12 are zero. -/
structure Wiped (n : Nat) (t : State) : Prop where
  r1 : t.regs 1 = 0
  r2 : t.regs 2 = 0
  r3 : t.regs 3 = 0
  r12 : t.regs 12 = 0
  wipe : ∀ y, Region (k.fp n) (n - savedBytes) y → t.mem y = 0
  saved : ∀ i < 9,
    read32 t.mem (k.fp n + BitVec.ofNat 32 (n - savedBytes + 4 * i)) = k.regs0 savedRegs[i]!

/-- From `s`, the call returns in a state with `R`, and every write of the run is in `W`. -/
def Returns (s : State) (R : State → Prop) (W : Word → Prop) : Prop :=
  ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil k.ret fuel s = .ok (t, tr) ∧
    R t ∧ WritesTo W tr

end Call

/-! ## `m0c_ed25519_pubkey(pk, seed)` -/

namespace Pubkey

def stackBytes : Nat := 1060

structure Ctx extends Call where
  pk : Word
  seed : Word

namespace Ctx

variable (c : Ctx)

def fp : Word := c.toCall.fp stackBytes
def seedB : List Byte := c.bytes c.seed 32
/-- RFC 8032 section 5.1.5. -/
def pkOut : List Byte := Spec.Ed25519.publicKey c.seedB

end Ctx

structure Valid (b : Build) (c : Ctx) : Prop where
  call : c.toCall.Valid b stackBytes
  /-- code vs. output -/
  codeO : Disj c.base b.size c.pk 32
  pkS : Disj c.pk 32 c.fp stackBytes
  seedS : Disj c.seed 32 c.fp stackBytes

/-- AAPCS: r0 = pk, r1 = seed. -/
structure Entry (b : Build) (c : Ctx) (s : State) : Prop where
  call : c.toCall.Entry b.pubkeyAt s
  r0 : c.regs0 0 = c.pk
  r1 : c.regs0 1 = c.seed

/-- A valid call entered in `s`: the hypothesis of every pubkey theorem. -/
structure Pre (b : Build) (c : Ctx) (s : State) : Prop where
  valid : Valid b c
  entry : Entry b c s

structure Result (c : Ctx) (t : State) : Prop where
  ret : c.Returned t
  wiped : c.Wiped stackBytes t
  mem : c.MemOut stackBytes c.pk 32 c.pkOut t

def WrOk (c : Ctx) (y : Word) : Prop := Region c.fp stackBytes y ∨ Region c.pk 32 y

def Correct : Prop := ∀ b c s, Pre b c s → c.Returns s (Result c) (WrOk c)

end Pubkey

/-! ## `m0c_ed25519_sign(sig, m, n, sk)` -/

namespace Sign

def stackBytes : Nat := 1260

structure Ctx extends Call where
  sig : Word
  msg : Word
  len : Word
  sk : Word

namespace Ctx

variable (c : Ctx)

def fp : Word := c.toCall.fp stackBytes
def seedB : List Byte := c.bytes c.sk 32
/-- `sk[32..64]`: the public key as the caller supplies it, not checked (C2). -/
def pkB : List Byte := c.bytes (c.sk + 32#32) 32
def msgB : List Byte := c.bytes c.msg c.len.toNat
/-- RFC 8032 section 5.1.6 with the caller's public key (D8). -/
def sigOut : List Byte := Spec.Ed25519.signWith c.seedB c.pkB c.msgB

end Ctx

structure Valid (b : Build) (c : Ctx) : Prop where
  call : c.toCall.Valid b stackBytes
  lenLt : c.len.toNat < 2 ^ 32 - 64
  codeO : Disj c.base b.size c.sig 64
  sigS : Disj c.sig 64 c.fp stackBytes
  msgS : c.len = 0 ∨ Disj c.msg c.len.toNat c.fp stackBytes
  skS : Disj c.sk 64 c.fp stackBytes

/-- AAPCS: r0 = sig, r1 = m, r2 = n, r3 = sk. -/
structure Entry (b : Build) (c : Ctx) (s : State) : Prop where
  call : c.toCall.Entry b.signAt s
  r0 : c.regs0 0 = c.sig
  r1 : c.regs0 1 = c.msg
  r2 : c.regs0 2 = c.len
  r3 : c.regs0 3 = c.sk

structure Pre (b : Build) (c : Ctx) (s : State) : Prop where
  valid : Valid b c
  entry : Entry b c s

structure Result (c : Ctx) (t : State) : Prop where
  ret : c.Returned t
  wiped : c.Wiped stackBytes t
  mem : c.MemOut stackBytes c.sig 64 c.sigOut t

def WrOk (c : Ctx) (y : Word) : Prop := Region c.fp stackBytes y ∨ Region c.sig 64 y

def Correct : Prop := ∀ b c s, Pre b c s → c.Returns s (Result c) (WrOk c)

/-- When `sk[32..64]` is the public key of `seed`, `sig` holds the RFC 8032 signature. -/
def CorrectRfc : Prop :=
  ∀ b c s, Pre b c s → c.pkB = Spec.Ed25519.publicKey c.seedB →
    c.Returns s (fun t => Result c t ∧
      Frame.Ctx.bytesAt t.mem c.sig 64 = Spec.Ed25519.sign c.seedB c.msgB) (WrOk c)

end Sign

/-! ## `m0c_ed25519_verify(sig, m, n, pk)` -/

namespace Verify

def stackBytes : Nat := 1764

structure Ctx extends Call where
  sig : Word
  msg : Word
  len : Word
  pk : Word

namespace Ctx

variable (c : Ctx)

def fp : Word := c.toCall.fp stackBytes
def sigB : List Byte := c.bytes c.sig 64
def msgB : List Byte := c.bytes c.msg c.len.toNat
def pkB : List Byte := c.bytes c.pk 32

end Ctx

structure Valid (b : Build) (c : Ctx) : Prop where
  call : c.toCall.Valid b stackBytes
  lenLt : c.len.toNat < 2 ^ 32 - 64
  sigS : Disj c.sig 64 c.fp stackBytes
  msgS : c.len = 0 ∨ Disj c.msg c.len.toNat c.fp stackBytes
  pkS : Disj c.pk 32 c.fp stackBytes

/-- AAPCS: r0 = sig, r1 = m, r2 = n, r3 = pk. -/
structure Entry (b : Build) (c : Ctx) (s : State) : Prop where
  call : c.toCall.Entry b.verifyAt s
  r0 : c.regs0 0 = c.sig
  r1 : c.regs0 1 = c.msg
  r2 : c.regs0 2 = c.len
  r3 : c.regs0 3 = c.pk

structure Pre (b : Build) (c : Ctx) (s : State) : Prop where
  valid : Valid b c
  entry : Entry b c s

structure Result (c : Ctx) (t : State) : Prop where
  ret : c.Returned t
  /-- 0 exactly when `Spec.Ed25519.verify` accepts (C3: RFC 8032 section 5.1.3 decoding, S < L, the
  cofactorless equation with k reduced modulo L as in section 6), else -1. -/
  r0 : t.regs 0 = if Spec.Ed25519.verify c.sigB c.msgB c.pkB then 0 else 0xffffffff#32
  /-- Memory outside the stack window is unchanged. -/
  mem : ∀ y, ¬ Region c.fp stackBytes y → t.mem y = c.m0 y

def WrOk (c : Ctx) (y : Word) : Prop := Region c.fp stackBytes y

def Correct : Prop := ∀ b c s, Pre b c s → c.Returns s (Result c) (WrOk c)

end Verify

end M0Crypto.Release.Ed25519
