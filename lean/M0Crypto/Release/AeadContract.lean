import M0Crypto.Release.ChaCha20Contract

/-!
# Contract of `m0c_chacha20poly1305_encrypt` and `m0c_chacha20poly1305_decrypt`

Statement file: definitions only, no proofs (see `Contract.lean`). In reading order: the call
(`ACall`), the entry state (`AEntry`), the preconditions (`AValid`, `ABuf`), the three bundled
as the hypothesis of every headline theorem (`APre`), the write regions, and what a returned
call guarantees (`RetPost`, `EncryptResult`, `DecryptResult`). Compare with
`include/m0crypto/chacha20poly1305.h`.
-/

namespace M0Crypto.Release.Aead

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (macData encrypt decrypt poly1305 polyKey)

/-! ## The call -/

/-- One AEAD call (same register and stack arguments for encrypt and decrypt). -/
structure ACall where
  base : Word
  sp0 : Word
  out : Word
  tag : Word
  inp : Word
  len : Word
  aad : Word
  alen : Word
  key : Word
  nonce : Word
  m0 : Mem
  regs0 : Reg → Word

namespace ACall
variable (c : ACall)
/-- Stack pointer after the prologue. -/
def A : Word := c.sp0 - 144#32
/-- Return address: LR with the Thumb bit cleared. -/
def ret : Word := c.regs0 14 &&& ~~~1#32
end ACall

/-- Entry to the function at offset `e`. -/
structure AEntry (c : ACall) (e : Nat) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 e
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.out
  r1 : c.regs0 1 = c.tag
  r2 : c.regs0 2 = c.inp
  r3 : c.regs0 3 = c.len
  aad : read32 c.m0 c.sp0 = c.aad
  alen : read32 c.m0 (c.sp0 + 4#32) = c.alen
  key : read32 c.m0 (c.sp0 + 8#32) = c.key
  nonce : read32 c.m0 (c.sp0 + 12#32) = c.nonce

/-- Entry offsets: the release symbols. -/
def encOff : Nat := Artifacts.Release.chacha20poly1305_encrypt
def decOff : Nat := Artifacts.Release.chacha20poly1305_decrypt

/-! ## Caller data -/

/-- Key and nonce bytes as the caller passed them. -/
def ACall.keyB (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte := Ctx.bytesAt c.m0 c.key 32
def ACall.nonceB (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte := Ctx.bytesAt c.m0 c.nonce 12

/-- AAD bytes shared by the encryption and decryption contracts. -/
def ACall.aadB (c : ACall) := Ctx.bytesAt c.m0 c.aad c.alen.toNat

/-- Caller input bytes. -/
def ACall.ptB (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte := Ctx.bytesAt c.m0 c.inp c.len.toNat

def ACall.tagB (c : ACall) := Ctx.bytesAt c.m0 c.tag 16
def ACall.expected (c : ACall) := poly1305 (polyKey c.keyB c.nonceB) (macData c.aadB c.ptB)

/-! ## Preconditions -/

structure AValid (c : ACall) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 320 ≤ c.sp0.toNat
  spHi : c.sp0.toNat + 16 ≤ 2 ^ 32
  codeS : Disj c.base Artifacts.Release.size (c.sp0 - 320#32) 336
  keyS : Disj c.key 32 (c.sp0 - 320#32) 320
  nonceS : Disj c.nonce 12 (c.sp0 - 320#32) 320
  code : CodeAt c.m0 c.base B

/-- Caller buffer placement. `in` is exactly `out` or disjoint from it; `out`, `in`,
`aad` and `tag` stay clear of the stack region and caller arguments, and `out`,
`tag` clear of the code. -/
structure ABuf (c : ACall) : Prop where
  outS : Disj c.out c.len.toNat (c.sp0 - 320#32) 336
  inS : Disj c.inp c.len.toNat (c.sp0 - 320#32) 320
  inOut : c.inp = c.out ∨ Disj c.inp c.len.toNat c.out c.len.toNat
  codeO : Disj c.base Artifacts.Release.size c.out c.len.toNat
  aadS : Disj c.aad c.alen.toNat (c.sp0 - 320#32) 320
  aadO : Disj c.aad c.alen.toNat c.out c.len.toNat
  tagS : Disj c.tag 16 (c.sp0 - 320#32) 336
  tagO : Disj c.tag 16 c.out c.len.toNat
  codeT : Disj c.base Artifacts.Release.size c.tag 16

/-! ## Hypothesis of the headline theorems -/

/-- A valid call of the AEAD function at offset `e` (`encOff` or `decOff`) entered in state
`s`. The correctness, trace, read and stack theorems of both functions assume exactly this. -/
structure APre (c : ACall) (e : Nat) (s : State) : Prop where
  valid : AValid c
  buf : ABuf c
  entry : AEntry c e s
  /-- LR is a Thumb address. -/
  thumb : (c.regs0 14).getLsbD 0 = true
  /-- The function returns to an address outside the artifact. -/
  retOut : ¬ Region c.base Artifacts.Release.size c.ret

/-! ## Write regions -/

/-- The stack region of the AEAD and its callees: `[sp0 - 320, sp0)`. -/
def SWr (A : Word) (y : Word) : Prop := Region (A - 176#32) 320 y

/-- Bytes of the output buffer. -/
def OutR (c : ACall) (y : Word) : Prop := Region c.out c.len.toNat y

/-- The AEAD's writes: the stack region, `out` and `tag`. -/
def AWr (c : ACall) (y : Word) : Prop := SWr c.A y ∨ OutR c y ∨ Region c.tag 16 y

def DWr (c : ACall) (y : Word) : Prop := SWr c.A y ∨ OutR c y

/-- Output stores are permitted only after successful authentication. -/
def DAllowed (c : ACall) (y : Word) : Prop := SWr c.A y ∨ (c.expected=c.tagB ∧ OutR c y)

/-! ## Postconditions -/

/-- Common C ABI postcondition, independent of AEAD success or failure. -/
structure RetPost (c : ACall) (result : Word) (t : State) : Prop where
  pc : t.pc = c.regs0 14 &&& ~~~1#32
  sp : t.regs 13 = c.sp0
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  r0 : t.regs 0 = result
  scratch : ∀ r : Reg, 1 ≤ r.val → r.val < 4 → t.regs r = 0#32

/-- Ciphertext and tag, erasure and C ABI for encryption. -/
structure EncryptResult (c : ACall) (t : State) : Prop extends RetPost c 0#32 t where
  out : Ctx.bytesAt t.mem c.out c.len.toNat = (encrypt c.keyB c.nonceB c.aadB c.ptB).1
  tag : Ctx.bytesAt t.mem c.tag 16 = (encrypt c.keyB c.nonceB c.aadB c.ptB).2
  frame : ∀ y, ¬ AWr c y → t.mem y = c.m0 y
  zero : ∀ o < 96, t.mem (c.A + BitVec.ofNat 32 (8+o)) = 0#8

/-- Checked decryption, unchanged output on authentication failure, erasure and ABI. -/
structure DecryptResult (c : ACall) (t : State) : Prop where
  abi : RetPost c (if c.expected=c.tagB then 0#32 else 0xfffffffe#32) t
  ok : ∀ pt, decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB=some pt →
    t.regs 0=0#32 ∧ Ctx.bytesAt t.mem c.out c.len.toNat=pt
  reject : decrypt c.keyB c.nonceB c.aadB c.ptB c.tagB=none →
    t.regs 0=0xfffffffe#32 ∧ Ctx.bytesAt t.mem c.out c.len.toNat=Ctx.bytesAt c.m0 c.out c.len.toNat
  frame : ∀ y, ¬ DWr c y → t.mem y=c.m0 y
  zero : ∀ o<96, t.mem (c.A+BitVec.ofNat 32 (8+o))=0#8

end M0Crypto.Release.Aead
