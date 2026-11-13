import M0Crypto.Release.X25519Contract

/-!
Frame layout of `m0c_x25519`. This is the only place
that names stack offsets of the entry; it mirrors the layout section of
`tools/gen_x25519.py`, and the instance checks of `X25519EntryCode` tie it to the bytes.

After the prologue SP is `E c = sp0 - (SAVED + LFRAME)`. The frame holds five persistent
field elements, four temporaries, the clamped scalar and three words. The callees use the
`CALLEE` bytes below `E`; together with the frame that is `X25519.wipeBytes`, starting at
`c.fp`.
-/

namespace M0Crypto.Release.X25519Layout
open M0Crypto.Armv6M (Word)

def sX1 : Nat := 0
def sX2 : Nat := 32
def sZ2 : Nat := 64
def sX3 : Nat := 96
def sZ3 : Nat := 128
def sA : Nat := 160
def sB : Nat := 192
def sC : Nat := 224
def sD : Nat := 256
/-- Clamped scalar, 8 words. -/
def sK : Nat := 288
/-- Ladder bit index, then the squaring counter. -/
def lvT : Nat := 320
def lvSwap : Nat := 324
def lvOut : Nat := 328
def LFRAME : Nat := 332
/-- r4-r7, lr, then r8-r11. -/
def SAVED : Nat := 36
/-- Deepest callee frame (`m0c_fe_mul`, `m0c_fe_sqr`). -/
def CALLEE : Nat := 148

/-- The offsets as numbers, for `omega` in the proofs (the only place they are restated). -/
theorem lay : sX1 = 0 ∧ sX2 = 32 ∧ sZ2 = 64 ∧ sX3 = 96 ∧ sZ3 = 128 ∧ sK = 288 ∧ lvT = 320 ∧
    lvSwap = 324 ∧ lvOut = 328 ∧ LFRAME = 332 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stack_split : SAVED + LFRAME + CALLEE = X25519.stackBytes := rfl
theorem wipe_split : LFRAME + CALLEE = X25519.wipeBytes := rfl

/-- SP after the prologue. -/
def E (c : X25519.Ctx) : Word := c.sp0 - BitVec.ofNat 32 (SAVED + LFRAME)

end M0Crypto.Release.X25519Layout
