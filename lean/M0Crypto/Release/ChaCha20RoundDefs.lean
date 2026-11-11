import M0Crypto.Thumb.SpBlock

/-!
# Release ChaCha20 double round: definitions

The code of the double round (`core`, `pre`, `post`, `qr`, `dround`), the rotation-register
precondition `RotRegs`, the row-d register map `dregOf`, the ChaCha state view `view`, and
the fact that every instruction of `dround` falls through.

These definitions live apart from `Release.ChaCha20Round` (the hand-proved statements), so
that the symbolic checks in `Sym.ChaCha20Core` and `Sym.ChaCha20DoubleRound` can use them without
importing that module.
-/

namespace M0Crypto.Release.ChaCha20Round

open M0Crypto.Armv6M (Word Reg LowReg State read32 slot)
open M0Crypto.Thumb

def core : List Instr :=
  [ .addReg 0 0 1, .dp .eors 3 0, .dp .rors 3 4, .addReg 2 2 3, .dp .eors 1 2, .dp .rors 1 5,
    .addReg 0 0 1, .dp .eors 3 0, .dp .rors 3 6, .addReg 2 2 3, .dp .eors 1 2, .dp .rors 1 7 ]

/-- Loads of `QR_REG_D`: a (unless already in r0), b, c from the stack; d from `dreg`. -/
def pre (a b c : Nat) (dreg : Reg) (haveA : Bool) : List Instr :=
  (if haveA then [] else [.ldrSp 0 (BitVec.ofNat 8 a)]) ++
  [.ldrSp 1 (BitVec.ofNat 8 b), .ldrSp 2 (BitVec.ofNat 8 c), .movHi 3 dreg]

/-- Stores of `QR_REG_D`: a (unless kept in r0), b, c to the stack; d to `dreg`. -/
def post (a b c : Nat) (dreg : Reg) (keepA : Bool) : List Instr :=
  (if keepA then [] else [.strSp 0 (BitVec.ofNat 8 a)]) ++
  [.strSp 1 (BitVec.ofNat 8 b), .strSp 2 (BitVec.ofNat 8 c), .movHi dreg 3]

/-- `QR_REG_D a, b, c, dreg, have_a, keep_a` (src/chacha20_round.inc). -/
def qr (a b c : Nat) (dreg : Reg) (haveA keepA : Bool) : List Instr :=
  pre a b c dreg haveA ++ core ++ post a b c dreg keepA

/-- `DOUBLE_ROUND_REG_D`. -/
def dround : List Instr :=
  qr 2 6 10 ⟨10, by decide⟩ true false ++ qr 0 4 8 ⟨8, by decide⟩ false false ++
  qr 1 5 9 ⟨9, by decide⟩ false false ++ qr 3 7 11 ⟨11, by decide⟩ false true ++
  qr 3 4 9 ⟨10, by decide⟩ true false ++ qr 0 5 10 ⟨11, by decide⟩ false false ++
  qr 1 6 11 ⟨8, by decide⟩ false false ++ qr 2 7 8 ⟨9, by decide⟩ false true

/-- Stack slots the double round addresses: slots `0..11`, one per spilled state word
(`strSp`/`ldrSp` operands in `dround`). -/
def droundSlots : Nat := 12

/-- Bytes above SP that `dround` may write: `droundSlots` words. -/
def droundBytes : Nat := 4 * droundSlots

/-- r4-r7 hold the rotation counts for left rotations by 16, 12, 8, 7. -/
structure RotRegs (s : State) : Prop where
  r4 : s.regs 4 = 16#32
  r5 : s.regs 5 = 20#32
  r6 : s.regs 6 = 24#32
  r7 : s.regs 7 = 25#32

/-- Register of d-row word `k` (12..15 ↦ r8..r11). -/
def dregOf (k : Nat) : Reg := ⟨(k - 4) % 16, Nat.mod_lt _ (by decide)⟩

/-- The 16-word ChaCha state as the round loop holds it: rows a, b, c in stack slots
0..11 (except the word kept in r0, if any), row d in r8..r11. 0 beyond 16. -/
def view (inR0 : Option Nat) (s : State) (k : Nat) : Word :=
  if k < 12 then (if inR0 = some k then s.regs 0 else read32 s.mem (slot (s.regs 13) k))
  else if k < 16 then s.regs (dregOf k) else 0

theorem dround_falls : dround.all Instr.falls = true := by decide

end M0Crypto.Release.ChaCha20Round
