import M0Crypto.Release.ChaCha20Xor
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt

/-!
# Non-vacuity of the entry contracts

A theorem whose hypotheses no real call can satisfy is true and useless. For each
function this file gives one concrete call (registers, memory with the release code at address
0, buffers and stack arguments) and proves that it meets the hypothesis shared by all of the
function's headline theorems (`ChaCha20Xor.Pre`, `Aead.APre`). Each witness is then passed to
its correctness theorem (`example`s at the end).

The calls are chosen to exercise the cases where an over-strong precondition would hide:
in-place operation, unaligned buffers and a non-empty message.

All witnesses are checked by kernel evaluation (`decide +kernel`) of the concrete facts.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj Ctx Valid)
open M0Crypto.Release.Aead (ACall AValid ABuf AEntry)

/-! ## Concrete memory and registers -/

/-- Little-endian bytes of a 32-bit value. -/
def le32 (w : Nat) : List (BitVec 8) := (List.range 4).map fun i => BitVec.ofNat 8 (w / 256 ^ i)

/-- The release code at address 0, the given regions `(start, bytes)` above it, zeros
elsewhere. -/
def memOf (regions : List (Nat × List (BitVec 8))) : Mem := fun a =>
  if a.toNat < Artifacts.Release.size then B.getD a.toNat 0
  else match regions.find? (fun r => decide (r.1 ≤ a.toNat ∧ a.toNat < r.1 + r.2.length)) with
    | some r => r.2.getD (a.toNat - r.1) 0
    | none => 0

theorem codeAt (rs : List (Nat × List (BitVec 8))) : Thumb.CodeAt (memOf rs) 0 B := by
  intro i hi
  have hi' : i < Artifacts.Release.size := by rw [B_len] at hi; exact hi
  have e : (0 + BitVec.ofNat 32 i).toNat = i := by
    have : i < 2 ^ 32 := by unfold Artifacts.Release.size at hi'; omega
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
  show (if _ then _ else _) = _
  simp only [e, hi', ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- Entry SP of every witness call. -/
def sp0 : Nat := 0x20001000

/-- Registers of a call: PC, r0-r3, SP = `sp0`, LR = 0x00010001 (Thumb, outside the code). -/
def regsOf (pc r0 r1 r2 r3 : Nat) : Reg → Word := fun r =>
  if r = 0 then BitVec.ofNat 32 r0 else if r = 1 then BitVec.ofNat 32 r1
  else if r = 2 then BitVec.ofNat 32 r2 else if r = 3 then BitVec.ofNat 32 r3
  else if r = 13 then BitVec.ofNat 32 sp0 else if r = 14 then 0x00010001#32
  else if r = 15 then BitVec.ofNat 32 pc else 0#32

def stOf (m : Mem) (rg : Reg → Word) : State := ⟨rg, false, false, false, false, m⟩

/-- The return address lies outside the code. -/
theorem ret_out :
    ∀ i < Artifacts.Release.size, (0x00010001#32 : Word) &&& ~~~1#32 ≠ 0 + BitVec.ofNat 32 i := by
  intro i hi heq
  have := congrArg BitVec.toNat heq
  simp at this
  unfold Artifacts.Release.size at hi
  omega

/-! ## ChaCha20: in place, 100 bytes at an odd address, counter 1 -/

def chMem : Mem := memOf [(sp0, le32 0x20000340 ++ le32 1)]

def chCtx : Frame.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000401#32, 100#32, 0x20000300#32, 0x20000340#32,
   1#32, chMem, regsOf 0 0x20000401 0x20000401 100 0x20000300⟩

theorem xor_correct_nonvacuous : ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, Frame.Ctx.fp, chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, Artifacts.Release.size]; decide +kernel)

/-! ## AEAD: in place, 100 bytes at an odd address, 13-byte AAD, unaligned tag -/

def aMem : Mem :=
  memOf [(sp0, le32 0x20000500 ++ le32 13 ++ le32 0x20000300 ++ le32 0x20000340)]

def aCall (off : Nat) : ACall :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000483#32, 0x20000401#32, 100#32, 0x20000500#32,
   13#32, 0x20000300#32, 0x20000340#32, aMem, regsOf off 0x20000401 0x20000483 0x20000401 100⟩

local macro "aead_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide +kernel, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, aCall, Artifacts.Release.size]; decide +kernel)))

theorem encrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) := by
  aead_witness

theorem decrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.decOff) Aead.decOff (stOf aMem (aCall Aead.decOff).regs0) := by
  aead_witness

/-! ## Each witness fits its theorem -/

example := ChaCha20Xor.xor_correct _ _ xor_correct_nonvacuous
example := Aead.encrypt_correct _ _ encrypt_correct_nonvacuous
example := Aead.decrypt_correct _ _ decrypt_correct_nonvacuous

end M0Crypto.Release.NonVacuity
