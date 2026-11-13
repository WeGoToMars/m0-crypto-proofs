import M0Crypto.Release.Reach

/-!
# Non-vacuity witnesses: shared helpers

A theorem whose hypotheses no real call can satisfy is true and useless. Each release asset
has its own witness module (`ChaCha20Poly1305NonVacuity`, `Blake2sNonVacuity`,
`X25519NonVacuity`) giving one concrete call per function, with the asset's release code at
address 0, and passing it to the function's correctness theorem. This module holds the
concrete memory and register helpers they share.

All witnesses are checked by kernel evaluation (`decide +kernel`) of the concrete facts.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)

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

end M0Crypto.Release.NonVacuity
