import M0Crypto.Release.Reach
import M0Crypto.Release.TraceSpec
import M0Crypto.Release.FrameBase

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

/-- Code bytes carry over to any memory that agrees on the code range. -/
theorem codeAt_of_agree {m m' : Mem} (h : Thumb.CodeAt m 0 B)
    (hm : ∀ a : Word, a.toNat < Artifacts.Release.size → m' a = m a) : Thumb.CodeAt m' 0 B := by
  intro i hi
  have hi' : i < Artifacts.Release.size := by rw [B_len] at hi; exact hi
  have e : (0 + BitVec.ofNat 32 i : Word).toNat = i := by
    have h0 : (0 : Word).toNat = 0 := rfl
    have : i < 2 ^ 32 := by unfold Artifacts.Release.size at hi'; omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
  rw [hm _ (by rw [e]; exact hi')]
  exact h i hi

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

/-! ## Interrupts -/

/-- A handler that zeroes the `K` bytes below SP and increments the byte at `a`, a counter of its
own. -/
def tickBelowSp (K : Nat) (a : Word) (_ : Nat) (s : State) : State :=
  { s with mem := fun y =>
      if Region (s.sp - BitVec.ofNat 32 K) K y then 0 else if y = a then s.mem y + 1 else s.mem y }

/-- `HandlerRoom` and `Handlers` of `tickBelowSp K a`, from regions that cover `P`, each separated
from the `K` bytes below the window and from `a`. -/
theorem interruptWitness_of {K n : Nat} {sp0 a : Word} {P : Word → Prop} (rs : List (Word × Nat))
    (hlo : n + K ≤ sp0.toNat) (hP : ∀ y, P y → ∃ r ∈ rs, Region r.1 r.2 y)
    (hd : ∀ r ∈ rs,
      Frame.Disj r.1 r.2 (sp0 - BitVec.ofNat 32 (n + K)) K ∧ Frame.Disj r.1 r.2 a 1) :
    TraceSpec.HandlerRoom K n sp0 P ∧ TraceSpec.Handlers K P (tickBelowSp K a) := by
  have hne : ∀ (r : Word × Nat) b m, Frame.Disj r.1 r.2 b m → ∀ y, Region r.1 r.2 y →
      ¬ Region b m y := by
    intro r b m hd y hry hy
    obtain ⟨o, ho, rfl⟩ := Region.exists hry
    obtain ⟨q, hq, e⟩ := Region.exists hy
    obtain ⟨h1, h2, h3⟩ := hd
    exact Frame.ne_of_disj h1 h2 h3 ho hq e
  refine ⟨⟨hlo, fun y hy hp => ?_⟩, fun _ s => ⟨rfl, rfl, rfl, rfl, rfl, fun y ⟨hp, hk⟩ => ?_⟩⟩
  · obtain ⟨r, hr, hry⟩ := hP y hp
    exact hne r _ _ (hd r hr).1 y hry hy
  · obtain ⟨r, hr, hry⟩ := hP y hp
    have hya : y ≠ a := fun h => hne r _ _ (hd r hr).2 y hry (by rw [h]; simp)
    show (if _ then _ else _) = _
    rw [ite_eq_right hk, ite_eq_right hya]

end M0Crypto.Release.NonVacuity
