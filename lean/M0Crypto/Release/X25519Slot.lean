import M0Crypto.Release.X25519Comb

/-!
The 8-word product slot of `mul128` and `sqr128`.

Both macros leave a 256-bit product partly in memory at an 8-word slot `a`: words 0 and 1
stay where the first half-product put them, and `combine128` (or `combine128sq`) stores
`cregs` at offset `coff`. `SlotOut` states this as word reads, plus memory unchanged outside
the slot; it is what the callers (`combine_reduce` and the routine frames) read back.
`slotOut_store` proves it from the macro's last store over any memory that has the two low
words and agrees with the start outside the slot.
-/

namespace M0Crypto.Release.X25519Slot
open M0Crypto.Armv6M (Word Reg LowReg State read32 Mem)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Comb (coff cregs)

/-- Word `i` of the buffer at `a`. -/
def ld (m : Mem) (a : Word) (i : Nat) : Word := read32 m (a + BitVec.ofNat 32 (4 * i))

/-- A word read outside a word store. -/
theorem read32_storeWords_disj (m : Mem) (a b : Word) (ws : List Word) {n : Nat}
    (hd : Frame.Disj a n b (4 * ws.length)) (i : Nat) (hi : 4 * i + 4 ≤ n) :
    read32 (storeWords m b ws) (a + BitVec.ofNat 32 (4 * i)) =
      read32 m (a + BitVec.ofNat 32 (4 * i)) := by
  apply Frame.read32_congr
  intro q hq
  apply storeWords_other
  intro j q' hj hq' e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  obtain ⟨h1, h2, h3⟩ := hd
  omega

/-- Word `i` of a word store. -/
theorem ld_store_same (m : Mem) (a : Word) (ws : List Word) (i : Nat) (hi : i < ws.length)
    (hl : ws.length ≤ 2 ^ 28) : ld (storeWords m a ws) a i = ws[i] :=
  Frame.read32_storeWords_same m a ws i hi hl

/-- A store inside the slot leaves memory outside it unchanged. -/
theorem storeWords_frame (m : Mem) (a : Word) (o : Nat) (ws : List Word)
    (h : o + 4 * ws.length ≤ 32) (y : Word) (hy : ∀ i < 32, y ≠ a + BitVec.ofNat 32 i) :
    storeWords m (a + BitVec.ofNat 32 o) ws y = m y := by
  apply storeWords_other
  intro i q hi hq
  rw [ofNat_add_assoc, ofNat_add_assoc]
  exact hy _ (by omega)

/-- The product slot at `a` in `m`, against the start memory `m0`. -/
def SlotOut (m0 m : Mem) (a : Word) (direct : Bool) (l0 l1 : Word) (t : State) : Prop :=
  ld m a 0 = l0 ∧ ld m a 1 = l1 ∧
  (∀ j (hj : j < (cregs direct t).length),
    ld m (a + BitVec.ofNat 32 (coff direct)) j = (cregs direct t)[j]) ∧
  ∀ y, (∀ i < 32, y ≠ a + BitVec.ofNat 32 i) → m y = m0 y

theorem slotOut_store (m0 m1 : Mem) (a : Word) (ha : a.toNat + 32 ≤ 2 ^ 32) (direct : Bool)
    (l0 l1 : Word) (t : State) (h0 : ld m1 a 0 = l0) (h1 : ld m1 a 1 = l1)
    (hf : ∀ y, (∀ i < 32, y ≠ a + BitVec.ofNat 32 i) → m1 y = m0 y) :
    SlotOut m0 (storeWords m1 (a + BitVec.ofNat 32 (coff direct)) (cregs direct t)) a direct
      l0 l1 t := by
  have hlen : 4 * (cregs direct t).length + coff direct ≤ 32 := by
    cases direct <;> simp [cregs, coff]
  have hd : Frame.Disj a 8 (a + BitVec.ofNat 32 (coff direct)) (4 * (cregs direct t).length) := by
    have hc : 8 ≤ coff direct := by cases direct <;> simp [coff]
    refine ⟨by omega, ?_, ?_⟩ <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  refine ⟨?_, ?_, fun j hj => ld_store_same _ _ _ j hj (by omega), fun y hy => ?_⟩
  · unfold ld; rw [read32_storeWords_disj _ _ _ _ hd 0 (by omega)]; exact h0
  · unfold ld; rw [read32_storeWords_disj _ _ _ _ hd 1 (by omega)]; exact h1
  · rw [storeWords_frame _ _ _ _ (by omega) y hy]; exact hf y hy

end M0Crypto.Release.X25519Slot
