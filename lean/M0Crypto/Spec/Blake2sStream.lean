import M0Crypto.Spec.Blake2s

/-!
# Streaming lemmas for the implementation's three `update` paths

The assembly never calls `State.push`. It appends a chunk to `pending` when the chunk fits,
flushes a full pending block before more input arrives, and compresses full 64-byte input
blocks in place. These three lemmas are the machine-independent facts the proof of
`m0c_blake2s_update` uses; each says the path agrees with `absorb`.
-/

namespace M0Crypto.Spec.Blake2s

/-- `absorb` of a concatenation is two `absorb`s. -/
theorem absorb_append (s : State) (a b : List Byte) : absorb s (a ++ b) = absorb (absorb s a) b := by
  simp [absorb, List.foldl_append]

/-- A chunk that fits in `pending` is appended without compressing. -/
theorem absorb_fit (k : List Byte) : ∀ (s : State), s.pending.length + k.length ≤ 64 →
    absorb s k = ⟨s.h, s.count, s.pending ++ k⟩ := by
  induction k with
  | nil => intro s _; simp [absorb]
  | cons b k ih =>
    intro s hs
    have hlt : s.pending.length ≠ 64 := by simp at hs; omega
    have h1 : (s.push b).pending.length + k.length ≤ 64 := by
      simp [State.push, hlt] at *; omega
    have := ih (s.push b) h1
    simp only [absorb, List.foldl_cons] at this ⊢
    rw [this]
    simp [State.push, hlt]

/-- A full pending block followed by more input is compressed first (non-final). -/
theorem absorb_flush (s : State) (hp : s.pending.length = 64) (k : List Byte) (hk : k ≠ []) :
    absorb s k = absorb ⟨compress s.h (blockWords s.pending) (s.count + 64) false, s.count + 64, []⟩ k := by
  cases k with
  | nil => exact absurd rfl hk
  | cons b k =>
    simp [absorb, State.push, hp]

/-- With nothing pending, a full 64-byte block followed by more input is compressed straight from
the input (non-final). -/
theorem absorb_direct (h : Array Word) (c : Nat) (k : List Byte) (hk : 64 < k.length) :
    absorb ⟨h, c, []⟩ k =
      absorb ⟨compress h (blockWords (k.take 64)) (c + 64) false, c + 64, []⟩ (k.drop 64) := by
  have e : k = k.take 64 ++ k.drop 64 := (List.take_append_drop 64 k).symm
  have hl : (k.take 64).length = 64 := by simp; omega
  have hd : k.drop 64 ≠ [] := by
    intro h'; have := congrArg List.length h'; simp at this; omega
  have e2 : absorb ⟨h, c, []⟩ k = absorb ⟨h, c, []⟩ (k.take 64 ++ k.drop 64) := by
    rw [List.take_append_drop]
  rw [e2, absorb_append, absorb_fit (k.take 64) ⟨h, c, []⟩ (by simp [hl])]
  rw [absorb_flush _ (by simpa using hl) _ hd]
  simp

end M0Crypto.Spec.Blake2s
