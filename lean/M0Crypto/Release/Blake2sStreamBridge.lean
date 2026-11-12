import M0Crypto.Spec.Blake2sStream
import M0Crypto.Release.Blake2sCompressSpec

set_option linter.unusedSimpArgs false

/-!
# Machine memory ↔ specification bytes

`bytesAt m p n` is the byte list at `p`. The lemmas relate the little-endian words the assembly
reads (`wd`, `read32`) to the byte lists the streaming specification works on.
-/

namespace M0Crypto.Release.Blake2sStream

open M0Crypto.Armv6M (Mem read32)
open M0Crypto.Release.Blake2s (wd arr8 arr16)
open M0Crypto.Spec.Blake2s

/-- The `n` bytes starting at `p`. -/
def bytesAt (m : Mem) (p : BitVec 32) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m (p + BitVec.ofNat 32 i)

theorem bytesAt_length (m : Mem) (p : BitVec 32) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_succ (m : Mem) (p : BitVec 32) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1#32) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    congr 1
    bv_omega

theorem bytesAt_congr {m1 m2 : Mem} {p : BitVec 32} {n : Nat}
    (h : ∀ i < n, m1 (p + BitVec.ofNat 32 i) = m2 (p + BitVec.ofNat 32 i)) :
    bytesAt m1 p n = bytesAt m2 p n := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem bytesAt_append (m : Mem) (p : BitVec 32) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 32 a) b := by
  induction a generalizing p with
  | zero =>
    simp only [Nat.zero_add, bytesAt, List.range_zero, List.map_nil, List.nil_append]
    congr 1
    funext i
    congr 1
    bv_omega
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, bytesAt_succ, bytesAt_succ, ih, List.cons_append]
    congr 3
    bv_omega

/-! ### Words -/

theorem wob (b0 b1 b2 b3 : BitVec 8) : wordOfBytes b0 b1 b2 b3 = b3 ++ b2 ++ b1 ++ b0 := by
  unfold wordOfBytes
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  have e1 : i - 8 - 8 = i - 16 := by omega
  have e2 : i - 16 - 8 = i - 24 := by omega
  rw [e1, e2]
  by_cases h1 : i < 8
  · simp [h1, show i < 32 by omega, show i < 16 by omega, show i < 24 by omega]
  by_cases h2 : i < 16
  · simp [h1, h2, show i < 32 by omega, show i < 24 by omega, show i - 8 < 8 by omega,
      BitVec.getLsbD_of_ge b0 i (by omega), show i - 8 < 32 by omega]
  by_cases h3 : i < 24
  · simp [h1, h2, h3, show i < 32 by omega, show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega,
      BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
      show i - 16 < 32 by omega, BitVec.getLsbD_eq_getElem (show i - 16 < 8 by omega)]
  · simp [h1, h2, h3, show i < 32 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show i - 24 < 8 by omega, show i - 24 < 32 by omega,
      BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
      BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_eq_getElem (show i - 24 < 8 by omega)]

/-- A word is the concatenation of its four little-endian bytes. -/
theorem bow (w : BitVec 32) :
    w = w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have e1 : i - 8 - 8 = i - 16 := by omega
  have e2 : i - 16 - 8 = i - 24 := by omega
  rw [e1, e2]
  by_cases h1 : i < 8
  · simp [h1, hi]
  by_cases h2 : i < 16
  · simp [h1, hi, show i - 8 < 8 by omega]; congr 1; omega
  by_cases h3 : i < 24
  · simp [h1, hi, show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega]; congr 1; omega
  · simp [h1, hi, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega, show i - 24 < 8 by omega]
    congr 1; omega

theorem read32_wob (m : Mem) (a : BitVec 32) :
    read32 m a = wordOfBytes (m a) (m (a + 1#32)) (m (a + 2#32)) (m (a + 3#32)) := by
  rw [wob]; rfl

/-- The little-endian bytes of a word, as `bytesOfWord` lists them. -/
theorem bytesOfWord_eq (w : BitVec 32) :
    bytesOfWord w = [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8] := rfl

theorem wordsOfBytes_bytesAt (m : Mem) : ∀ (k : Nat) (p : BitVec 32),
    wordsOfBytes (bytesAt m p (4 * k)) = (List.range k).map (wd m p) := by
  intro k
  induction k with
  | zero => intro p; simp [bytesAt, wordsOfBytes]
  | succ k ih =>
    intro p
    rw [show 4 * (k + 1) = (((4 * k + 1) + 1) + 1) + 1 by omega]
    simp only [bytesAt_succ]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have e : p + 1#32 + 1#32 + 1#32 + 1#32 = p + 4#32 := by bv_omega
    rw [e]
    simp only [wordsOfBytes]
    have e1 : p + 1#32 + 1#32 = p + 2#32 := by bv_omega
    have e2 : p + 2#32 + 1#32 = p + 3#32 := by bv_omega
    rw [e1, e2, ih (p + 4#32)]
    congr 1
    · unfold wd
      rw [read32_wob]
      have : p + BitVec.ofNat 32 (4 * 0) = p := by bv_omega
      rw [this]
    · apply List.map_congr_left
      intro i _
      unfold wd
      simp only [Function.comp]
      congr 1
      bv_omega

/-- The sixteen words at `p` are the block words of any byte list whose padded form is the
64 bytes at `p`. -/
theorem arr16_wd (m : Mem) (p : BitVec 32) (l : List (BitVec 8)) (h : bytesAt m p 64 = pad l) :
    arr16 (wd m p) = blockWords l := by
  have e := wordsOfBytes_bytesAt m 16 p
  rw [show 4 * 16 = 64 from rfl, h] at e
  unfold blockWords
  rw [e]
  rfl

theorem arr8_eq (f : Nat → BitVec 32) (a : Array (BitVec 32)) (hsz : a.size = 8)
    (h : ∀ i < 8, f i = a[i]!) : arr8 f = a := by
  apply Array.ext
  · simp [arr8, hsz]
  · intro i h1 h2
    have hi : i < 8 := by simpa [hsz] using h2
    have := h i hi
    rw [getElem!_pos a i h2] at this
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this

/-- The chain value, byte counter and pending bytes of a streaming state (everything in the
context except the `used` field). -/
structure CtxNU (m : Mem) (c : BitVec 32) (st : State) : Prop where
  hsz : st.h.size = 8
  h : ∀ i < 8, read32 m (c + BitVec.ofNat 32 (4 * i)) = st.h[i]!
  clo : read32 m (c + 32#32) = BitVec.ofNat 32 st.count
  chi : read32 m (c + 36#32) = BitVec.ofNat 32 (st.count / 2 ^ 32)
  cnt : st.count < 2 ^ 64
  plen : st.pending.length ≤ 64
  buf : bytesAt m (c + 40#32) st.pending.length = st.pending

/-- The whole context, including the `used` field. -/
structure Ctx (m : Mem) (c : BitVec 32) (st : State) : Prop extends CtxNU m c st where
  used : read32 m (c + 104#32) = BitVec.ofNat 32 st.pending.length

end M0Crypto.Release.Blake2sStream
