import M0Crypto.Release.Blake2sRoundSpec

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Mem read32)
open M0Crypto.Spec.Blake2s (IV initVec compress rounds)

/-- The `i`-th little-endian word at address `a`. -/
def wd (m : Mem) (a : Word) (i : Nat) : Word := read32 m (a + BitVec.ofNat 32 (4 * i))

/-- The eight chain words at `a`. -/
def hv (m : Mem) (a : Word) : Array Word :=
  #[wd m a 0, wd m a 1, wd m a 2, wd m a 3, wd m a 4, wd m a 5, wd m a 6, wd m a 7]

/-- The sixteen message words at `a`. -/
def mv (m : Mem) (a : Word) : Array Word :=
  #[wd m a 0, wd m a 1, wd m a 2, wd m a 3, wd m a 4, wd m a 5, wd m a 6, wd m a 7,
    wd m a 8, wd m a 9, wd m a 10, wd m a 11, wd m a 12, wd m a 13, wd m a 14, wd m a 15]

/-- The initial working vector the prologue builds, as a function. -/
def v0 (hm : Nat → Word) (t0 t1 f0 : Word) : Nat → Word := fun k =>
  if k < 8 then hm k
  else if k = 8 then 0x6A09E667#32 else if k = 9 then 0xBB67AE85#32
  else if k = 10 then 0x3C6EF372#32 else if k = 11 then 0xA54FF53A#32
  else if k = 12 then 0x510E527F#32 ^^^ t0 else if k = 13 then 0x9B05688C#32 ^^^ t1
  else if k = 14 then 0x1F83D9AB#32 ^^^ f0 else 0x5BE0CD19#32

theorem arr16_v0 (m : Mem) (a : Word) (t : Nat) (f : Bool) :
    arr16 (v0 (wd m a) (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32))
      (if f then 0xFFFFFFFF#32 else 0#32)) = initVec (hv m a) t f := by
  cases f <;> rfl

open M0Crypto.Release.Blake2sCode (sg)

/-- The vector after `n` rounds, in the assembly's order of the `G`s. -/
def Vr (v m : Nat → Word) : Nat → Nat → Word
  | 0 => v
  | n + 1 => roundF (Vr v m n) m (sg n)

theorem arr16_Vr (v m : Nat → Word) : ∀ n, n ≤ 10 →
    arr16 (Vr v m n) = rounds (arr16 m) n (arr16 v)
  | 0, _ => rfl
  | n + 1, h => by
    have ih := arr16_Vr v m n (by omega)
    show arr16 (roundF (Vr v m n) m (sg n)) = M0Crypto.Spec.Blake2s.round (rounds (arr16 m) n (arr16 v)) (arr16 m) n
    rw [← ih]
    exact round_spec (Vr v m n) m ⟨n, by omega⟩

/-- Eight chain words as an array. -/
def arr8 (f : Nat → Word) : Array Word := #[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7]

theorem initVec_arr (hm : Nat → Word) (t : Nat) (f : Bool) :
    initVec (arr8 hm) t f = arr16 (v0 hm (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32))
      (if f then 0xFFFFFFFF#32 else 0#32)) := by
  cases f <;> rfl

/-- The RFC compression result, word by word, in terms of the assembly's vector function. -/
theorem compress_get (hm mm : Nat → Word) (t : Nat) (f : Bool) (i : Nat) (hi : i < 8) :
    (compress (arr8 hm) (arr16 mm) t f)[i]! =
      hm i ^^^ Vr (v0 hm (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32))
        (if f then 0xFFFFFFFF#32 else 0#32)) mm 10 i ^^^
      Vr (v0 hm (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32))
        (if f then 0xFFFFFFFF#32 else 0#32)) mm 10 (i + 8) := by
  unfold compress
  rw [initVec_arr, ← arr16_Vr _ _ 10 (by omega)]
  have h8 : ∀ k, k < 8 → (arr8 hm)[k]! = hm k := by
    intro k hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  generalize Vr (v0 hm (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32))
    (if f then 0xFFFFFFFF#32 else 0#32)) mm 10 = V
  show (Array.map (fun j => (arr8 hm)[j]! ^^^ (arr16 V)[j]! ^^^ (arr16 V)[j + 8]!)
    (List.range 8).toArray)[i]! = _
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
  rw [h8 i hi, arr16_get _ i (by omega), arr16_get _ (i + 8) (by omega)]

end M0Crypto.Release.Blake2s
