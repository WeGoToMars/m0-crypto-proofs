import M0Crypto.Release.FrameBase

/-!
The stack frame of the X25519 field routines as a function from word slots to words
.

`FrameOk fp n m0 F m`: the `n` words from `fp` read as `F`, and every byte outside them is as
in `m0`. Stores into the frame update `F` (`write`, `storeWords`); words outside the frame
read as in `m0` (`read_out`, `read_disj`). The frame must not wrap (`fits`).
-/

namespace M0Crypto.Release.X25519Frame

open M0Crypto.Armv6M (Word Mem read32 write32 slot)
open M0Crypto.Thumb (storeWords ofNat_add_assoc)
open M0Crypto.Release.Frame (Disj InFrame read32_congr toNat_add_ofNat)

structure FrameOk (fp : Word) (n : Nat) (m0 : Mem) (F : Nat → Word) (m : Mem) : Prop where
  fits : fp.toNat + 4 * n ≤ 2 ^ 32
  slots : ∀ i < n, read32 m (slot fp i) = F i
  out : ∀ y, ¬ InFrame fp n y → m y = m0 y

/-- `F` with the words `vs` from slot `k`. -/
def upd (F : Nat → Word) (k : Nat) (vs : List Word) : Nat → Word :=
  fun i => if k ≤ i ∧ i < k + vs.length then vs.getD (i - k) 0 else F i

theorem slot_byte (fp : Word) (i p : Nat) : slot fp i + BitVec.ofNat 32 p = fp + BitVec.ofNat 32 (4 * i + p) := by
  simp only [slot, ofNat_add_assoc]

theorem slot_byte_ne {fp : Word} {n i k p q : Nat} (hf : fp.toNat + 4 * n ≤ 2 ^ 32) (hi : i < n)
    (hk : k < n) (hp : p < 4) (hq : q < 4) (hik : i ≠ k) :
    slot fp i + BitVec.ofNat 32 p ≠ slot fp k + BitVec.ofNat 32 q := by
  rw [slot_byte, slot_byte]
  intro h
  have := congrArg BitVec.toNat h
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

theorem inFrame_slot {fp : Word} {n k q : Nat} (hk : k < n) (hq : q < 4) :
    InFrame fp n (slot fp k + BitVec.ofNat 32 q) := ⟨4 * k + q, by omega, slot_byte fp k q⟩

theorem FrameOk.write {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m : Mem}
    (h : FrameOk fp n m0 F m) {k : Nat} (hk : k < n) (v : Word) :
    FrameOk fp n m0 (upd F k [v]) (write32 m (slot fp k) v) := by
  refine ⟨h.fits, fun i hi => ?_, fun y hy => ?_⟩
  · by_cases hik : i = k
    · subst hik; simp [upd, M0Crypto.Armv6M.read32_write32_same]
    · have e : upd F k [v] i = F i := by simp only [upd, List.length_singleton]; split <;> first | rfl | omega
      rw [e, ← h.slots i hi]
      apply read32_congr
      intro p hp
      apply M0Crypto.Armv6M.write32_other
      intro q hq
      exact slot_byte_ne h.fits hi hk hp hq hik
  · rw [M0Crypto.Armv6M.write32_other _ _ _ _ (fun q hq e => hy (by rw [e]; exact inFrame_slot hk hq))]
    exact h.out y hy

theorem upd_cons (F : Nat → Word) (k : Nat) (v : Word) (vs : List Word) :
    upd F k (v :: vs) = upd (upd F k [v]) (k + 1) vs := by
  funext i
  simp only [upd, List.length_cons, List.length_nil]
  by_cases h1 : k + 1 ≤ i ∧ i < k + 1 + vs.length
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
      ite_eq_left_of_eq_true _ _ (eq_true (show k ≤ i ∧ i < k + (vs.length + 1) by omega))]
    obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + j := ⟨i - (k + 1), by omega⟩
    rw [show k + 1 + j - k = j + 1 by omega, show k + 1 + j - (k + 1) = j by omega]
    simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : i = k
    · subst h2
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show i ≤ i ∧ i < i + (vs.length + 1) by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show i ≤ i ∧ i < i + 1 by omega))]
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(k ≤ i ∧ i < k + (vs.length + 1)) by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬(k ≤ i ∧ i < k + 1) by omega))]

theorem FrameOk.storeWords {fp : Word} {n : Nat} {m0 : Mem} :
    ∀ (vs : List Word) {F : Nat → Word} {m : Mem} {k : Nat}, FrameOk fp n m0 F m →
      k + vs.length ≤ n → FrameOk fp n m0 (upd F k vs) (storeWords m (slot fp k) vs)
  | [], F, m, k, h, _ => by
    have : upd F k [] = F := by funext i; simp [upd]; omega
    rw [this]; exact h
  | v :: vs, F, m, k, h, hl => by
    simp only [List.length_cons] at hl
    rw [upd_cons]
    simp only [M0Crypto.Thumb.storeWords]
    have e : slot fp k + 4#32 = slot fp (k + 1) := by
      rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, slot_byte]; rfl
    rw [e]
    exact FrameOk.storeWords vs (h.write (by omega) v) (by omega)

/-- A word whose bytes are all outside the frame reads as in `m0`. -/
theorem FrameOk.read_out {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m : Mem}
    (h : FrameOk fp n m0 F m) {a : Word} (ha : ∀ q < 4, ¬ InFrame fp n (a + BitVec.ofNat 32 q)) :
    read32 m a = read32 m0 a :=
  read32_congr fun q hq => h.out _ (ha q hq)

/-- Word `i` of a buffer disjoint from the frame reads as in `m0`. -/
theorem FrameOk.read_disj {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m : Mem}
    (h : FrameOk fp n m0 F m) {a : Word} {len : Nat} (hd : Disj a len fp (4 * n)) {i : Nat}
    (hi : 4 * i + 4 ≤ len) : read32 m (a + BitVec.ofNat 32 (4 * i)) = read32 m0 (a + BitVec.ofNat 32 (4 * i)) := by
  obtain ⟨h1, h2, h3⟩ := hd
  apply h.read_out
  intro q hq ⟨o, ho, e⟩
  rw [ofNat_add_assoc] at e
  have := congrArg BitVec.toNat e
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

end M0Crypto.Release.X25519Frame
