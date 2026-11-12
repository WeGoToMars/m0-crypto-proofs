import M0Crypto.Release.Blake2sStreamBridge

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release.Blake2sStream

open M0Crypto.Armv6M (Mem read32)
open M0Crypto.Release.Blake2s (wd)
open M0Crypto.Spec.Blake2s

theorem bytes_read32 (m : Mem) (a : BitVec 32) :
    bytesOfWord (read32 m a) = [m a, m (a + 1#32), m (a + 2#32), m (a + 3#32)] := by
  rw [read32_wob, bytesOfWord_eq, wob]
  have e0 : (m (a + 3#32) ++ m (a + 2#32) ++ m (a + 1#32) ++ m a).extractLsb' 0 8 = m a :=
    BitVec.extractLsb'_append_eq_right
  have e1 : (m (a + 3#32) ++ m (a + 2#32) ++ m (a + 1#32) ++ m a).extractLsb' 8 8 = m (a + 1#32) := by
    rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
    exact BitVec.extractLsb'_append_eq_right
  have e2 : (m (a + 3#32) ++ m (a + 2#32) ++ m (a + 1#32) ++ m a).extractLsb' 16 8 = m (a + 2#32) := by
    rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]
    exact BitVec.extractLsb'_append_eq_right
  have e3 : (m (a + 3#32) ++ m (a + 2#32) ++ m (a + 1#32) ++ m a).extractLsb' 24 8 = m (a + 3#32) := by
    rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]
    exact BitVec.extractLsb'_append_eq_left
  rw [e0, e1, e2, e3]

theorem bytesAt_words (m : Mem) : ∀ (k : Nat) (p : BitVec 32),
    bytesAt m p (4 * k) = (List.range k).flatMap (fun i => bytesOfWord (wd m p i)) := by
  intro k
  induction k with
  | zero => intro p; simp [bytesAt]
  | succ k ih =>
    intro p
    rw [show 4 * (k + 1) = (((4 * k + 1) + 1) + 1) + 1 by omega]
    simp only [bytesAt_succ]
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have e : p + 1#32 + 1#32 + 1#32 + 1#32 = p + 4#32 := by bv_omega
    have e1 : p + 1#32 + 1#32 = p + 2#32 := by bv_omega
    have e2 : p + 2#32 + 1#32 = p + 3#32 := by bv_omega
    rw [e, e1, e2, ih (p + 4#32)]
    have h0 : wd m p 0 = read32 m p := by
      unfold wd; congr 1; bv_omega
    rw [h0, bytes_read32]
    simp only [List.cons_append, List.nil_append]
    have f : ∀ i, wd m (p + 4#32) i = wd m p (i + 1) := by
      intro i; unfold wd; congr 1; bv_omega
    simp only [Function.comp, f]

theorem bytesAt_digest (m : Mem) (c : BitVec 32) (H : Array (BitVec 32)) (hs : H.size = 8)
    (h : ∀ i < 8, read32 m (c + BitVec.ofNat 32 (4 * i)) = H[i]!) :
    bytesAt m c 32 = digestOf H := by
  rw [show 32 = 4 * 8 from rfl, bytesAt_words]
  unfold digestOf
  have : H.toList.take 8 = (List.range 8).map (fun i => H[i]!) := by
    apply List.ext_getElem
    · simp [hs]
    · intro i h1 h2
      have : i < 8 := by simpa [hs] using h1
      simp [getElem!_pos H i (by omega)]
  rw [this, List.flatMap_map]
  simp only [List.flatMap]
  congr 1
  apply List.map_congr_left; intro i hi
  have := h i (List.mem_range.mp hi)
  show bytesOfWord (read32 m (c + BitVec.ofNat 32 (4 * i))) = _
  rw [this]

end M0Crypto.Release.Blake2sStream
