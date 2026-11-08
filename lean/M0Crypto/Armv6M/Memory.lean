import M0Crypto.Armv6M.State

/-!
Little-endian 32-bit word access over the byte-addressed data memory.

`read32 m a` is ARMv6-M `MemU[a, 4]` for a little-endian system on ordinary
memory: byte `a` is bits 7:0. Addresses wrap modulo 2^32 (`Word` arithmetic).
Alignment is checked by the step function, not here.
-/

namespace M0Crypto.Armv6M

abbrev Mem := Word → BitVec 8

def read32 (m : Mem) (a : Word) : Word :=
  m (a + 3#32) ++ m (a + 2#32) ++ m (a + 1#32) ++ m a

def write32 (m : Mem) (a : Word) (v : Word) : Mem := fun x =>
  if x = a then v.extractLsb' 0 8
  else if x = a + 1#32 then v.extractLsb' 8 8
  else if x = a + 2#32 then v.extractLsb' 16 8
  else if x = a + 3#32 then v.extractLsb' 24 8
  else m x

/-- Four little-endian bytes of `v` reassemble to `v`. -/
theorem bytes_reassemble (v : Word) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  repeat' split
  all_goals (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega)

theorem read32_write32_same (m : Mem) (a v : Word) : read32 (write32 m a v) a = v := by
  have h1 : a + 1#32 ≠ a := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h2 : a + 2#32 ≠ a := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h3 : a + 3#32 ≠ a := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h21 : a + 2#32 ≠ a + 1#32 := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h31 : a + 3#32 ≠ a + 1#32 := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h32 : a + 3#32 ≠ a + 2#32 := by
    intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  simp only [read32, write32, h1, h2, h3, h21, h31, h32, ite_true, ite_false]
  exact bytes_reassemble v

/-- A byte outside the four written bytes is unchanged. -/
theorem write32_other (m : Mem) (a v x : Word)
    (h : ∀ k : Nat, k < 4 → x ≠ a + BitVec.ofNat 32 k) : write32 m a v x = m x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [BitVec.add_zero] at h0
  simp [write32, h0, h1, h2, h3]

/-- Byte address `sp + 4*i + p` as a natural number modulo 2^32. -/
theorem slot_toNat (sp : Word) (n : Nat) :
    (sp + BitVec.ofNat 32 n).toNat = (sp.toNat + n % 2 ^ 32) % 2 ^ 32 := by
  simp [BitVec.toNat_add]

/-- Bytes of distinct word slots `sp + 4i` and `sp + 4j` (`i, j < 16`) never coincide
modulo 2^32. -/
theorem slot_byte_ne (sp : Word) (i j p q : Nat) (hi : i < 16) (hj : j < 16)
    (hp : p < 4) (hq : q < 4) (hij : i ≠ j) :
    sp + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 p ≠
      sp + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 q := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- Word slot `i` of a 16-word frame at `sp`. -/
def slot (sp : Word) (i : Nat) : Word := sp + BitVec.ofNat 32 (4 * i)

theorem read32_write32_slot (m : Mem) (sp v : Word) (i j : Nat) (hi : i < 16) (hj : j < 16) :
    read32 (write32 m (slot sp i) v) (slot sp j) =
      if i = j then v else read32 m (slot sp j) := by
  split
  · subst_vars; exact read32_write32_same m _ v
  · rename_i hij
    have hb : ∀ q, q < 4 → write32 m (slot sp i) v (slot sp j + BitVec.ofNat 32 q) =
        m (slot sp j + BitVec.ofNat 32 q) := by
      intro q hq
      apply write32_other
      intro k hk
      exact (slot_byte_ne sp i j k q hi hj hk hq hij).symm
    have h0 := hb 0 (by omega); have h1 := hb 1 (by omega)
    have h2 := hb 2 (by omega); have h3 := hb 3 (by omega)
    simp only [BitVec.add_zero] at h0
    simp only [read32]
    rw [h0, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, h1,
      show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, h2,
      show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, h3]

end M0Crypto.Armv6M
