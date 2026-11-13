import M0Crypto.Release.ConstantTime.MemoryStep
import M0Crypto.Release.ConstantTime.EntriesDefs

/-! Contract-based separation of writes contained in caller buffers. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Release.Frame (Disj)

/-- An access contained in the second disjoint region remains disjoint from
the first region. The positive width rules out an endpoint represented by a
wrapped machine address. -/
theorem disj_buffer_subrange {a b : Word} {n len offset width : Nat}
    (hd : Disj a n b len) (hwidth : 0 < width) (hbound : offset + width ≤ len) :
    Disj a n (b + BitVec.ofNat 32 offset) width := by
  have haddr : (b + BitVec.ofNat 32 offset).toNat = b.toNat + offset := by
    apply M0Crypto.Release.Frame.toNat_add_ofNat
    obtain ⟨_, hb, _⟩ := hd
    omega
  obtain ⟨ha, hb, hsep⟩ := hd
  unfold Disj
  rw [haddr]
  exact ⟨ha, by omega, by omega⟩

/-- Separation is symmetric. -/
theorem disj_symm {a b : Word} {n m : Nat} (h : Disj a n b m) : Disj b m a n := by
  obtain ⟨ha, hb, hs⟩ := h
  exact ⟨hb, ha, hs.symm⟩

/-- A write within a buffer disjoint from both regions is disjoint from each. -/
theorem buffer_subrange_separated {code stack buf : Word}
    {codeSize stackSize len offset width : Nat}
    (hc : Disj code codeSize buf len) (hs : Disj buf len stack stackSize)
    (hw : 0 < width) (hb : offset + width ≤ len) :
    Disj code codeSize (buf + BitVec.ofNat 32 offset) width ∧
    Disj stack stackSize (buf + BitVec.ofNat 32 offset) width :=
  ⟨disj_buffer_subrange hc hw hb, disj_buffer_subrange (disj_symm hs) hw hb⟩

/-- Every modeled memory operation accesses at least one byte. -/
theorem memOp_width_pos (op : M0Crypto.Thumb.MemOp) : 0 < op.width := by
  cases op <;> decide

/-- First and last byte bounds imply containment of a positive-width access,
provided the permitted buffer leaves room for that width in the address space. -/
theorem buffer_range_of_endpoints (buf a : Word) (len width : Nat) (hw : 0 < width)
    (hlen : len + width ≤ 2 ^ 32)
    (hfirst : (a - buf).toNat < len)
    (hlast : (a + BitVec.ofNat 32 (width - 1) - buf).toNat < len) :
    (a - buf).toNat + width ≤ len := by
  have heq : a + BitVec.ofNat 32 (width - 1) - buf =
      (a - buf) + BitVec.ofNat 32 (width - 1) := by bv_omega
  rw [heq, BitVec.toNat_add] at hlast
  have hm : (BitVec.ofNat 32 (width - 1)).toNat = width - 1 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm] at hlast
  omega

end M0Crypto.Release.ConstantTime
