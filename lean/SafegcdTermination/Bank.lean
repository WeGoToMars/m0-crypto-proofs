import SafegcdRow.BatchExec
import SafegcdTermination.RowsRefine

namespace SafegcdTermination.Bank

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.FoldRefine (vec value)
open M0Crypto.Armv6M (State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (ne_of_disj read32_congr)

def addr (sp : Word) (off : Nat) : Word := sp + BitVec.ofNat 32 off

theorem slot_addr (sp : Word) (off i : Nat) :
    slot (addr sp off) i = addr sp (off + 4*i) := by
  simp only [slot, addr, ofNat_add_assoc]

theorem stack_vec (s : State) (o i : Nat) :
    vec s.mem (addr s.sp o) i = stackWord s (o + 4*i) := by
  rw [vec, slot_addr]
  rfl

theorem addr_sep (sp : Word) {a b : Nat} (ha : a < 2^32) (hb : b < 2^32)
    (hn : a ≠ b) : addr sp a ≠ addr sp b := by
  intro he
  have h : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
    unfold addr at he
    bv_omega
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact hn h'

def FrameOk (sp : Word) : Prop := sp.toNat % 4 = 0 ∧ sp.toNat + frameBytes ≤ 2^32

def InSlot (o : Nat) : Prop := o + vectorBytes ≤ frameBytes ∧ o % 4 = 0

theorem addr_nat {sp : Word} (h : FrameOk sp) (o : Nat) (ho : o < frameBytes) :
    (addr sp o).toNat = sp.toNat + o := by
  have hb := h.2
  simp only [addr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  simp only [frameBytes] at hb ho
  rw [Nat.mod_eq_of_lt (by omega : o < 4294967296), Nat.mod_eq_of_lt (by omega)]

theorem in_range {sp : Word} (h : FrameOk sp) {a : Nat} (ha : InSlot a) :
    InRange (addr sp a) := by
  have hn : a < frameBytes := by have := ha.1; change a + 68 ≤ frameBytes at this; omega
  rw [InRange, addr_nat h _ hn]
  have hh := h.2
  have hA := ha.1
  change a + 68 ≤ frameBytes at hA
  omega

theorem aligned {sp : Word} (h : FrameOk sp) {a : Nat} (ha : InSlot a) :
    (addr sp a).toNat % 4 = 0 := by
  have hn : a < frameBytes := by have := ha.1; change a + 68 ≤ frameBytes at this; omega
  rw [addr_nat h _ hn]
  have hs := h.1
  have ha' := ha.2
  omega

def Separate (a b : Nat) : Prop := a + vectorBytes ≤ b ∨ b + vectorBytes ≤ a

theorem separate_nat {sp : Word} (h : FrameOk sp) {a b : Nat}
    (ha : InSlot a) (hb : InSlot b) (hab : Separate a b) :
    (addr sp a).toNat + 68 ≤ (addr sp b).toNat ∨ (addr sp b).toNat + 68 ≤ (addr sp a).toNat := by
  have hA := ha.1
  have hB := hb.1
  change a + 68 ≤ b ∨ b + 68 ≤ a at hab
  change a + 68 ≤ frameBytes at hA
  change b + 68 ≤ frameBytes at hB
  rw [addr_nat h _ (by omega), addr_nat h _ (by omega)]
  omega

theorem row_alias {sp : Word} (h : FrameOk sp) {a b : Nat}
    (ha : InSlot a) (hb : InSlot b) (hab : a = b ∨ Separate a b) :
    Aliases (addr sp a) (addr sp b) := by
  rcases hab with rfl | hsep
  · exact .inl rfl
  · exact .inr (separate_nat h ha hb hsep)

def WritesOnly (m m' : Mem) (a : Word) (n : Nat) : Prop :=
  ∀ x, (∀ i < n, x ≠ a + BitVec.ofNat 32 i) → m' x = m x

theorem read_vec_disjoint {m m' : Mem} {sp : Word} {a b : Nat} (h : FrameOk sp)
    (ha : InSlot a) (hb : InSlot b) (hd : Separate a b)
    (hm : WritesOnly m m' (addr sp a) vectorBytes) (i : Nat) (hi : i < 17) :
    vec m' (addr sp b) i = vec m (addr sp b) i := by
  apply read32_congr
  intro j hj
  apply hm
  intro l hl
  unfold slot
  rw [ofNat_add_assoc]
  have hL : l < 68 := hl
  exact (ne_of_disj (in_range h ha) (in_range h hb) (separate_nat h ha hb hd)
    hL (by omega : 4*i+j < 68)).symm

theorem value_disjoint {m m' : Mem} {sp : Word} {a b : Nat} (h : FrameOk sp)
    (ha : InSlot a) (hb : InSlot b) (hd : Separate a b)
    (hm : WritesOnly m m' (addr sp a) vectorBytes) :
    value m' (addr sp b) = value m (addr sp b) := by
  apply weighted_congr
  intro i hi
  simp only [limb, read_vec_disjoint h ha hb hd hm i hi]

theorem formed_disjoint {m m' : Mem} {sp : Word} {a b : Nat} (h : FrameOk sp)
    (ha : InSlot a) (hb : InSlot b) (hd : Separate a b)
    (hm : WritesOnly m m' (addr sp a) vectorBytes)
    (hw : VecWellFormed (vec m (addr sp b))) : VecWellFormed (vec m' (addr sp b)) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [read_vec_disjoint h ha hb hd hm i (by omega)]
    exact hw.1 i hi
  · rw [read_vec_disjoint h ha hb hd hm 16 (by decide)]
    exact hw.2

end SafegcdTermination.Bank
