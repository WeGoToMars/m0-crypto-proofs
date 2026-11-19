import SafegcdTermination.RunLoop
import M0Crypto.Release.FrameBase

namespace SafegcdTermination.Literal

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.RunRows SafegcdTermination.LoopLinks
open SafegcdTermination.BatchSlots (row)
open SafegcdTermination.RunRow (rowLit)

open M0Crypto.Armv6M (State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj lit_addr ne_of_disj)

set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

def codeWord (bs : List (BitVec 8)) (off : Nat) : Word :=
  bs.getD (off+3) 0 ++ bs.getD (off+2) 0 ++ bs.getD (off+1) 0 ++ bs.getD off 0

theorem read32_code {m : Mem} {base : Word} {bs : List (BitVec 8)} (h : CodeAt m base bs)
    (off : Nat) (hOff : off+4 ≤ bs.length) :
    read32 m (base + BitVec.ofNat 32 off) = codeWord bs off := by
  simp only [read32, codeWord]
  rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl,
    show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, show (3#32 : Word) = BitVec.ofNat 32 3 from rfl,
    ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc, h off (by omega), h (off+1) (by omega),
    h (off+2) (by omega), h (off+3) (by omega)]
  simp [List.getD_eq_getElem?_getD, show off < bs.length by omega, show off+1 < bs.length by omega,
    show off+2 < bs.length by omega, show off+3 < bs.length by omega]

def litSite (o : Nat) (r : RowCall) : Nat := o + seqSize (prepareRow r) + seqSize correctionPrefix

def litOff (q : Targets) (o : Nat) (r : RowCall) : Nat :=
  (litSite o r + 4) / 4 * 4 + (rowLit q o r).toNat * 4

/-- A word-aligned base gives the same literal offset even across modular
    address addition. -/
theorem literal_address_aligned (base : Word) (q : Targets) (o : Nat) (r : RowCall)
    (hb : base.toNat % 4 = 0) :
    literalAt base q o r = base + BitVec.ofNat 32 (litOff q o r) := by
  unfold literalAt litOff litSite
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, M0Crypto.Release.Frame.and_not3_toNat]
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem literal_address (base : Word) (q : Targets) (o : Nat) (r : RowCall)
    (hb : base.toNat % 4 = 0) (hl : base.toNat + litOff q o r + 4 ≤ 2^32) :
    literalAt base q o r = base + BitVec.ofNat 32 (litOff q o r) := by
  have h := lit_addr base hb (litSite o r) (rowLit q o r).toNat (by unfold litOff at hl; omega)
  simp only [literalAt, litOff, litSite] at h ⊢
  rw [Nat.mul_comm 4 (rowLit q o r).toNat]
  simpa only [ofNat_add_assoc] using h

def LiteralLinks (bs : List (BitVec 8)) (q : Targets) (entry done : Nat) : Prop :=
  q.literal+4 ≤ bs.length ∧ codeWord bs q.literal = 2587#32 ∧
    ∀ i : Fin 3, ∀ j : Fin 4, (row i j).modular = true →
      litOff q (rowPc q (firstRow q (phaseAt q entry done i) (phases i)) i j.val) (row i j) = q.literal

theorem literal_of_link {code : List (BitVec 8)} {q : Targets} {entry done : Nat} {base : Word} {s : State}
    (h : LiteralLinks code q entry done) (hb : base.toNat % 4 = 0) (hc : CodeAt s.mem base code)
    (hs : Disj base code.length s.sp frameBytes) (i : Fin 3) :
    LiteralAtRows s base q (firstRow q (phaseAt q entry done i) (phases i)) i := by
  intro j hm
  let r := row i j
  let o := rowPc q (firstRow q (phaseAt q entry done i) (phases i)) i j.val
  have hL : litOff q o r = q.literal := h.2.2 i j hm
  have hBound := h.1
  have hW := hs.1
  have e := literal_address base q o r hb (by rw [hL]; omega)
  change read32 s.mem (literalAt base q o r) = 2587#32 ∧ _
  rw [e,hL]
  refine ⟨(read32_code hc _ h.1).trans h.2.1, fun a ha b hb' => ?_⟩
  rw [ofNat_add_assoc]
  exact ne_of_disj hs.1 hs.2.1 hs.2.2 (by omega) hb'

end SafegcdTermination.Literal
