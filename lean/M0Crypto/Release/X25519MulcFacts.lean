import M0Crypto.Release.X25519MulcChain
import M0Crypto.Release.X25519Routines
import M0Crypto.Release.Field25519Reduce

set_option linter.unusedSimpArgs false

/-!
Facts for the routine proof of `m0c_fe_mulc_add`: the code
pieces at their offsets (`pieces`), the routine's PC region (`inReg`), the literal `60833`
read from the code bytes (`lit_val`), address disjointness, `feVal` as a partial sum, and the
step from a `ReachW` run to the model's `runUntil` when the stop address lies outside the
region of executed PCs (`reachW_runUntil`; the routine's return address is outside the
routine, not outside the artifact).
-/

namespace M0Crypto.Release.X25519MulcFacts
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion RegionWrites StepsOk stepsOk_events_iff WritesTo Region)
open M0Crypto.Release.Frame (Disj lit_addr codeWord read32_code read32_congr toNat_add_ofNat
  sub_ofNat_toNat)
open M0Crypto.Release.X25519MulcEnds (pre pre2 fold fin feMulcAddList_split)
open M0Crypto.Release.Field25519Facts (psum psum_lt)
open M0Crypto.Release.X25519Macros (mulcWord mulcStep feMulcAddList feMulcAddList' feMulcAdd_at mulcLit)
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMulcAdd feMulcAddSize)

/-- The literal's index operand. -/
abbrev lit : BitVec 8 := BitVec.ofNat 8 mulcLit

/-- The routine's code, cut into its pieces at their offsets. -/
theorem pieces :
    let o1 := feMulcAdd + seqSize (pre lit)
    let o2 := o1 + seqSize (mulcWord 7 none 3 4 5)
    let o3 := o2 + seqSize fold
    let o4 := o3 + seqSize (mulcStep 0 3 0)
    let o5 := o4 + seqSize (mulcStep 1 0 3)
    let o6 := o5 + seqSize (mulcStep 2 3 0)
    let o7 := o6 + seqSize (mulcStep 3 0 3)
    let o8 := o7 + seqSize (mulcStep 4 3 0)
    let o9 := o8 + seqSize (mulcStep 5 0 3)
    let o10 := o9 + seqSize (mulcStep 6 3 0)
    let o11 := o10 + seqSize fin
    seqAt B feMulcAdd (pre lit) = true ∧ seqAt B o1 (mulcWord 7 none 3 4 5) = true ∧
      seqAt B o2 fold = true ∧ seqAt B o3 (mulcStep 0 3 0) = true ∧
      seqAt B o4 (mulcStep 1 0 3) = true ∧ seqAt B o5 (mulcStep 2 3 0) = true ∧
      seqAt B o6 (mulcStep 3 0 3) = true ∧ seqAt B o7 (mulcStep 4 3 0) = true ∧
      seqAt B o8 (mulcStep 5 0 3) = true ∧ seqAt B o9 (mulcStep 6 3 0) = true ∧
      seqAt B o10 fin = true ∧ seqAt B o11 [.pop 0 true] = true := by
  intro o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11
  have h := feMulcAdd_at
  rw [feMulcAddList', feMulcAddList_split] at h
  simp only [seqAt_append, seqSize_append, Bool.and_eq_true, ← Nat.add_assoc] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩ := h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

/-- Two disjoint 4-byte words: a write to one keeps the other's read. -/
theorem read32_write32_disj (m : Mem) {a b : Word} (v : Word) (hd : Disj a 4 b 4) :
    read32 (write32 m a v) b = read32 m b := by
  apply read32_congr
  intro k hk
  apply M0Crypto.Armv6M.write32_other
  intro q hq e
  obtain ⟨h1, h2, h3⟩ := hd
  have := congrArg BitVec.toNat e
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

/-- Word `i < 8` of a 32-byte buffer is disjoint from a 4-byte region disjoint from the
buffer. -/
theorem disj_slot {p q : Word} (hd : Disj p 32 q 4) {i : Nat} (hi : i < 8) : Disj q 4 (slot p i) 4 := by
  obtain ⟨h1, h2, h3⟩ := hd
  have e : (slot p i).toNat = p.toNat + 4 * i := toNat_add_ofNat _ _ (by omega)
  exact ⟨h2, by omega, by omega⟩

/-- The literal: the word at `ldr r7, =60833`'s address is `60833` (read from the code bytes),
and the address is aligned. A push below `sp` does not reach it. -/
theorem lit_val {base sp : Word} {m : Mem} (v : Word) (hc : CodeAt m base B) (hb : base.toNat % 4 = 0)
    (hd : Disj base Artifacts.Release.size (sp - 4#32) 4) :
    let L := ((base + BitVec.ofNat 32 (feMulcAdd + seqSize pre2) + 4#32) &&& ~~~3#32) +
      BitVec.ofNat 32 (lit.toNat * 4)
    read32 (write32 m (sp - 4#32) v) L = 60833#32 ∧ L.toNat % 4 = 0 := by
  intro L
  have hl : lit.toNat = mulcLit := by decide
  have k : (feMulcAdd + seqSize pre2 + 4) / 4 * 4 + mulcLit * 4 + 4 ≤ Artifacts.Release.size ∧
      feMulcAdd + seqSize pre2 + 4 + mulcLit * 4 < Artifacts.Release.size := by decide
  have h1 := hd.1
  have e : L = base + BitVec.ofNat 32 ((feMulcAdd + seqSize pre2 + 4) / 4 * 4 + mulcLit * 4) := by
    simp only [L, hl]; exact lit_addr base hb _ _ (by omega)
  have et : L.toNat = base.toNat + ((feMulcAdd + seqSize pre2 + 4) / 4 * 4 + mulcLit * 4) := by
    rw [e]; exact toNat_add_ofNat _ _ (by omega)
  refine ⟨?_, by omega⟩
  rw [read32_write32_disj m v ⟨hd.2.1, by omega, by have := hd.2.2; omega⟩, e, read32_code hc _ k.1]
  decide +kernel

/-- The value split at word 7. -/
theorem psum8 (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 32) :
    psum f 8 / 2 ^ 224 = f 7 ∧ psum f 8 % 2 ^ 224 = psum f 7 := by
  have h := psum_lt hf 7
  have e : psum f 8 = psum f 7 + 2 ^ 224 * f 7 := rfl
  omega

end M0Crypto.Release.X25519MulcFacts
