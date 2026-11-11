import M0Crypto.Release.AeadCode
import M0Crypto.Release.Poly1305Context
set_option linter.unusedSimpArgs false

/-!
Internal calls. `Reach.bl` steps a `bl` of the release bytes; the callee's own
composable theorem (`xor_reach`, `init_reach`, `blocks_reach`, `finish_reach`) then
runs from the resulting state, and returns to `lr &&& ~1`, which `lr_mask`
identifies with the instruction after the `bl`.
-/

namespace M0Crypto.Release
open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- The return address of a `bl` at an even address, with the Thumb bit cleared. -/
theorem lr_mask (y : Word) (hy : y.toNat % 2 = 0) : (y ||| 1#32) &&& ~~~1#32 = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat]
  rcases i with _ | i
  · have : y.getLsbD 0 = false := by
      simp only [BitVec.getLsbD, Nat.testBit_zero]; simp [hy]
    simpa [BitVec.getLsbD_eq_getElem hi] using this
  · have : Nat.testBit 1 (i + 1) = false := by simp [Nat.testBit_succ]
    simp [this]

theorem lr_odd (y : Word) : (y ||| 1#32).getLsbD 0 = true := by
  simp [BitVec.getLsbD_or]

/-- One `bl` at offset `off` to offset `tgt`. -/
theorem Reach.bl {base : Word} {Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat) (imm : BitVec 25)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : Aead.blTarget off imm = BitVec.ofNat 32 tgt)
    (hq : Reach base Wr ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : Reach base Wr s Q := by
  apply Reach.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha)
  rw [show s.pc + 4#32 = base + BitVec.ofNat 32 (off + 4) by rw [hpc, ofNat_add_assoc],
    show base + BitVec.ofNat 32 (off + 4) + imm.signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [← ht, Aead.blTarget, ← ofNat_add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]]
  exact hq

end M0Crypto.Release
