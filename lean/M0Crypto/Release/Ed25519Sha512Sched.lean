import M0Crypto.Release.Ed25519Sha512Group
import M0Crypto.Release.RoutineBranch

set_option linter.unusedSimpArgs false

/-!
# Macro `schedule`: one masked step

`sched_run`: for any `j < 16` with `r7 = 8 j`, one pass of `schedBody` stores
`schedStep buf j` at word `j` of the buffer at `r6` (`buf` its sixteen words), advances `r7` to
`8 (j + 1)` and sets `Z` exactly when `j + 1 = 16`. The masked offsets `(8 j + 8 a) & 0x78` are
`sched_index`; the four uses of macro `sigma` are `sigma_regs`.
-/

namespace M0Crypto.Release.Ed25519Sha512Sched

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Exec
open M0Crypto.Release.Ed25519Sha512Round
open M0Crypto.Release.Ed25519Sha512Rounds (upd schedStep)
open M0Crypto.Spec.Sha512 (sigma0 sigma1)
open M0Crypto.Proofs (toReg_7)

/-- The two stores of word `j` of the buffer at `b`. -/
def wset (m : Mem) (b : Word) (j : Nat) (x : BitVec 64) : Mem :=
  write32 (write32 m (b + BitVec.ofNat 32 (2 * j * 4)) (loW x)) (b + BitVec.ofNat 32 ((2 * j + 1) * 4)) (hiW x)

theorem ofs_slot (b : Word) (n : Nat) : b + BitVec.ofNat 32 (n * 4) = slot b n := by
  rw [slot, Nat.mul_comm]

theorem wAt_wset (m : Mem) (b : Word) {t j : Nat} (ht : t < 16) (hj : j < 16) (x : BitVec 64) :
    wAt (wset m b j x) b t = if t = j then x else wAt m b t := by
  simp only [wAt, wset, ofs_slot]
  rw [read32_write32_slotN _ _ _ _ _ (by omega) (by omega),
    read32_write32_slotN _ _ _ _ _ (by omega) (by omega),
    read32_write32_slotN _ _ _ _ _ (by omega) (by omega),
    read32_write32_slotN _ _ _ _ _ (by omega) (by omega)]
  by_cases h : t = j
  · subst h; simp
  · simp only [h, ite_false, show ¬ 2 * j + 1 = 2 * t + 1 by omega, show ¬ 2 * j = 2 * t + 1 by omega,
      show ¬ 2 * j + 1 = 2 * t by omega, show ¬ 2 * j = 2 * t by omega]

/-- `(r7 + 8 a) & MASK` with `r7 = 8 j`: the byte offset of word `(j + a) mod 16`. -/
theorem idx (j a : Nat) (hj : j < 16) (ha : a < 16) :
    (BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (BitVec.ofNat 8 (8 * a)).toNat) &&&
      BitVec.ofNat 32 (BitVec.ofNat 8 MASK).toNat = BitVec.ofNat 32 (2 * ((j + a) % 16) * 4) := by
  have e1 : (BitVec.ofNat 8 (8 * a)).toNat = 8 * a := by simp; omega
  have e2 : (BitVec.ofNat 8 MASK).toNat = 0x78 := rfl
  rw [e1, e2, show 2 * ((j + a) % 16) * 4 = 8 * ((j + a) % 16) by omega]
  exact Ed25519Sha512Rounds.sched_index j a hj ha

theorem idx0 (j : Nat) (hj : j < 16) :
    BitVec.ofNat 32 (BitVec.ofNat 8 MASK).toNat &&& BitVec.ofNat 32 (8 * j) = BitVec.ofNat 32 (2 * j * 4) := by
  have h : ∀ x : Fin 16, BitVec.ofNat 32 (BitVec.ofNat 8 MASK).toNat &&& BitVec.ofNat 32 (8 * x.val) =
      BitVec.ofNat 32 (2 * x.val * 4) := by decide +kernel
  exact h ⟨j, hj⟩

theorem plus4 (b : Word) (n : Nat) :
    b + (BitVec.ofNat 32 (2 * n * 4) + BitVec.ofNat 32 (4 : BitVec 8).toNat) =
      b + BitVec.ofNat 32 ((2 * n + 1) * 4) := by
  rw [show (4 : BitVec 8).toNat = 4 from rfl, ← BitVec.ofNat_add,
    show 2 * n * 4 + 4 = (2 * n + 1) * 4 by omega]

/-- **One step of macro `schedule`.** -/
theorem sched_run (s : State) {j : Nat} (hj : j < 16) (h7 : s.regs 7 = BitVec.ofNat 32 (8 * j)) :
    let s' := execAll schedBody s
    s'.mem = wset s.mem (s.regs 6) j (schedStep (wAt s.mem (s.regs 6)) j j) ∧
    s'.regs 7 = BitVec.ofNat 32 (8 * (j + 1)) ∧ s'.z = decide (j + 1 = 16) ∧
    ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 15 →
      s'.regs r = s.regs r := by
  have o0 : sOk [1, 8] (some 7) = true := by decide
  have o1 : sOk [19, 61] (some 6) = true := by decide
  have r7 : (execAll schedBody s).regs 7 = BitVec.ofNat 32 (8 * (j + 1)) := by
    simp only [schedBody, ldW, schedIdx]
    rsimp [sigma_regs _ _ o0, sigma_regs _ _ o1, h7]
    rw [show (8 : BitVec 8).toNat = 8 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
  intro s'
  refine ⟨?_, r7, ?_, fun r h0 h1 h2 h3 h4 h5 h7 h8 h9 h15 => ?_⟩
  · simp only [s', schedBody, ldW, schedIdx]
    rsimp [sigma_regs _ _ o0, sigma_mem _ _ o0, sigma_regs _ _ o1, sigma_mem _ _ o1, h7,
      idx j _ hj, idx0 j hj, plus4]
    simp only [wset, schedStep, upd, wAt, ite_true, Nat.mod_eq_of_lt hj, sigma0_sig, sigma1_sig]
  · have e : schedBody = schedBody.dropLast ++ [.cmpImm 7 (BitVec.ofNat 8 (8 * 16))] := rfl
    simp only [s']
    rw [e, execAll_append] at r7 ⊢
    simp only [execAll] at r7 ⊢
    rw [(RoutineBranch.cmpImm_flags _ _ _).2, ← nx_cmpImm _ _ (by decide) 7 (BitVec.ofNat 8 (8 * 16)),
      toReg_7, r7]
    simp only [BitVec.toNat_ofNat, decide_eq_decide]
    omega
  · simp only [s', schedBody, ldW, schedIdx]
    rsimp [sigma_regs _ _ o0, sigma_regs _ _ o1, h0, h1, h2, h3, h4, h5, h7, h8, h9]

end M0Crypto.Release.Ed25519Sha512Sched
