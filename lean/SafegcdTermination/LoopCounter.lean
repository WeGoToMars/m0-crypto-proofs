import SafegcdTermination.BatchState

namespace SafegcdTermination.LoopCounter

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open M0Crypto.Armv6M (State Mem write32)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def triplets : Nat := batchCount / 3
def initialCount : Nat := triplets + 1

def updateCounter : List Instr := [loadSp 0 counterAt, .subImm8 0 1, storeSp 0 counterAt]

theorem count_effect (s : State) (n : Nat) (hn : n ≤ initialCount) (hnz : 0 < n)
    (hc : stackWord s counterAt = BitVec.ofNat 32 n) :
    let t := execAll updateCounter s
    t.mem = write32 s.mem (addr s.sp counterAt) (BitVec.ofNat 32 (n-1)) ∧
      t.z = (n == 1) ∧ t.sp = s.sp := by
  have hB : initialCount < 4294967296 := by decide
  have hs : stackWord s counterAt - 1#32 = BitVec.ofNat 32 (n-1) := by
    rw [hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hq : (BitVec.ofNat 32 (n-1) == 0#32) = (n == 1) := by
    by_cases he : n = 1
    · simp [he]
    · have hn' : BitVec.ofNat 32 (n-1) ≠ 0#32 := by
        intro h
        have h' := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reducePow] at h'
        omega
      rw [beq_eq_false_iff_ne.mpr hn', beq_eq_false_iff_ne.mpr he]
  unfold updateCounter loadSp storeSp imm addr
  row_simps
  have ho : counterAt / 4 % 256 * 4 = counterAt := by decide
  rw [ho]
  have hv : (M0Crypto.Armv6M.addWithCarry (stackWord s counterAt) 4294967294#32 true).1 =
      BitVec.ofNat 32 (n-1) := (M0Crypto.Release.sub_flags _ 1#32).trans hs
  change write32 s.mem (addr s.sp counterAt)
      (M0Crypto.Armv6M.addWithCarry (stackWord s counterAt) 4294967294#32 true).1 = _ ∧
      (((M0Crypto.Armv6M.addWithCarry (stackWord s counterAt) 4294967294#32 true).1 == 0#32) = (n == 1))
  rw [hv]
  exact ⟨rfl, hq⟩

/-- Counter as observed at the head of phase zero after k full triplets. -/
theorem loop_bounds {k : Nat} (hk : k ≤ triplets) :
    0 < initialCount - k ∧ initialCount - k ≤ initialCount ∧ 3*k + 1 ≤ batchCount ∧
      ((initialCount - k = 1) ↔ (3*k + 1 = batchCount)) := by
  simp only [initialCount, triplets, batchCount, Nat.reduceDiv] at hk ⊢
  omega

theorem extra_two {k : Nat} (hk : k ≤ triplets) (hc : initialCount - k ≠ 1) :
    k+1 ≤ triplets ∧ 3*k + 3 ≤ batchCount := by
  simp only [initialCount, triplets, batchCount, Nat.reduceDiv] at hk hc ⊢
  omega

end SafegcdTermination.LoopCounter
