import M0Crypto.Release.Blake2sUpdateCall
import M0Crypto.Release.Blake2sCopyLoops
import M0Crypto.Release.ReachN
import M0Crypto.Release.Blake2sCopyNR

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # The byte-copy loop of `update` (1 to 7 bytes)

The loop is the byte loop of `m0c_blake2s_copy` placed inside `update`; unlike there, `r4`-`r7`
are live across it, so the invariant keeps every register from `r4` up. -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sCopy (ReachNR Cp cp_w8 cp_src byteB_eff read8_low cp1 sr_ne sr_pc rem_zero cp_zero)
open M0Crypto.Release.Blake2sCopyCode (byteB)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

/-- The byte-loop state: `k` bytes are copied, `r0`, `r1`, `r2` track the cursors, `r4` up is kept. -/
structure BI (R : Reg → Word) (m0 : Mem) (d s : Word) (n k : Nat) (t : State) : Prop where
  r0 : t.regs 0 = d + BitVec.ofNat 32 k
  r1 : t.regs 1 = s + BitVec.ofNat 32 k
  r2 : t.regs 2 = BitVec.ofNat 32 (n - k)
  cp : Cp m0 t.mem d s k
  hi : ∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → t.regs r = R r
  kn : k ≤ n

theorem BI.setPc {R m0 d s n k t} (h : BI R m0 d s n k t) (v : Word) : BI R m0 d s n k (t.setReg 15 v) :=
  ⟨by rw [sr_ne _ _ _ _ (by decide)]; exact h.r0, by rw [sr_ne _ _ _ _ (by decide)]; exact h.r1,
   by rw [sr_ne _ _ _ _ (by decide)]; exact h.r2, by rw [show (t.setReg 15 v).mem = t.mem from rfl]; exact h.cp,
   fun r h4 h15 => by rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.hi r h4 h15, h.kn⟩

theorem byteLoop_eq : byteLoop = byteB := rfl

theorem byteL_BI {R m0 d s n k t} (h : BI R m0 d s n k t) (hk : k < n) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) :
    BI R m0 d s n (k + 1) (execAll byteLoop t) ∧ (execAll byteLoop t).z = decide (k + 1 = n) := by
  rw [byteLoop_eq]
  obtain ⟨e0, e1, e2, em, ez, er⟩ := byteB_eff t
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hk⟩, ?_⟩
  · rw [e0, h.r0, ofNat_add_assoc]
  · rw [e1, h.r1, ofNat_add_assoc]
  · rw [e2, h.r2]; bv_omega
  · rw [em, h.r0, h.r1]
    apply cp_w8 (by omega) h.cp
    rw [read8_low, cp_src h.cp hDj (by omega) hk]
  · intro r h4 h15
    rw [er r h4 h15]; exact h.hi r h4 h15
  · rw [ez, h.r2]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    · intro e; have : n - k = 1 := by omega
      rw [this]; rfl

/-- The loop ends at `oNext` with all `n` bytes copied. -/
def GB (base : Word) (R : Reg → Word) (m0 : Mem) (d s : Word) (n : Nat) (u : State) : Prop :=
  u.pc = base + BitVec.ofNat 32 oNext ∧ BI R m0 d s n n u

section loops
variable {base : Word} {Wr Rd : Word → Prop} {R : Reg → Word} {m0 : Mem} {d s : Word} {n : Nat}

theorem byte_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ rem k, rem + k = n → ∀ t : State, t.pc = base + BitVec.ofNat 32 oBytesL →
      BI R m0 d s n k t → 1 ≤ rem → ReachNR base Wr Rd t (GB base R m0 d s n)
  | 0, k, h, t, hpc, hci, hr => absurd hr (by omega)
  | rem + 1, k, h, t, hpc, hci, _ => by
    have hk : k < n := by omega
    refine ReachNR.symBlock hb2 [((1 : Reg), 1), ((0 : Reg), 1)] [((0 : Reg), (0#32 : Word), 1)]
      [((1 : Reg), (0#32 : Word), 1)] byteLoop oBytesL hpc
      (by decide +kernel) byteLoop_at (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact Nat.mod_one _
    · apply Reach.region_one
      intro o ho
      rw [hci.r0, BitVec.add_zero, ofNat_add_assoc]; exact hW _ (by omega)
    · apply rr_one
      intro o ho
      rw [hci.r1, BitVec.add_zero, ofNat_add_assoc]; exact hR _ (by omega)
    obtain ⟨hci', hz⟩ := byteL_BI hci hk hDj hn
    have hp : (execAll byteLoop t).pc = base + BitVec.ofNat 32 oBytesBne := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oBytesBne oBytesL 1 (brImm8 oBytesBne oBytesL) hp (by decide +kernel) bytesBne_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      have hz' : (execAll byteLoop t).z = false := by
        rw [cp1] at hc; simpa using hc
      have hne : k + 1 ≠ n := by rw [hz] at hz'; simpa using hz'
      exact byte_loop hb2 hDj hn hW hR rem (k + 1) (by omega) _ (by rw [sr_pc]) (hci'.setPc _) (by omega)
    · intro hc
      have hz' : (execAll byteLoop t).z = true := by rw [cp1] at hc; simpa using hc
      have heq : k + 1 = n := by rw [hz] at hz'; simpa using hz'
      apply ReachNR.done
      refine ⟨by rw [sr_pc, show oBytesBne + 2 = oNext by decide], ?_⟩
      have := hci'.setPc (base + BitVec.ofNat 32 (oBytesBne + 2))
      rwa [heq] at this

end loops

/-- Entry: a state at the byte loop with `r0 = d`, `r1 = s`, `r2 = n` and nothing copied. -/
theorem byte_reach {base : Word} {Wr Rd : Word → Prop} {t : State} (hb2 : base.toNat % 2 = 0)
    {n : Nat} (hn1 : 1 ≤ n) (hn : n < 2 ^ 31) (hDj : Disj (t.regs 0) n (t.regs 1) n)
    (hpc : t.pc = base + BitVec.ofNat 32 oBytesL) (h2 : t.regs 2 = BitVec.ofNat 32 n)
    (hW : ∀ i < n, Wr (t.regs 0 + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (t.regs 1 + BitVec.ofNat 32 i)) :
    ReachNR base Wr Rd t (GB base t.regs t.mem (t.regs 0) (t.regs 1) n) := by
  refine byte_loop hb2 hDj hn hW hR n 0 (by omega) t hpc ⟨?_, ?_, ?_, cp_zero _ _ _, fun r _ _ => rfl, by omega⟩ hn1
  · simp
  · simp
  · rw [h2]; simp

end M0Crypto.Release.Blake2sUpdate
