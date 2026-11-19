import M0Crypto.Release.Field25519Routines
import M0Crypto.Release.Field25519Block

set_option linter.unusedSimpArgs false

/-!
Facts shared by the routine proofs of the field routines and by their callers: `feVal` as a
little-endian partial sum (`psum`, `feVal_psum`, `feVal_lt`), code addresses inside a routine's
bytes (`inReg`, `inReg1`) and apart from a disjoint region (`region_ne`), the final
`pop {pc}` (`pop_at`, `pop_run_w`), and the step from a `ReachW` run to the model's `runUntil`
when the stop address lies outside the region of executed PCs (`reachW_runUntil`; a routine's
return address is outside the routine, not outside the artifact).
-/

namespace M0Crypto.Release.Field25519Facts
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion RegionWrites StepsOk stepsOk_events_iff WritesTo Region)
open M0Crypto.Release.Frame (Disj sub_ofNat_toNat)
open M0Crypto.Release.Field25519Routines (feVal)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- Little-endian partial sum of `j` words. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => psum f j + 2 ^ (32 * j) * f j

theorem psum_congr {f g : Nat → Nat} : ∀ {j : Nat}, (∀ i < j, f i = g i) → psum f j = psum g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [psum]
    rw [psum_congr (fun i hi => h i (by omega)), h j (by omega)]

theorem psum_lt {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ 32) : ∀ j, psum f j < 2 ^ (32 * j)
  | 0 => by simp [psum]
  | j + 1 => by
    simp only [psum]
    have ih := psum_lt hf j
    have hj := hf j
    have : 2 ^ (32 * j) * f j + 2 ^ (32 * j) ≤ 2 ^ (32 * j) * 2 ^ 32 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    rw [show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
    omega

theorem sum_range_psum (f : Nat → Nat) : ∀ j : Nat,
    ((List.range j).map fun i => f i * 2 ^ (32 * i)).sum = psum f j
  | 0 => rfl
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_psum f j]
    simp only [psum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.mul_comm (f j)]

/-- `feVal` is the little-endian sum of the 8 words. -/
theorem feVal_psum (m : Mem) (p : Word) :
    feVal m p = psum (fun i => (read32 m (slot p i)).toNat) 8 :=
  sum_range_psum (fun i => (read32 m (slot p i)).toNat) 8

theorem feVal_lt (m : Mem) (p : Word) : feVal m p < 2 ^ 256 := by
  rw [feVal_psum]; exact psum_lt (fun i => BitVec.isLt _) 8

/-- `pop {pc}` at its offset. -/
theorem pop_at {o : Nat} (h : seqAt B o [.pop 0 true] = true) :
    instrAt B o = some (.pop 0 true) ∧ o + 2 ≤ B.length := by
  simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1, by simpa [Instr.size] using h.2⟩

/-- Code bytes `[off, off + n)` inside the routine's bytes. -/
theorem inReg {base : Word} {F S off n : Nat} (h : F ≤ off ∧ off + n ≤ F + S ∧ F + S < 2 ^ 32) :
    InRegion (Region (base + BitVec.ofNat 32 F) S) base off n := fun j hj => by
  show ((base + BitVec.ofNat 32 (off + j)) - (base + BitVec.ofNat 32 F)).toNat < S
  rw [show off + j = F + (off + j - F) by omega, ← ofNat_add_assoc, sub_ofNat_toNat _ _ (by omega)]
  omega

/-- One code address inside the routine's bytes. -/
theorem inReg1 {base : Word} {F S off : Nat} (h : F ≤ off ∧ off + 1 ≤ F + S ∧ F + S < 2 ^ 32) :
    Region (base + BitVec.ofNat 32 F) S (base + BitVec.ofNat 32 off) := by
  simpa using inReg (n := 1) h 0 (by omega)

/-- A byte of `b`'s region is not a byte of `a`'s when the regions are disjoint. -/
theorem region_ne {a b y : Word} {n m : Nat} (hd : Disj a n b m) (hy : Region b m y) :
    ∀ i < n, y ≠ a + BitVec.ofNat 32 i := by
  intro i hi e
  obtain ⟨h1, h2, h3⟩ := hd
  subst e
  have hx : ((a + BitVec.ofNat 32 i) - b).toNat < m := hy
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := a.isLt; have := b.isLt
  rw [Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show a.toNat + i < 2 ^ 32 by omega)] at hx
  omega

/-- A `ReachW` run to `stop` whose writes miss the code is the model's `runUntil stop`,
provided `stop` lies outside the region of executed PCs. -/
theorem reachW_runUntil {base : Word} {Pc Wr : Word → Prop} {s : State} {stop : Word}
    {P : State → Prop} (hc : CodeAt s.mem base B)
    (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i) (hstop : ¬ Pc stop)
    (h : ReachW base Pc Wr s fun s' => s'.pc = stop ∧ P s') :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil stop fuel s = .ok (s', tr) ∧ P s' ∧
      WritesTo Wr tr := by
  obtain ⟨n, s', tr, hr, hok, hpc, hP⟩ := h
  have hev := (stepsOk_events_iff (p := fun e => Pc e.pc ∧ ∀ y, Writes e.accesses y → Wr y) hr).mp hok
  refine ⟨n, fun fuel hf => ⟨s', tr, ?_, hP, fun e he y hy => (hev e he).2 y hy⟩⟩
  apply runUntil_of_runH n fuel s s' tr hc hr _ _ hpc hf
  · intro e he i hi hwr
    exact hwc _ ((hev e he).2 _ hwr) i hi rfl
  · intro e he heq
    exact hstop (heq ▸ (hev e he).1)

/-- `pop {pc}`: return to the saved word at SP. -/
theorem pop_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off : Nat} (hat : instrAt B off = some (.pop 0 true)) (hsz : off + 2 ≤ B.length)
    (ho : off % 2 = 0) (hpc : x.pc = base + BitVec.ofNat 32 off) (hr : Pc (base + BitVec.ofNat 32 off))
    (hsp : (x.regs 13).toNat % 4 = 0) (hlr : (read32 x.mem (x.regs 13)).getLsbD 0 = true)
    {Q : State → Prop}
    (hq : ∀ y : State, y.pc = read32 x.mem (x.regs 13) &&& ~~~1#32 →
      y.regs 13 = x.regs 13 + 4#32 → y.mem = x.mem → Q y) :
    ReachW base Pc Wr x Q := by
  have hb0 : bitCount (0 : BitVec 8) = 0 := by decide
  have hl : listRegs (0 : BitVec 8) = [] := by decide
  have hb0' : bitCount 0#8 = 0 := by decide
  have hl' : listRegs 0#8 = [] := by decide
  have ha : x.regs 13 + BitVec.ofNat 32 (4 * bitCount (0 : BitVec 8)) = x.regs 13 := by
    rw [hb0]; simp
  have hex : (Instr.pop 0 true).exec x = .ok
      ((((loadRegs (x.setReg 15 (x.pc + BitVec.ofNat 32 (Instr.pop 0 true).size)) x.sp
        ((listRegs 0).map LowReg.toReg)).setReg 13
          (x.sp + BitVec.ofNat 32 (4 * (bitCount 0 + true.toNat))))).setReg 15
          (read32 x.mem (x.regs 13) &&& ~~~1#32)) := by
    simp only [Instr.exec, State.sp, ha, hlr, ite_true]
  refine ReachW.step hb off (.pop 0 true) hpc ho hat hsz ?_ hex ?_ hr (ReachS.done (hq _ ?_ ?_ ?_))
  · simp [Instr.accesses, wordAccesses, hb0, Access.aligned, State.sp, hsp]
  · intro y ⟨a, ha', hw, _⟩
    simp [Instr.accesses, wordAccesses, hb0] at ha'
    obtain ⟨_, _, rfl⟩ := ha'
    cases hw
  · simp [State.setReg, State.pc]
  · simp [State.setReg, hb0, hb0', loadRegs, hl, hl', State.sp]
  · simp [State.setReg, loadRegs, hl, hl']

end M0Crypto.Release.Field25519Facts
