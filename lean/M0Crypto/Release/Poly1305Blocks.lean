import M0Crypto.Release.Poly1305BlocksCode
import M0Crypto.Release.Poly1305Mac
import M0Crypto.Release.Poly1305BlocksCheck
import M0Crypto.Release.ReachSteps
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-!
Execution of both message-load paths, one block, and the finite block loop.
All results refer to the instruction-level state functions checked against the
release bytes in `Poly1305BlocksCode`; none asserts RFC accumulator correctness.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Mac (mac narrow colend)

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

/-- Equal offsets from one base give equal addresses. Offsets are closed Nat terms
(the derived names of `Poly1305BlocksCode`), so callers discharge `h` by `decide +kernel`. -/
theorem pc_congr {base : Word} {a b : Nat} (h : a = b) :
    base + BitVec.ofNat 32 a = base + BitVec.ofNat 32 b := by
  rw [h]

/-- The straight-line body, from message addition through the reduced accumulator.
Its writes are restricted to five frame words; the count and saved registers survive. -/
theorem body_run_w {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 bodyAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hw : ∀ o < bodyBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) :
    ReachW base (BlkPc base) Wr s (fun t => t = execAll body s) := by
  apply ReachW.block (by omega) body bodyAt hp (by decide +kernel) segments_at.2.2.2.1 body_falls
    (stable_aligned body s body_stable hs hc)
  · intro e he y hy
    obtain ⟨o, ho, rfl⟩ := frameWB_writes body s body_frame e he y hy
    exact hw o ho
  · exact inRegion_pcBetween (by decide +kernel) (by decide +kernel)
  · exact ReachS.done rfl

theorem body_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 bodyAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hw : ∀ o < bodyBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) :
    Reach base Wr s (fun t => t = execAll body s) :=
  (body_run_w hb s hp hs hc hw).toReach

theorem body_regs (s : State) :
    (execAll body s).regs 7 = s.regs 7 ∧ (execAll body s).regs 12 = s.regs 12 ∧
    (execAll body s).regs 13 = s.regs 13 := by
  exact ⟨execAll_regs_other _ _ _ (by decide) (by decide),
    execAll_regs_other _ _ _ (by decide) (by decide), frameWB_sp _ _ body_frame⟩

theorem body_count (s : State) :
    read32 (execAll body s).mem (slot (s.regs 13) slotCount) = read32 s.mem (slot (s.regs 13) slotCount) := by
  apply read32_congr
  intro k hk
  apply frameWB_mem body s body_frame body_falls
  rintro ⟨o, ho, he⟩
  have := congrArg BitVec.toNat he
  have hc : slotCount < 2 ^ 28 := by decide
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- One block's execution function. It includes the actual alignment test, selected
load path, message addition, products, reduction and count decrement. It excludes
only the two loop-control branches. This definition makes no modular-arithmetic
claim; `Poly1305Arith.block_arith` is the independent arithmetic specification. -/
def loadState (s : State) : State :=
  let t := execAll testAlign s
  if (t.regs 6).toNat % 4 = 0 then
    (execAll loadA (t.setReg 15 (s.pc + BitVec.ofNat 32 loadAFrom))).setReg 15
      (s.pc + BitVec.ofNat 32 bodyFrom)
  else execAll loadU (t.setReg 15 (s.pc + BitVec.ofNat 32 loadUFrom))

def oneBlock (s : State) : State := execAll dec (execAll body (loadState s))

theorem test_regs (s : State) :
    (execAll testAlign s).regs 6 = read32 s.mem (slot (s.regs 13) slotMsg) ∧
    (execAll testAlign s).z = (read32 s.mem (slot (s.regs 13) slotMsg) &&& 3#32 == 0#32) := by
  simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, execAll, testAlign, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, slot, slotMsg]

theorem and3_zero (x : Word) : (x &&& 3#32 == 0#32) = (x.toNat % 4 == 0) := by
  have he : (x &&& 3#32).toNat = x.toNat % 4 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h; rw [← he, h]; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; rw [he, h]; rfl

theorem load_run_w {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0) :
    ReachW base (BlkPc base) Wr s (fun t => t = loadState s) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  apply ReachW.block hb2 testAlign testAt hp (by decide) segments_at.1 (by decide)
    (stable_aligned _ _ (by decide) hs hc) (WritesTo.of_noWritesMem _ _ (by decide) Wr)
    (inRegion_pcBetween (by decide +kernel) (by decide +kernel))
  let t := execAll testAlign s
  have pt : t.pc = base + BitVec.ofNat 32 alignBrAt := by
    dsimp [t]; rw [execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have tr : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 6 → r.val ≠ 15 → t.regs r = s.regs r := by
    intro r h4 h6 h15
    exact execAll_regs_other _ _ _ h15 (by simp [testAlign, Instr.dsts]; omega)
  have tz : t.z = ((t.regs 6).toNat % 4 == 0) := by
    rw [(test_regs s).2, and3_zero, (test_regs s).1]
  apply ReachW.bcond hb2 alignBrAt loadUAt 1 (brImm8 alignBrAt loadUAt) pt (by decide) (by decide) (by decide) (by decide)
    ⟨alignBrAt, by decide, by decide, rfl⟩
  · intro hT
    have hna : ¬ (t.regs 6).toNat % 4 = 0 := by
      simpa [condPassed, tz] using hT
    let u := t.setReg 15 (base + BitVec.ofNat 32 loadUAt)
    apply ReachW.block hb2 loadU loadUAt (by rfl) (by decide) segments_at.2.2.1 (by decide)
      (stable_aligned _ _ (by decide)
        (by simpa [u, M0Crypto.Armv6M.State.setReg, tr 13 (by decide) (by decide) (by decide)] using hs)
        (by simpa [u, M0Crypto.Armv6M.State.setReg, tr 7 (by decide) (by decide) (by decide)] using hc))
      (WritesTo.of_noWritesMem _ _ (by decide) Wr)
      (inRegion_pcBetween (by decide +kernel) (by decide +kernel))
    apply ReachS.done
    simp only [loadState, show execAll testAlign s = t from rfl, hna, ite_false]
    congr 2
    rw [hp, BitVec.add_assoc]; rfl
  · intro hF
    have ha : (t.regs 6).toNat % 4 = 0 := by
      simpa [condPassed, tz] using hF
    let u := t.setReg 15 (base + BitVec.ofNat 32 loadAAt)
    apply ReachW.block hb2 loadA loadAAt (by rfl) (by decide) segments_at.2.1 (by decide)
    · simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, alignedAll, loadA, Instr.accesses, wordAccesses, List.range_succ, bitCount,
        Access.aligned, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, u, BitVec.toNat_add]
      omega
    · exact WritesTo.of_noWritesMem _ _ (by decide) Wr
    · exact inRegion_pcBetween (by decide +kernel) (by decide +kernel)
    let v := execAll loadA u
    have pv : v.pc = base + BitVec.ofNat 32 skipBrAt := by
      dsimp [v]; rw [execAll_pc _ _ (by decide)]; change base + _ + _ = _
      rw [ofNat_add_assoc]; exact pc_congr (by decide +kernel)
    apply ReachW.b hb2 skipBrAt bodyAt (brImm11 skipBrAt bodyAt) pv (by decide) (by decide) (by decide) (by decide)
      ⟨skipBrAt, by decide, by decide, rfl⟩
    apply ReachS.done
    simp only [loadState, show execAll testAlign s = t from rfl, ha, ite_true]
    dsimp [v, u]
    rw [hp, BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem load_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0) :
    Reach base Wr s (fun t => t = loadState s) :=
  (load_run_w hb s hp hs hc).toReach

theorem load_props (s : State) :
    (loadState s).regs 7 = s.regs 7 ∧ (loadState s).regs 12 = s.regs 12 ∧
    (loadState s).regs 13 = s.regs 13 ∧ (loadState s).mem = s.mem := by
  have rt : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 6 → r.val ≠ 15 →
      (execAll testAlign s).regs r = s.regs r := by
    intro r h4 h6 h15; exact execAll_regs_other _ _ _ h15 (by simp [testAlign, Instr.dsts]; omega)
  have mt : (execAll testAlign s).mem = s.mem := execAll_mem _ _ (by decide)
  unfold loadState
  dsimp only
  split
  all_goals
    simp only [setReg_regs_ne, M0Crypto.Armv6M.State.setReg, ite_false, show (7 : Reg) ≠ 15 by decide, show (12 : Reg) ≠ 15 by decide, show (13 : Reg) ≠ 15 by decide]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [execAll_regs_other _ _ 7 (by decide) (by decide)]
      simp only [M0Crypto.Armv6M.State.setReg, ite_false, show (7 : Reg) ≠ 15 by decide]
      exact rt 7 (by decide) (by decide) (by decide)
    · rw [execAll_regs_other _ _ 12 (by decide) (by decide)]
      simp only [M0Crypto.Armv6M.State.setReg, ite_false, show (12 : Reg) ≠ 15 by decide]
      exact rt 12 (by decide) (by decide) (by decide)
    · rw [execAll_regs_other _ _ 13 (by decide) (by decide)]
      simp only [M0Crypto.Armv6M.State.setReg, ite_false, show (13 : Reg) ≠ 15 by decide]
      exact rt 13 (by decide) (by decide) (by decide)
    · rw [execAll_mem _ _ (by decide)]; exact mt

theorem load_pc (s : State) : (loadState s).pc = s.pc + BitVec.ofNat 32 bodyFrom := by
  unfold loadState
  dsimp only
  split
  · rfl
  · rw [execAll_pc _ _ (by decide)]
    change s.pc + BitVec.ofNat 32 loadUFrom + BitVec.ofNat 32 (seqSize loadU) = _
    rw [ofNat_add_assoc]; rfl

theorem dec_props (s : State) :
    let t := execAll dec s
    t.mem = write32 s.mem (slot (s.regs 13) slotCount) (read32 s.mem (slot (s.regs 13) slotCount) - 1#32) ∧
    t.z = (read32 s.mem (slot (s.regs 13) slotCount) - 1#32 == 0#32) := by
  simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, execAll, dec, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg,
    M0Crypto.Release.sub_flags, slot]
  change _ = _ ∧ _ = _
  rw [show (4294967294#32 : Word) = ~~~1#32 from rfl, M0Crypto.Release.sub_flags]
  exact ⟨rfl, rfl⟩

attribute [local irreducible] body loadState

theorem one_props (s : State) :
    (oneBlock s).regs 7 = s.regs 7 ∧ (oneBlock s).regs 12 = s.regs 12 ∧
    (oneBlock s).regs 13 = s.regs 13 ∧
    (oneBlock s).pc = s.pc + BitVec.ofNat 32 countBrFrom ∧
    read32 (oneBlock s).mem (slot (s.regs 13) slotCount) = read32 s.mem (slot (s.regs 13) slotCount) - 1#32 ∧
    (oneBlock s).z = (read32 s.mem (slot (s.regs 13) slotCount) - 1#32 == 0#32) := by
  obtain ⟨l7, l12, l13, lm⟩ := load_props s
  obtain ⟨b7, b12, b13⟩ := body_regs (loadState s)
  have cr : read32 (execAll body (loadState s)).mem (slot (s.regs 13) slotCount) =
      read32 s.mem (slot (s.regs 13) slotCount) := by
    rw [← l13, body_count, l13, lm]
  have br : (execAll body (loadState s)).regs 13 = s.regs 13 := b13.trans l13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneBlock, execAll_regs_other _ _ 7 (by decide) (by decide), b7, l7]
  · rw [oneBlock, execAll_regs_other _ _ 12 (by decide) (by decide), b12, l12]
  · rw [oneBlock, execAll_regs_other _ _ 13 (by decide) (by decide), br]
  · rw [oneBlock, execAll_pc _ _ (by decide), execAll_pc _ _ body_falls, load_pc,
      ofNat_add_assoc, ofNat_add_assoc]; exact pc_congr (by decide +kernel)
  · rw [oneBlock, (dec_props _).1, br, M0Crypto.Armv6M.read32_write32_same, cr]
  · rw [oneBlock, (dec_props _).2, br, cr]

theorem one_run_w {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hw : ∀ o < belowPadBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) :
    ReachW base (BlkPc base) Wr s (fun t => t = oneBlock s) := by
  apply ReachS.bind
  apply (load_run_w hb s hp hs hc).mono (fun _ _ h => h)
  intro t ht; subst t
  obtain ⟨l7, _, l13, _⟩ := load_props s
  have lp : (loadState s).pc = base + BitVec.ofNat 32 bodyAt := by
    rw [load_pc, hp, ofNat_add_assoc]; rfl
  apply ReachS.bind
  apply (body_run_w hb _ lp (by rw [l13]; exact hs) (by rw [l7]; exact hc)
    (fun o ho => by rw [l13]; exact hw o (Nat.lt_of_lt_of_le ho bodyBytes_le_belowPad))).mono (fun _ _ h => h)
  intro t ht; subst t
  have bsp := (body_regs (loadState s)).2.2.trans l13
  apply ReachW.block (by omega) dec decAt
    (by rw [execAll_pc _ _ body_falls, lp, ofNat_add_assoc]; exact pc_congr (by decide +kernel))
    (by decide +kernel) segments_at.2.2.2.2.1 (by decide)
    (stable_aligned _ _ (by decide) (by rw [bsp]; exact hs)
      (by rw [(body_regs _).1, l7]; exact hc))
  · intro e he y hy
    obtain ⟨o, ho, rfl⟩ := frameWB_writes dec _ (show frameWB slotPad dec = true from by decide) e he y hy
    rw [bsp]; exact hw o ho
  · exact inRegion_pcBetween (by decide +kernel) (by decide +kernel)
  · exact ReachS.done rfl

theorem one_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hw : ∀ o < belowPadBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) :
    Reach base Wr s (fun t => t = oneBlock s) :=
  (one_run_w hb s hp hs hc hw).toReach

attribute [local irreducible] oneBlock

theorem setPc_twice (s : State) (a b : Word) :
    (s.setReg 15 a).setReg 15 b = s.setReg 15 b := by
  simp only [M0Crypto.Armv6M.State.setReg]
  congr 1
  funext r
  by_cases hr : r = 15 <;> simp [hr]

/-- Exact finite loop result, retaining the selected load path and register-width
arithmetic of each block. This is an execution specification; `Poly1305BlocksCorrect` refines it to the RFC MAC. -/
def loopState (base : Word) : Nat → State → State
  | 0, s => s
  | n+1, s =>
    let t := oneBlock s
    if n = 0 then t.setReg 15 (base + BitVec.ofNat 32 publishAt)
    else loopState base n (t.setReg 15 (base + BitVec.ofNat 32 testAt))

theorem loop_run_w {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} :
    ∀ (n : Nat), 0 < n → n < 2^32 → ∀ s : State,
    s.pc = base + BitVec.ofNat 32 testAt →
    (s.regs 13).toNat % 4 = 0 → (s.regs 7).toNat % 4 = 0 →
    read32 s.mem (slot (s.regs 13) slotCount) = BitVec.ofNat 32 n →
    (∀ o < belowPadBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) →
    ReachW base (BlkPc base) Wr s (fun t => t = loopState base n s ∧
      t.pc = base + BitVec.ofNat 32 publishAt ∧ t.regs 7 = s.regs 7 ∧
      t.regs 12 = s.regs 12 ∧ t.regs 13 = s.regs 13 ∧
      read32 t.mem (slot (s.regs 13) slotCount) = 0#32)
  | 0, hn, _, _, _, _, _, _, _ => by omega
  | n+1, _, hn, s, hp, hs, hc, hcount, hw => by
    have hb2 : base.toNat % 2 = 0 := by omega
    apply ReachS.bind
    apply (one_run_w hb s hp hs hc hw).mono (fun _ _ h => h)
    intro t ht; subst t
    obtain ⟨r7, r12, r13, pc, count, z⟩ := one_props s
    have pc' : (oneBlock s).pc = base + BitVec.ofNat 32 countBrAt := by
      rw [pc, hp, ofNat_add_assoc]; rfl
    have sub : BitVec.ofNat 32 (n+1) - 1#32 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    have c' : read32 (oneBlock s).mem (slot (s.regs 13) slotCount) = BitVec.ofNat 32 n := by
      rw [count, hcount, sub]
    have z' : (oneBlock s).z = (BitVec.ofNat 32 n == 0#32) := by
      rw [z, hcount, sub]
    apply ReachW.bcond hb2 countBrAt publishAt 0 (brImm8 countBrAt publishAt) pc' (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ⟨countBrAt, by decide +kernel, by decide +kernel, rfl⟩
    · intro hT
      have n0 : n = 0 := by
        have hz : BitVec.ofNat 32 n = 0#32 := by simpa [condPassed, z'] using hT
        have := congrArg BitVec.toNat hz; simp at this; omega
      apply ReachS.done
      refine ⟨by simp [loopState, n0], rfl, ?_, ?_, ?_, ?_⟩
      · simpa [M0Crypto.Armv6M.State.setReg] using r7
      · simpa [M0Crypto.Armv6M.State.setReg] using r12
      · simpa [M0Crypto.Armv6M.State.setReg] using r13
      · simpa [n0] using c'
    · intro hF
      have nn : n ≠ 0 := by
        intro hz; simp [condPassed, z', hz] at hF
      let u := (oneBlock s).setReg 15 (base + BitVec.ofNat 32 (countBrAt + 2))
      apply ReachW.b hb2 backBrAt testAt (brImm11 backBrAt testAt) (by rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        ⟨backBrAt, by decide +kernel, by decide +kernel, rfl⟩
      let v := u.setReg 15 (base + BitVec.ofNat 32 testAt)
      have v7 : v.regs 7 = s.regs 7 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r7
      have v12 : v.regs 12 = s.regs 12 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r12
      have v13 : v.regs 13 = s.regs 13 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r13
      have vc : read32 v.mem (slot (v.regs 13) slotCount) = BitVec.ofNat 32 n := by rw [v13]; exact c'
      apply (loop_run_w hb n (by omega) (by omega) v rfl (by rw [v13]; exact hs)
        (by rw [v7]; exact hc) vc (by rw [v13]; exact hw)).mono (fun _ _ h => h)
      intro t ht
      obtain ⟨eq, pt, t7, t12, t13, tc⟩ := ht
      refine ⟨?_, pt, t7.trans v7, t12.trans v12, t13.trans v13, ?_⟩
      · rw [eq, loopState, ite_eq_right nn]
        change loopState base n (((oneBlock s).setReg 15 _).setReg 15 _) = _
        rw [setPc_twice]
      · rw [← v13]; exact tc

theorem loop_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} :
    ∀ (n : Nat), 0 < n → n < 2^32 → ∀ s : State,
    s.pc = base + BitVec.ofNat 32 testAt →
    (s.regs 13).toNat % 4 = 0 → (s.regs 7).toNat % 4 = 0 →
    read32 s.mem (slot (s.regs 13) slotCount) = BitVec.ofNat 32 n →
    (∀ o < belowPadBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) →
    Reach base Wr s (fun t => t = loopState base n s ∧
      t.pc = base + BitVec.ofNat 32 publishAt ∧ t.regs 7 = s.regs 7 ∧
      t.regs 12 = s.regs 12 ∧ t.regs 13 = s.regs 13 ∧
      read32 t.mem (slot (s.regs 13) slotCount) = 0#32) :=
  fun n h1 h2 s hp hs hc hn hw => (loop_run_w hb n h1 h2 s hp hs hc hn hw).toReach

theorem one_mem (s : State) (y : Word) (hy : ¬ InFrame (s.regs 13) slotPad y) :
    (oneBlock s).mem y = s.mem y := by
  have hcp : slotCount < slotPad := by decide
  obtain ⟨_, _, l13, lm⟩ := load_props s
  have br : (execAll body (loadState s)).regs 13 = s.regs 13 :=
    (body_regs _).2.2.trans l13
  rw [oneBlock, (dec_props _).1]
  rw [M0Crypto.Armv6M.write32_other]
  · rw [frameWB_mem body _ body_frame body_falls y, lm]
    intro h; apply hy; rw [l13] at h
    obtain ⟨o, ho, he⟩ := h; exact ⟨o, by omega, he⟩
  · intro k hk he
    apply hy
    refine ⟨4 * slotCount + k, by omega, ?_⟩
    rw [he, br, slot, ofNat_add_assoc]

theorem loop_regs (base : Word) : ∀ n s,
    (loopState base n s).regs 7 = s.regs 7 ∧
    (loopState base n s).regs 12 = s.regs 12 ∧
    (loopState base n s).regs 13 = s.regs 13
  | 0, s => ⟨rfl, rfl, rfl⟩
  | n+1, s => by
    obtain ⟨r7, r12, r13, _⟩ := one_props s
    rw [loopState]
    split
    · simp only [setReg_regs_ne _ 15 7 _ (by decide), setReg_regs_ne _ 15 12 _ (by decide),
        setReg_regs_ne _ 15 13 _ (by decide)]
      exact ⟨r7, r12, r13⟩
    · obtain ⟨a, b, c⟩ := loop_regs base n ((oneBlock s).setReg 15 (base + BitVec.ofNat 32 testAt))
      rw [setReg_regs_ne _ 15 7 _ (by decide)] at a
      rw [setReg_regs_ne _ 15 12 _ (by decide)] at b
      rw [setReg_regs_ne _ 15 13 _ (by decide)] at c
      exact ⟨a.trans r7, b.trans r12, c.trans r13⟩

theorem loop_mem (base : Word) : ∀ n s y, (¬ InFrame (s.regs 13) slotPad y) →
    (loopState base n s).mem y = s.mem y
  | 0, s, y, _ => rfl
  | n+1, s, y, hy => by
    rw [loopState]
    split
    · exact one_mem s y hy
    · rw [loop_mem base n _ y]
      · exact one_mem s y hy
      · rw [setReg_regs_ne _ 15 13 _ (by decide), (one_props s).2.2.1]
        exact hy

end M0Crypto.Release.Poly1305Blocks
