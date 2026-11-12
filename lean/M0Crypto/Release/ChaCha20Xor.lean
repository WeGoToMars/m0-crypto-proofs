import M0Crypto.Release.ChaCha20Clear
import M0Crypto.Release.ChaCha20Output
import M0Crypto.Release.ChaCha20Layout

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
The block loop, frame clearing and the whole-function theorem for `m0c_chacha20_xor`.
-/

namespace M0Crypto.Release.ChaCha20Xor
open M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Output (Out sub_carry)
open M0Crypto.Release.ChaCha20Layout (n1Off blsOff nxtOff bbackOff clrOff zOff epiOff errOff berrOff2 bpreOff
  slotLen slotInp slotOutp slotCtr slotJ chFrameWords chFrameBytes chStackBytes slotSaved)

/-! ## `.Lnext`: `n1Off` - `clrOff` -/

theorem n1_at : seqAt B n1Off lenTest = true := by decide
theorem bls_at : instrAt B blsOff = some (.bcond 9 (brImm8 blsOff clrOff)) := by decide +kernel

theorem nxt_at : seqAt B nxtOff nxt = true := by decide
theorem bback_at : instrAt B bbackOff = some (.b (brImm11 bbackOff bpreOff)) := by decide +kernel
theorem bls_next : blsOff + 2 = nxtOff := by decide
theorem n1_next : n1Off + seqSize lenTest = blsOff := by decide
theorem nxt_end : nxtOff + seqSize nxt = bbackOff := by decide
theorem z_next : zOff + seqSize [.movImm 0 0] = epiOff := by decide
theorem err_next : errOff + seqSize [.movImm 0 0, .dp .mvns 0 0] = berrOff2 := by decide
theorem clr_end : clrOff + seqSize clr = zOff := by decide

theorem nxt_effect (t : State) (sp : Word) (h13 : t.regs 13 = sp) :
    (execAll nxt t).regs 13 = sp ∧
    (execAll nxt t).mem = write32 (write32 (write32 (write32 t.mem (slot sp slotLen) (t.regs 4 - 64#32))
      (slot sp slotInp) (t.regs 2 + 64#32)) (slot sp slotOutp) (t.regs 3 + 64#32)) (slot sp slotCtr)
      (read32 (write32 (write32 (write32 t.mem (slot sp slotLen) (t.regs 4 - 64#32))
      (slot sp slotInp) (t.regs 2 + 64#32)) (slot sp slotOutp) (t.regs 3 + 64#32)) (slot sp slotCtr) + 1#32) := by
  refine ⟨(execAll_regs_other nxt t 13 (by decide) (by decide)).trans h13, ?_⟩
  simp only [nxt, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3,
    M0Crypto.Proofs.toReg_4, slotLen, slotInp, slotOutp, slotCtr, slotJ]
  simp (config := { decide := true }) only [ite_true, ite_false, h13]
  rw [M0Crypto.Release.sub_flags, add_flags, add_flags, add_flags]
  simp [slot]

theorem J_succ (c : Ctx) (k i : Nat) (hi : i < 16) (h12 : i ≠ 12) : c.J (k + 1) i = c.J k i := by
  by_cases h4 : i < 4
  · obtain ⟨a0, a1, a2, a3⟩ := J_const c k
    obtain ⟨b0, b1, b2, b3⟩ := J_const c (k + 1)
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]
  by_cases h12' : i < 12
  · obtain ⟨j, rfl⟩ : ∃ j, i = 4 + j := ⟨i - 4, by omega⟩
    rw [J_key c _ j (by omega), J_key c _ j (by omega)]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 13 + j := ⟨i - 13, by omega⟩
    rw [J_nonce c _ j (by omega), J_nonce c _ j (by omega)]

theorem J_succ12 (c : Ctx) (k : Nat) : c.J (k + 1) 12 = c.J k 12 + 1#32 := by
  rw [J_ctr, J_ctr, BitVec.add_assoc, ← ChaCha20Output.ofNat_succ]

theorem sub64 (a : Word) (k : Nat) : a - BitVec.ofNat 32 (64 * k) - 64#32 = a - BitVec.ofNat 32 (64 * (k + 1)) := by
  rw [BitVec.sub_sub, show (64#32 : Word) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]; congr 2

theorem add64 (a : Word) (k : Nat) : a + BitVec.ofNat 32 (64 * k) + 64#32 = a + BitVec.ofNat 32 (64 * (k + 1)) := by
  rw [show (64#32 : Word) = BitVec.ofNat 32 64 from rfl, ofNat_add_assoc, Nat.mul_succ]

/-- **`.Lnext`**: after block `k`, either everything is written (to `clrOff`) or block `k + 1` starts. -/
theorem lnext_select_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : Out c k t) (allowed : Word → Kind → Word → Prop)
    (hlenTest : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 n1Off →
      EventAccessesTo allowed (traceAll lenTest u))
    (hnxt : ∀ u : State, u.pc = c.base + BitVec.ofNat 32 nxtOff → u.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll nxt u)) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → c.len.toNat - 64 * k ≤ 64 → ReachS c.base (ChaCha20Policy.EvP Pc allowed) u Q)
    (knext : ∀ u, BlockInv c (k + 1) u → ReachS c.base (ChaCha20Policy.EvP Pc allowed) u Q) : ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hR := ChaCha20Output.rem_eq c k h.lt
  have := h.lt
  have hlen := c.len.isLt
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sFB := ChaCha20Layout.chFrameBytes_eq
  have sJ : slotJ = 16 := by decide
  -- Numeric values of the named slots, for `omega` side conditions only.
  have sC : slotCtr = 28 := by decide
  have sO : slotOutp = 33 := by decide
  have sI : slotInp = 34 := by decide
  have sL : slotLen = 32 := by decide
  have hjs : ∀ i < 16, c.fw t (slotJ + i) = c.J k i := fun i hi => h.j i hi
  apply ChaCha20Policy.blockP hPc hb2 lenTest n1Off h.pc (by decide) n1_at (by decide)
    (by
      simp only [lenTest, alignedAll, Instr.accesses, M0Crypto.Armv6M.State.sp, h.sp, List.all_cons, List.all_nil,
        Access.aligned, Bool.and_true, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := ChaCha20Setup.fp4 hv; simp; omega)
    (hlenTest t h.pc) (by decide +kernel)
  generalize hs1 : execAll lenTest t = s1
  have r1 : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 15 → s1.regs r = t.regs r := fun r a b => by
    rw [← hs1]; exact execAll_regs_other _ _ r b (by simp [lenTest, Instr.dsts, Fin.ext_iff]; exact a)
  have m1 : s1.mem = t.mem := by rw [← hs1]; exact execAll_mem _ _ (by decide)
  have pc1 : s1.pc = c.base + BitVec.ofNat 32 blsOff := by
    rw [← hs1, execAll_pc _ _ (by decide), h.pc, ofNat_add_assoc, n1_next]
  have v4 : s1.regs 4 = BitVec.ofNat 32 (c.len.toNat - 64 * k) := by
    rw [← hs1]
    simp only [lenTest, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setNZCV,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_4]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [h.sp, show c.fp + BitVec.ofNat 32 ((BitVec.ofNat 8 slotLen).toNat * 4) = slot c.fp slotLen by simp [slot, slotLen]]
    rw [show read32 t.mem (slot c.fp slotLen) = c.fw t slotLen from rfl, h.len, hR]
  have cz : (condPassed 9 s1) = decide (c.len.toNat - 64 * k ≤ 64) := by
    rw [← hs1]
    simp only [condPassed, lenTest, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setNZCV,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_4]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [h.sp, show c.fp + BitVec.ofNat 32 ((BitVec.ofNat 8 slotLen).toNat * 4) = slot c.fp slotLen by simp [slot, slotLen]]
    rw [show read32 t.mem (slot c.fp slotLen) = c.fw t slotLen from rfl, h.len, hR, sub_carry, M0Crypto.Release.sub_flags]
    by_cases hc : c.len.toNat - 64 * k ≤ 64
    · by_cases he : c.len.toNat - 64 * k = 64
      · simp [he]
      · simp [hc]; omega
    · simp [hc]
      constructor
      · omega
      · intro e
        have := congrArg BitVec.toNat e
        simp at this; omega
  apply ChaCha20Policy.evBcond hb2 blsOff clrOff 9 (brImm8 blsOff clrOff) pc1 (by decide) bls_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
  · intro hT
    rw [cz] at hT
    have hle : c.len.toNat - 64 * k ≤ 64 := by simpa using hT
    apply kdone _ (ChaCha20Setup.setReg15_pc _ _)
      (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), r1 13 (by decide) (by decide), h.sp])
      ?_ hle
    simp only [M0Crypto.Armv6M.State.setReg]
    rw [m1]
    have hm := h.mem
    rwa [show min (64 * k + 64) c.len.toNat = c.len.toNat by omega] at hm
  · intro hF
    rw [cz] at hF
    have hgt : 64 < c.len.toNat - 64 * k := by simp at hF; omega
    generalize hu : s1.setReg 15 (c.base + BitVec.ofNat 32 (blsOff + 2)) = u
    have upc : u.pc = c.base + BitVec.ofNat 32 nxtOff := by rw [← hu, ChaCha20Setup.setReg15_pc, bls_next]
    have ur : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 15 → u.regs r = t.regs r := fun r a b => by
      rw [← hu, ChaCha20Setup.setReg15_regs _ _ r b, r1 r a b]
    have u13 : u.regs 13 = c.fp := by rw [ur 13 (by decide) (by decide), h.sp]
    have u4 : u.regs 4 = c.len - BitVec.ofNat 32 (64 * k) := by
      rw [← hu, ChaCha20Setup.setReg15_regs _ _ 4 (by decide), v4, hR]
    have um : u.mem = t.mem := by rw [← hu]; simp only [M0Crypto.Armv6M.State.setReg]; exact m1
    apply ChaCha20Policy.blockP hPc hb2 nxt nxtOff upc (by decide) nxt_at (by decide)
      (alignedAll_sp nxt u (spBlock_of_B (ok := fun p => p.2 % 4 == 0) (by decide) |>.mono
        (fun p hp => by simpa using hp)) (by rw [u13]; exact ChaCha20Setup.fp4 hv))
      (hnxt u upc u13) (by decide +kernel)
    obtain ⟨n13, nm⟩ := nxt_effect u c.fp u13
    have rd : ∀ j, j < 64 → read32 (execAll nxt u).mem (slot c.fp j) =
        if slotCtr = j then c.fw t slotCtr + 1#32 else if slotOutp = j then u.regs 3 + 64#32 else
        if slotInp = j then u.regs 2 + 64#32 else if slotLen = j then u.regs 4 - 64#32 else c.fw t j := fun j hj => by
      rw [nm]; simp (disch := omega) only [ChaCha20Output.read32_w_slot]
      simp only [sC, sO, sI, sL, um, ite_true, ite_false, eq_self_iff_true] <;> rfl
    have npc : (execAll nxt u).pc = c.base + BitVec.ofNat 32 bbackOff := by
      rw [execAll_pc _ _ (by decide), upc, ofNat_add_assoc, nxt_end]
    apply ChaCha20Policy.evB hb2 bbackOff bpreOff (brImm11 bbackOff bpreOff) npc (by decide) bback_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
    apply knext
    have fwv : ∀ j, j < 64 → c.fw ((execAll nxt u).setReg 15 (c.base + BitVec.ofNat 32 bpreOff)) j =
        read32 (execAll nxt u).mem (slot c.fp j) := fun j _ => rfl
    refine ⟨ChaCha20Setup.setReg15_pc _ _, by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), n13],
      fun i hi => ?_, ?_, ?_, ?_, ?_, by omega, h.ok⟩
    · rw [fwv _ (by omega), rd _ (by omega)]
      by_cases h12 : i = 12
      · subst h12
        rw [if_pos (show slotCtr = slotJ + 12 by decide), show slotCtr = slotJ + 12 by decide, hjs 12 (by decide), J_succ12]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hjs i hi,
          J_succ c k i hi h12]
    · rw [fwv _ (by omega), rd _ (by omega)]
      rw [if_neg (show ¬ (slotCtr = slotLen) by decide), if_neg (show ¬ (slotOutp = slotLen) by decide),
        if_neg (show ¬ (slotInp = slotLen) by decide), if_pos (show slotLen = slotLen from rfl)]
      rw [u4, sub64]
    · rw [fwv _ (by omega), rd _ (by omega)]
      rw [if_neg (show ¬ (slotCtr = slotOutp) by decide), if_pos (show slotOutp = slotOutp from rfl)]
      rw [ur 3 (by decide) (by decide), h.r3, add64]
    · rw [fwv _ (by omega), rd _ (by omega)]
      rw [if_neg (show ¬ (slotCtr = slotInp) by decide), if_neg (show ¬ (slotOutp = slotInp) by decide),
        if_pos (show slotInp = slotInp from rfl)]
      rw [ur 2 (by decide) (by decide), h.r2, add64]
    · simp only [M0Crypto.Armv6M.State.setReg]
      rw [nm, um]
      have hm := h.mem
      rw [show min (64 * k + 64) c.len.toNat = 64 * (k + 1) by omega] at hm
      exact c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot hm _ (by omega) _)
        _ (by omega) _) _ (by omega) _) _ (by omega) _

theorem lnext_select_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : Out c k t) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → c.len.toNat - 64 * k ≤ 64 → ReachW c.base Pc c.Wr u Q)
    (knext : ∀ u, BlockInv c (k + 1) u → ReachW c.base Pc c.Wr u Q) : ReachW c.base Pc c.Wr t Q := by
  apply ChaCha20Policy.ofEvPW
  apply lnext_select_S c hv hPc k t h (writeOnlyPolicy c.Wr) ?_ ?_ Q ?_ ?_
  · intro u _
    exact WritesTo.toEventAccesses (WritesTo.of_noWritesMem lenTest u (by decide) c.Wr)
  · intro u hp hs
    apply WritesTo.toEventAccesses
    intro e he y hy
    exact ChaCha20Setup.wr_frame (by
      have := frameWB_writes (n := chFrameWords) nxt u (by decide) e he y hy
      rwa [hs] at this) (by have := ChaCha20Layout.chFrameWords_eq; have := ChaCha20Layout.chStackWords_eq; omega)
  · intro u hp hs hm hl
    exact ChaCha20Policy.reachW_toEvP (kdone u hp hs hm hl)
  · intro u hu
    exact ChaCha20Policy.reachW_toEvP (knext u hu)

theorem lnext_select (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : Out c k t) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → c.len.toNat - 64 * k ≤ 64 → Reach c.base c.Wr u Q)
    (knext : ∀ u, BlockInv c (k + 1) u → Reach c.base c.Wr u Q) : Reach c.base c.Wr t Q := by
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine lnext_select_w c hv (fun _ _ => trivial) k t h Q ?_ ?_
  · intro u hp hs hm hl
    exact (kdone u hp hs hm hl).toReachW
  · intro u hu
    exact (knext u hu).toReachW

/-- The post-output transition accesses memory only after all output stores. -/
theorem lnext_after_output {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : Out c k t) :
    ReachS c.base (ChaCha20Policy.EvP Pc (fun pc kind y => PCBetween c.base n1Off Artifacts.Release.size pc ∧ writeOnlyPolicy c.Wr pc kind y)) t (fun u =>
      (c.len.toNat ≤ 64 * (k + 1) ∧ u.pc = c.base + BitVec.ofNat 32 clrOff ∧
        u.regs 13 = c.fp ∧ c.MemOk c.len.toNat u.mem) ∨
      (64 * (k + 1) < c.len.toNat ∧ BlockInv c (k + 1) u)) := by
  apply lnext_select_S c hv hPc k t h (fun pc kind y => PCBetween c.base n1Off Artifacts.Release.size pc ∧ writeOnlyPolicy c.Wr pc kind y)
  · intro u hp
    apply EventAccessesTo.and (traceAll_pcBetween c.base n1Off Artifacts.Release.size n1Off lenTest u
      (by decide) hp (by omega) (by decide +kernel))
    exact WritesTo.toEventAccesses (WritesTo.of_noWritesMem lenTest u (by decide) c.Wr)
  · intro u hp hs
    apply EventAccessesTo.and (traceAll_pcBetween c.base n1Off Artifacts.Release.size nxtOff nxt u
      (by decide) hp (by decide +kernel) (by decide +kernel))
    apply WritesTo.toEventAccesses
    intro e he y hy
    exact ChaCha20Setup.wr_frame (by
      have := frameWB_writes (n := chFrameWords) nxt u (by decide) e he y hy
      rwa [hs] at this) (by have := ChaCha20Layout.chFrameWords_eq; have := ChaCha20Layout.chStackWords_eq; omega)
  · intro u hp hs hm hl
    exact ReachS.done (Or.inl ⟨by omega, hp, hs, hm⟩)
  · intro u hu
    exact ReachS.done (Or.inr ⟨hu.lt, hu⟩)

/-- Continue after one output block, either finishing or entering the next block. -/
theorem lnext_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (k : Nat) (t : State) (h : Out c k t) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → ReachW c.base Pc c.Wr u Q)
    (knext : ∀ u, BlockInv c (k + 1) u → ReachW c.base Pc c.Wr u Q) : ReachW c.base Pc c.Wr t Q :=
  lnext_select_w c hv hPc k t h Q (fun u pc sp mem _ => kdone u pc sp mem) knext

theorem loop_next (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : Out c k t) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → Reach c.base c.Wr u Q)
    (knext : ∀ u, BlockInv c (k + 1) u → Reach c.base c.Wr u Q) : Reach c.base c.Wr t Q :=
  (lnext_w (Pc := fun _ => True) c hv (fun _ _ => trivial) k t h Q
    (fun u hp hs hm => (kdone u hp hs hm).toReachW) (fun u hu => (knext u hu).toReachW)).toReach

/-! ## The block loop -/

/-- **All blocks**: from `BlockInv c k` to `clrOff` with the whole output written. -/
theorem blocks_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → ReachW c.base Pc c.Wr u Q) :
    ∀ m k t, c.len.toNat ≤ 64 * (k + m) → BlockInv c k t → ReachW c.base Pc c.Wr t Q
  | 0, k, t, hm, h => absurd h.lt (by omega)
  | m + 1, k, t, hm, h => by
    apply ChaCha20Output.bpost_w c hv hPc k t h
    intro u hu
    apply ChaCha20Output.bout_w c hv hPc k u hu
    intro w hw
    apply lnext_w c hv hPc k w hw Q kdone
    intro v hv'
    exact blocks_w c hv hPc Q kdone m (k + 1) v (by omega) hv'

theorem blocks (c : Ctx) (hv : Valid c) (Q : State → Prop)
    (kdone : ∀ u, u.pc = c.base + BitVec.ofNat 32 clrOff → u.regs 13 = c.fp →
      c.MemOk c.len.toNat u.mem → Reach c.base c.Wr u Q) :
    ∀ m k t, c.len.toNat ≤ 64 * (k + m) → BlockInv c k t → Reach c.base c.Wr t Q := by
  intro m k t hm h
  exact (blocks_w (Pc := fun _ => True) c hv (fun _ _ => trivial) Q
    (fun u hp hs hm => (kdone u hp hs hm).toReachW) m k t hm h).toReach

/-! ## Clearing: `clrOff` - `zOff` -/

theorem clr_at : seqAt B clrOff clr := by decide

theorem stores_frameWB (n : Nat) (hn : n ≤ chFrameWords) : frameWB chFrameWords (stores n) = true := by
  have sFW := ChaCha20Layout.chFrameWords_eq
  simp only [frameWB, stores, List.all_map, List.all_eq_true, List.mem_range, Function.comp]
  intro i hi; simp; omega

theorem stores_falls (n : Nat) : (stores n).all Instr.falls = true := by
  simp [stores, Instr.falls]

theorem stores_regs (n : Nat) (s : State) (r : Reg) (hr : r.val ≠ 15) : (execAll (stores n) s).regs r = s.regs r :=
  execAll_regs_other _ _ r hr (by simp [stores, Instr.dsts])

theorem stores_zero : ∀ (n : Nat), n ≤ chFrameWords → ∀ s : State, s.regs 0 = 0 →
    ∀ i < n, read32 (execAll (stores n) s).mem (slot (s.regs 13) i) = 0
  | 0, _, _, _, i, hi => absurd hi (by omega)
  | n + 1, hn, s, h0, i, hi => by
    have sFW := ChaCha20Layout.chFrameWords_eq
    rw [stores, List.range_succ, List.map_append, execAll_append]
    simp only [List.map_cons, List.map_nil, execAll]
    rw [Frame.strSp_next _ 0 n (by omega)]
    simp only [M0Crypto.Proofs.toReg_0]
    rw [show (execAll (List.map (fun i => Instr.strSp 0 (BitVec.ofNat 8 i)) (List.range n)) s).regs 0 = 0 from
      (stores_regs n s 0 (by decide)).trans h0,
      show (execAll (List.map (fun i => Instr.strSp 0 (BitVec.ofNat 8 i)) (List.range n)) s).regs 13 = s.regs 13 from
      stores_regs n s 13 (by decide)]
    rw [read32_write32_slot' _ _ _ _ _ (by omega) (by omega)]
    split
    · rfl
    · exact stores_zero n (by omega) s h0 i (by omega)

theorem clr_effect (t : State) :
    let u := execAll clr t
    u.regs 0 = 0 ∧ u.regs 1 = 0 ∧ u.regs 2 = 0 ∧ u.regs 3 = 0 ∧ u.regs 12 = 0 ∧ u.regs 13 = t.regs 13 ∧
    (∀ i < chFrameWords, read32 u.mem (slot (t.regs 13) i) = 0) ∧
    (∀ y, ¬ InFrame (t.regs 13) chFrameWords y → u.mem y = t.mem y) := by
  obtain ⟨h0, h1, h2, h3, h12, h13⟩ := clear_regs t
  refine ⟨h0, h1, h2, h3, h12, h13, ?_, ?_⟩
  · intro i hi
    rw [clear_mem]
    exact stores_zero chFrameWords (by omega) (t.setReg 0 0)
      (by simp [M0Crypto.Armv6M.State.setReg]) i hi
  · intro y hy
    rw [clear_mem, frameWB_mem _ (t.setReg 0 0)
      (stores_frameWB chFrameWords (by omega)) (stores_falls chFrameWords) y]
    · rfl
    · simpa [M0Crypto.Armv6M.State.setReg] using hy

/-! ## Exits -/

theorem z_at : seqAt B zOff [.movImm 0 0] = true := by decide
theorem err_at : seqAt B errOff [.movImm 0 0, .dp .mvns 0 0] = true := by decide
theorem berr_at : instrAt B berrOff2 = some (.b (brImm11 berrOff2 epiOff)) := by decide +kernel

theorem outS_outF {c : Ctx} {y : Word} (h : OutS c y) : c.OutF y := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sFB := ChaCha20Layout.chFrameBytes_eq
  exact fun o ho => Region.ne h o (by omega)

theorem mP_outS (c : Ctx) (hv : Valid c) {y : Word} (h : OutS c y) : c.mP y = c.m0 y := by
  apply ChaCha20Return.mP_other
  intro k hk e
  have sFB := ChaCha20Layout.chFrameBytes_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have hs : c.sp0 - BitVec.ofNat 32 36 = c.fp + BitVec.ofNat 32 chFrameBytes := by
    rw [sFB]; simp only [Ctx.fp]; bv_omega
  apply Region.ne h (chFrameBytes + k) (by omega)
  rw [e, hs, ofNat_add_assoc]

/-- Saved-register slots are outside the frame (`chFrameBytes`) and the output. -/
theorem saved_memOk (c : Ctx) (hv : Valid c) {P : Nat} {m : Mem} (h : c.MemOk P m) (hP : P ≤ c.len.toNat) :
    ∀ i < 9, read32 m (slot c.fp (slotSaved + i)) = Frame.saved c.regs0 i := by
  intro i hi
  have sFB := ChaCha20Layout.chFrameBytes_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  rw [← ChaCha20Return.mP_saved c hv i hi]
  apply read32_congr
  intro q hq
  have hf := ChaCha20Setup.fp_toNat hv
  have := hv.spLo
  have sS := ChaCha20Return.ssv35
  have sB := ChaCha20Layout.chFrameBytes_eq
  have hy : slot c.fp (slotSaved + i) + BitVec.ofNat 32 q = c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * i + q) := by
    rw [Frame.slot_eq, ofNat_add_assoc]; congr 2; omega
  rw [hy]
  have hF : c.OutF (c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * i + q)) := fun o ho e => by
    have := congrArg BitVec.toNat e
    rw [toNat_add_ofNat _ _ (by have := c.sp0.isLt; omega), toNat_add_ofNat _ _ (by have := c.sp0.isLt; omega)] at this
    omega
  rw [h _ hF, if_neg]
  intro hlt
  obtain ⟨h1, h2, h3⟩ := hv.outF
  exact ne_of_disj (i := c.oidx (c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * i + q))) (j := chFrameBytes + 4 * i + q) h1 h2 h3
    (by omega) (by omega) (eq_add_sub c.out _).symm

theorem counterOk_zero (c : Ctx) (h : c.len = 0) : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true := by
  have := c.ctr.isLt
  simp [M0Crypto.Spec.Aead.counterOk, h]; omega

/-- From `zOff` with `MemOk P` for the full prefix: `movs r0, #0` and the epilogue. -/
theorem fin0_w {Pc Wr : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (hlr : (c.regs0 14).getLsbD 0 = true) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 zOff) (h13 : t.regs 13 = c.fp)
    (hsv : ∀ i < 9, read32 t.mem (slot c.fp (slotSaved + i)) = Frame.saved c.regs0 i)
    (P : State → Prop) (hP : ∀ u, u.mem = t.mem → u.regs 0 = 0 → P u) :
    ReachW c.base Pc Wr t fun u => u.pc = c.regs0 14 &&& ~~~1#32 ∧ u.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = c.regs0 r) ∧ P u := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ReachW.block hb2 [.movImm 0 0] zOff hpc (by decide) z_at (by decide)
    (by simp [alignedAll, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _)
    (ChaCha20Policy.chaRegion hPc (by decide +kernel))
  generalize hs : execAll [.movImm 0 0] t = s1
  have s0 : s1.regs 0 = 0 := by
    rw [← hs]
    simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Proofs.toReg_0]
    simp (config := { decide := true }) only [ite_true, ite_false]
  have sr : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → s1.regs r = t.regs r := fun r a b => by
    have hd : [Instr.movImm 0 0].all (fun i => !(i.dsts.contains r.val)) = true := by
      simp only [List.all_cons, List.all_nil, Instr.dsts, M0Crypto.Proofs.toReg_0, Bool.and_true,
        Bool.not_eq_true', List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne]
      simpa using a
    rw [← hs]; exact execAll_regs_other [Instr.movImm 0 0] t r b hd
  have sm : s1.mem = t.mem := by rw [← hs]; exact execAll_mem [Instr.movImm 0 0] t (by decide)
  have spc : s1.pc = c.base + BitVec.ofNat 32 epiOff := by
    rw [← hs, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc, z_next]
  apply (ChaCha20Return.ret_w c hv Wr hPc s1 spc (by rw [sr 13 (by decide) (by decide), h13])
    (fun i hi => by rw [sm]; exact hsv i hi) hlr).mono (fun _ _ h => h)
  rintro u ⟨upc, usp, ucal, ulow, umem⟩
  exact ⟨upc, usp, ucal, hP u (umem.trans sm) ((ulow 0 (.inl (by decide))).trans s0)⟩

/-- From `zOff` with `MemOk P` for the full prefix: `movs r0, #0` and the epilogue. -/
theorem fin0 (c : Ctx) (hv : Valid c) {Wr : Word → Prop} (hlr : (c.regs0 14).getLsbD 0 = true) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 zOff) (h13 : t.regs 13 = c.fp)
    (hsv : ∀ i < 9, read32 t.mem (slot c.fp (slotSaved + i)) = Frame.saved c.regs0 i)
    (P : State → Prop) (hP : ∀ u, u.mem = t.mem → u.regs 0 = 0 → P u) :
    Reach c.base Wr t fun u => u.pc = c.regs0 14 &&& ~~~1#32 ∧ u.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = c.regs0 r) ∧ P u :=
  (fin0_w (Pc := fun _ => True) c hv (fun _ _ => trivial) hlr t hpc h13 hsv P hP).toReach

theorem mP_saved' (c : Ctx) (hv : Valid c) : ∀ i < 9, read32 c.mP (slot c.fp (slotSaved + i)) = Frame.saved c.regs0 i :=
  fun i hi => ChaCha20Return.mP_saved c hv i hi

theorem wrOk_wr {c : Ctx} {y : Word} (h : WrOk c y) : c.Wr y := by
  rcases h with h | h
  · exact .inl (Region.exists h)
  · exact .inr h.2

/-- **Whole function, as a run of the release bytes**: every call satisfying `Valid` and
`Entry` reaches the return address in a `Result` state, writing only the frame and output. -/
theorem xor_reach_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (s : State) (h : ChaCha20Setup.Entry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachW c.base Pc (WrOk c) s fun u => u.pc = c.regs0 14 &&& ~~~1#32 ∧ Result c u := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sFB := ChaCha20Layout.chFrameBytes_eq
  have sJ : ChaCha20Layout.slotJ = 16 := by decide
  apply ChaCha20Setup.checks_w c hv (WrOk c) (fun o ho => .inl (Region.mk ho rfl)) hPc s h
  · -- len = 0
    intro t pc sp mem hz
    have hok := counterOk_zero c hz
    apply (fin0_w c hv hPc hlr t pc sp (by rw [mem]; exact mP_saved' c hv) (fun u => u.mem = t.mem ∧ u.regs 0 = 0)
      (fun u a b => ⟨a, b⟩)).mono (fun _ _ h => h)
    rintro u ⟨upc, usp, ucal, um, u0⟩
    refine ⟨upc, upc, usp, ucal, by rw [u0, hok]; rfl, fun y hy => ?_, fun _ hne => absurd hz hne⟩
    rw [um, mem, if_neg (by rw [hz]; simp), mP_outS c hv hy]
  · -- counter overflow
    intro t pc sp mem _ hok
    apply ReachW.block hb2 [.movImm 0 0, .dp .mvns 0 0] errOff pc (by decide) err_at (by decide)
      (by simp [alignedAll, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _)
      (ChaCha20Policy.chaRegion hPc (by decide +kernel))
    generalize hs : execAll [.movImm 0 0, .dp .mvns 0 0] t = s1
    have s0 : s1.regs 0 = ~~~0 := by
      rw [← hs]
      simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
        M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0]
      simp (config := { decide := true }) only [ite_true, ite_false]
    have sr : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → s1.regs r = t.regs r := fun r a b => by
      have hd : [Instr.movImm 0 0, Instr.dp .mvns 0 0].all (fun i => !(i.dsts.contains r.val)) = true := by
        simp only [List.all_cons, List.all_nil, Instr.dsts, M0Crypto.Proofs.toReg_0, Bool.and_true,
          Bool.not_eq_true', List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne]
        simpa using a
      rw [← hs]; exact execAll_regs_other _ t r b hd
    have sm : s1.mem = t.mem := by rw [← hs]; exact execAll_mem _ t (by decide)
    have spc : s1.pc = c.base + BitVec.ofNat 32 berrOff2 := by
      rw [← hs, execAll_pc _ _ (by decide), pc, ofNat_add_assoc, err_next]
    apply ReachW.b hb2 berrOff2 epiOff (brImm11 berrOff2 epiOff) spc (by decide) berr_at (by decide) (by decide +kernel)
      (ChaCha20Policy.chaAt hPc (by decide +kernel))
    apply (ChaCha20Return.ret_w c hv (WrOk c) hPc _ (ChaCha20Setup.setReg15_pc _ _)
      (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), sr 13 (by decide) (by decide), sp])
      (fun i hi => by simp only [M0Crypto.Armv6M.State.setReg]; rw [sm, mem]; exact mP_saved' c hv i hi) hlr).mono (fun _ _ h => h)
    rintro u ⟨upc, usp, ucal, ulow, um⟩
    refine ⟨upc, upc, usp, ucal, ?_, fun y hy => ?_, fun h' => absurd h' (by rw [hok]; decide)⟩
    · rw [ulow 0 (.inl (by decide)), ChaCha20Setup.setReg15_regs _ _ 0 (by decide), s0, hok]; rfl
    · rw [um]; simp only [M0Crypto.Armv6M.State.setReg]
      rw [sm, mem, hok]; simp only [Bool.false_eq_true, false_and, if_false]; exact mP_outS c hv hy
  · -- accepted
    intro t hacc
    apply ReachW.monoW (Wr := c.Wr) _ (fun y hy => by
      rcases hy with ⟨o, ho, rfl⟩ | h'
      · exact .inl (Region.mk ho rfl)
      · exact .inr ⟨hacc.ok, h'⟩)
    apply ChaCha20Init.init_w c hv hPc t hacc
    intro t0 hb0
    apply blocks_w c hv hPc _ _ (c.len.toNat / 64 + 1) 0 t0 (by omega) hb0
    intro u upc usp umem
    have sFW := ChaCha20Layout.chFrameWords_eq
    apply ReachW.blockR (ChaCha20Policy.chaRegion hPc (by decide +kernel)) hb2 upc (by decide) clr_at (by decide)
      (clear_aligned u (by rw [usp]; exact ChaCha20Setup.fp4 hv))
      (fun e he y ⟨a, ha, _, q, hq, hy⟩ => by
        have ham : a ∈ (traceAll clr u).flatMap Event.accesses := List.mem_flatMap.mpr ⟨e, he, ha⟩
        rw [clear_accesses] at ham
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ham
        have hi' := List.mem_range.mp hi
        apply ChaCha20Setup.wr_frame (c := c) (n := chFrameWords)
        · refine ⟨4 * i + q, by simp at hq; omega, ?_⟩
          rw [hy, usp]
          simp [slot, ofNat_add_assoc]
        · omega)
    obtain ⟨-, -, -, -, -, v13, vz, vm⟩ := clr_effect u
    have vmem : c.MemOk c.len.toNat (execAll clr u).mem := fun y hy => by
      rw [vm y (by rw [usp]; rintro ⟨o, ho, rfl⟩; exact hy o (by omega) rfl)]; exact umem y hy
    apply (fin0_w c hv hPc hlr _ (by rw [execAll_pc _ _ (by decide), upc, ofNat_add_assoc, clr_end])
      (by rw [v13, usp]) (saved_memOk c hv vmem (Nat.le_refl _))
      (fun w => w.mem = (execAll clr u).mem ∧ w.regs 0 = 0) (fun w a b => ⟨a, b⟩)).mono (fun _ _ h => h)
    rintro w ⟨wpc, wsp, wcal, wm, w0⟩
    refine ⟨wpc, wpc, wsp, wcal, by rw [w0, hacc.ok]; rfl, fun y hy => ?_, fun _ _ i hi => ?_⟩
    · rw [wm, vmem y (outS_outF hy), hacc.ok]
      by_cases hl : c.oidx y < c.len.toNat
      · rw [if_pos hl, if_pos ⟨rfl, hl⟩]
      · rw [if_neg hl, if_neg (fun e => hl e.2), mP_outS c hv hy]
    · rw [wm, ← usp]; exact vz i hi

/-- **Whole function, as a run of the release bytes**: every call satisfying `Valid` and
`Entry` reaches the return address in a `Result` state, writing only the frame and output. -/
theorem xor_reach (c : Ctx) (hv : Valid c) (s : State) (h : ChaCha20Setup.Entry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base (WrOk c) s fun u => u.pc = c.regs0 14 &&& ~~~1#32 ∧ Result c u :=
  (xor_reach_w (Pc := fun _ => True) c hv (fun _ _ => trivial) s h hlr).toReach

/-! ## The whole-function theorem -/

/-- **`m0c_chacha20_xor` (release bytes, Harvard model of the final artifact).** For every
valid call (`Pre`: `Valid`, that is alignment, non-overlap, exact in-place or disjoint buffers and
code in memory; entry state `Entry`; a Thumb return address outside the artifact), the
run to the return address terminates in a `Result` state: SP and r4-r11 restored, r0 = 0 iff the
RFC 8439 counter range fits, the output buffer holds RFC 8439 ChaCha20 of the input (on success),
all other memory outside the 176 stack bytes unchanged, the 140-byte frame zeroed after a
non-empty call; and every write lies in the 176 stack bytes or, only if the call is accepted,
the output buffer (`WrOk`). Reads and intermediate SP values are not bounded here. -/
theorem xor_correct (c : Ctx) (s : State) (hp : Pre c s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil c.ret fuel s = .ok (s', tr) ∧
      Result c s' ∧ WritesTo (WrOk c) tr := by
  obtain ⟨hv, h, hlr, hret⟩ := hp
  replace hret := Region.ne hret
  have sSB := ChaCha20Layout.chStackBytes_eq
  have hc : CodeAt s.mem c.base B := by rw [h.mem]; exact hv.code
  obtain ⟨n, hn⟩ := Reach.runUntil (P := Result c) hc
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases wrOk_wr hy with ⟨o, ho, rfl⟩ | hl
      · obtain ⟨h1, h2, h3⟩ := hv.codeF
        exact ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) (by omega)
      · obtain ⟨h1, h2, h3⟩ := hv.codeO
        rw [eq_add_sub c.out y]
        exact ne_of_disj h2 h1 (by omega) hl hi)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    (xor_reach c hv s h hlr)
  exact ⟨n, fun fuel hf => by
    obtain ⟨s', tr, hr, hP, hw⟩ := hn fuel hf
    exact ⟨s', tr, hr, hP, hw⟩⟩

/-- On success the output buffer is exactly RFC 8439 §2.4 ChaCha20 of the input. -/
theorem result_output (c : Ctx) (hv : Valid c) {t : State} (h : Result c t)
    (hok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true) :
    Ctx.bytesAt t.mem c.out c.len.toNat = M0Crypto.Spec.Aead.chacha20 c.keyB c.ctr.toNat c.nonceB c.msg := by
  have hl : (M0Crypto.Spec.Aead.chacha20 c.keyB c.ctr.toNat c.nonceB c.msg).length = c.len.toNat := by
    rw [ChaCha20Spec.chacha20_length, ChaCha20Output.msg_length]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < c.len.toNat
  · rw [Frame.bytesAt_get _ _ _ _ hi, List.getElem?_eq_getElem (by rw [hl]; exact hi)]
    have hy : OutS c (c.out + BitVec.ofNat 32 i) := Region.not fun o ho => by
      have sSB := ChaCha20Layout.chStackBytes_eq
      obtain ⟨h1, h2, h3⟩ := hv.outF
      exact ne_of_disj h1 h2 h3 hi (by omega)
    rw [h.mem _ hy, ChaCha20Output.oidx_out c hv i hi, if_pos ⟨hok, Region.mk hi rfl⟩, Ctx.outB, getElem!_pos _ i (by rw [hl]; exact hi)]
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega), List.getElem?_eq_none (by rw [hl]; omega)]

end M0Crypto.Release.ChaCha20Xor
