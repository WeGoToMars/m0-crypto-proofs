import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305BlocksCorrect
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-!
Caller-visible execution postconditions: preserved memory, h publication,
nonempty-call scratch clearing and zero-block behavior. `blocks_execution_safe`
collects the execution, register, write-bound, memory-frame and clearing results.
Read-address bounds, timing traces and RFC modular refinement are separate.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local irreducible] body loadState oneBlock loopState

/-- Value just before publishing h and clearing scratch. Used only for nonempty calls. -/
def finalLoop (c : BCtx) (s : State) : State :=
  loopState c.base c.count.toNat (execAll setup
    ((execAll prologue s).setReg 15 (c.base + BitVec.ofNat 32 setupAt)))

theorem finalLoop_sp (c : BCtx) (s : State) (he : BEntry c s) :
    (finalLoop c s).regs 13 = c.fp := by
  rw [finalLoop, (loop_regs _ _ _).2.2, (setup_effect _).2.2.1,
    setReg_regs_ne _ 15 13 _ (by decide)]
  exact (prologue_effect c s he).2.1

theorem finalLoop_ctx (c : BCtx) (s : State) (he : BEntry c s) :
    (finalLoop c s).regs 7 = c.ctx := by
  rw [finalLoop, (loop_regs _ _ _).1, (setup_effect _).1,
    setReg_regs_ne _ 15 0 _ (by decide)]
  exact (prologue_effect c s he).2.2.1

theorem result_cleared (c : BCtx) (s t : State) (he : BEntry c s) (ht : BResult c s t)
    (hn : c.count ≠ 0#32) :
    (∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → t.regs r = 0#32) ∧
    (∀ o < frameBytes, t.mem (c.fp + BitVec.ofNat 32 o) = 0#8) := by
  constructor
  · intro r hr
    rw [ht.scratch r hr, afterBlocks, ite_eq_right hn]
    exact (publish_effect _).2.1 r hr
  · intro o ho
    rw [ht.mem, afterBlocks, ite_eq_right hn, (publish_effect _).1]
    change publishMem (finalLoop c s) (c.fp + BitVec.ofNat 32 o) = _
    have hw : read32 (publishMem (finalLoop c s)) (slot c.fp (o/4)) = 0#32 := by
      unfold publishMem
      rw [finalLoop_sp c s he]
      change read32 _ (c.fp + BitVec.ofNat 32 (4*(o/4))) = _
      have hfb : frameBytes = 4 * frameWords := rfl
      have hfw : frameWords ≤ 2^28 := by decide
      rw [Frame.read32_storeWords_same _ c.fp (List.replicate frameWords 0#32) (o/4)
        (by simp; omega) (by simp only [List.length_replicate]; exact hfw)]
      exact List.getElem_replicate _
    have b := byte_of_read32 (publishMem (finalLoop c s)) (slot c.fp (o/4)) (o%4) (by omega)
    rw [hw] at b
    have addr : slot c.fp (o/4) + BitVec.ofNat 32 (o%4) = c.fp + BitVec.ofNat 32 o := by
      rw [slot, ofNat_add_assoc]; congr 2; omega
    rw [addr] at b
    simpa using b

/-- h words published after the final block. No modular-correctness assumption
is hidden here: the right side is the instruction-level loop state. -/
theorem result_h (c : BCtx) (hv : BValid c) (s t : State) (he : BEntry c s)
    (ht : BResult c s t) (hn : c.count ≠ 0#32) (j : Nat) (hj : j < 5) :
    read32 t.mem (slot c.ctx j) =
      (if j < 4 then (finalLoop c s).regs ⟨8+j, by omega⟩ else (finalLoop c s).regs 14) := by
  rw [ht.mem, afterBlocks, ite_eq_right hn, (publish_effect _).1]
  change read32 (publishMem (finalLoop c s)) (slot c.ctx j) = _
  unfold publishMem
  rw [finalLoop_ctx c s he, finalLoop_sp c s he]
  rw [read32_congr (m := storeWords (finalLoop c s).mem c.ctx
    [(finalLoop c s).regs 8, (finalLoop c s).regs 9, (finalLoop c s).regs 10,
      (finalLoop c s).regs 11, (finalLoop c s).regs 14])]
  · have h := Frame.read32_storeWords_same (finalLoop c s).mem c.ctx
      [(finalLoop c s).regs 8, (finalLoop c s).regs 9, (finalLoop c s).regs 10,
        (finalLoop c s).regs 11, (finalLoop c s).regs 14] j (by simp; omega) (by simp)
    change read32 _ (c.ctx + BitVec.ofNat 32 (4*j)) = _
    rw [h]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with
      rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro k hk
    apply storeWords_other
    intro i q hi hq heq
    simp only [List.length_replicate] at hi
    have hfw : frameWords = 7 := by decide
    obtain ⟨h1, h2, h3⟩ := hv.ctxS
    apply ne_of_disj h1 h2 h3 (i := 4*j+k) (j := 4*i+q) (by omega) (by omega)
    rw [slot, ofNat_add_assoc, ofNat_add_assoc] at heq
    exact heq

/-- A successful Harvard run changes memory only at its reported write addresses. -/
theorem runH_mem_other {base : Word} : ∀ n (s t : State) tr,
    runH B base n s = .ok (t, tr) → ∀ y, (∀ e ∈ tr, ¬ Writes e.accesses y) → t.mem y = s.mem y
  | 0, s, t, tr, h, y, _ => by
    simp only [runH, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | n+1, s, t, tr, h, y, hy => by
    simp only [runH] at h
    split at h
    · cases h
    · rename_i s1 e he
      split at h
      · cases h
      · rename_i t1 es hes
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [runH_mem_other n s1 t1 es hes y (fun e he' => hy e (List.mem_cons_of_mem _ he'))]
        unfold stepH at he
        try dsimp only at he
        split at he
        · cases he
        split at he
        · cases he
        split at he
        try dsimp only at he
        split at he
        · split at he
          · rename_i t' hex
            simp only [Except.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact exec_mem_other _ _ _ hex y (hy _ List.mem_cons_self)
          · cases he
        · cases he
        · cases he

/-- Every byte outside the 64-byte stack window and (nonempty calls only) h words
is preserved. In particular a zero-block call cannot modify the context. -/
theorem result_frame (c : BCtx) (hv : BValid c) (s t : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) (ht : BResult c s t) :
    ∀ y, ¬ c.Wr y → t.mem y = c.m0 y := by
  obtain ⟨n, u, tr, hr, hw, hu⟩ := blocks_reach c hv s he hlr
  intro y hy
  rw [ht.mem, ← hu.mem, ← he.mem]
  exact runH_mem_other n s u tr hr y (fun e he hw' => hy (hw e he y hw'))

theorem result_zero (c : BCtx) (s t : State) (he : BEntry c s) (ht : BResult c s t)
    (hz : c.count = 0#32) : t.mem = c.mP ∧
    (∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → t.regs r = c.regs0 r) := by
  refine ⟨?_, ?_⟩
  · rw [ht.mem, afterBlocks, ite_eq_left hz]
    exact (prologue_effect c s he).1
  · intro r hr
    have hr15 : r.val ≠ 15 := by omega
    have hreg : (execAll prologue s).regs r = s.regs r := by
      apply execAll_regs_other _ _ _ hr15
      simp [prologue, Instr.dsts, Frame.listRegs_f0]
      omega
    rw [ht.scratch r hr, afterBlocks, ite_eq_left hz, hreg, he.regs]

theorem result_key_preserved (c : BCtx) (hv : BValid c) (s t : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) (ht : BResult c s t) (o : Nat) (hlo : 20 ≤ o) (hhi : o < 64) :
    t.mem (c.ctx + BitVec.ofNat 32 o) = c.m0 (c.ctx + BitVec.ofNat 32 o) := by
  apply result_frame c hv s t he hlr ht
  rintro (⟨k, hk, heq⟩ | ⟨_, k, hk, heq⟩)
  · obtain ⟨h1, h2, h3⟩ := hv.ctxS
    exact ne_of_disj h1 h2 h3 hhi hk heq
  · have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have hn := hv.ctxS.1
    omega

/-- Complete execution contract, with memory preservation and nonempty-call
scratch clearing made explicit. No RFC accumulator equality is asserted here. -/
theorem blocks_execution_safe (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      BResult c s t ∧ WritesTo c.Wr tr ∧
      (∀ y, ¬ c.Wr y → t.mem y = c.m0 y) ∧
      (c.count ≠ 0#32 →
        (∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → t.regs r = 0#32) ∧
        (∀ o < frameBytes, t.mem (c.fp + BitVec.ofNat 32 o) = 0#8)) := by
  obtain ⟨n, h⟩ := blocks_execution c hv s he hlr hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hr, ht, hw⟩ := h fuel hf
  exact ⟨t, tr, hr, ht, hw, result_frame c hv s t he hlr ht, result_cleared c s t he ht⟩

end M0Crypto.Release.Poly1305Blocks
