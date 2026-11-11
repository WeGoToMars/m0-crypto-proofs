import M0Crypto.Release.Poly1305Loop
import M0Crypto.Release.Poly1305BlocksPost
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (p)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

def wordAt (m : Mem) (ctx : Word) (j : Nat) : Nat := (read32 m (slot ctx j)).toNat
def accAt (m : Mem) (ctx : Word) : Nat := Poly1305Arith.val5 (wordAt m ctx 0) (wordAt m ctx 1)
  (wordAt m ctx 2) (wordAt m ctx 3) (wordAt m ctx 4)
def keyAt (m : Mem) (ctx : Word) : Nat := Poly1305Arith.val4 (wordAt m ctx 5) (wordAt m ctx 6)
  (wordAt m ctx 7) (wordAt m ctx 8)
def keyAtOK (m : Mem) (ctx : Word) : Prop :=
  (wordAt m ctx 5 < 2^28 ∧ wordAt m ctx 6 < 2^28 ∧ wordAt m ctx 7 < 2^28 ∧ wordAt m ctx 8 < 2^28) ∧
  (wordAt m ctx 6 % 4 = 0 ∧ wordAt m ctx 7 % 4 = 0 ∧ wordAt m ctx 8 % 4 = 0) ∧
  (wordAt m ctx 9 = wordAt m ctx 6 + wordAt m ctx 6 / 4 ∧
   wordAt m ctx 10 = wordAt m ctx 7 + wordAt m ctx 7 / 4 ∧
   wordAt m ctx 11 = wordAt m ctx 8 + wordAt m ctx 8 / 4)

def start (c : BCtx) (s : State) : State :=
  execAll setup ((execAll prologue s).setReg 15 (c.base + BitVec.ofNat 32 setupAt))

theorem start_regs (c : BCtx) (s : State) (he : BEntry c s) :
    (start c s).regs 7 = c.ctx ∧ (start c s).regs 12 = c.pad ∧ (start c s).regs 13 = c.fp := by
  obtain ⟨_, sp, r0, _, _, r3, _⟩ := prologue_effect c s he
  rw [start]
  obtain ⟨s7, s12, s13, _⟩ := setup_effect ((execAll prologue s).setReg 15 (c.base + BitVec.ofNat 32 setupAt))
  simpa only [setReg_regs_ne _ 15 0 _ (by decide), setReg_regs_ne _ 15 3 _ (by decide),
    setReg_regs_ne _ 15 13 _ (by decide), r0, r3, sp] using And.intro s7 (And.intro s12 s13)

theorem mP_out (c : BCtx) (y : Word) (hy : ¬ InFrame c.fp 16 y) : c.mP y = c.m0 y := by
  unfold BCtx.mP
  rw [storeWords_other]
  · apply storeWords_other
    intro i k hi hk heq
    apply hy
    refine ⟨44+4*i+k, by simp at hi; omega, ?_⟩
    rw [heq]
    simp only [BCtx.fp]; bv_omega
  · intro i k hi hk heq
    apply hy
    refine ⟨28+4*i+k, by simp at hi; omega, ?_⟩
    rw [heq]
    simp only [BCtx.fp]; bv_omega

theorem start_out (c : BCtx) (s : State) (he : BEntry c s) (y : Word)
    (hy : ¬ InFrame c.fp 16 y) : (start c s).mem y = c.m0 y := by
  have hsm : slotMsg < 16 := by decide
  have hsc : slotCount < 16 := by decide
  obtain ⟨pm, sp, _⟩ := prologue_effect c s he
  rw [start, (setup_effect _).2.2.2, setReg_mem, setReg_regs_ne _ 15 13 _ (by decide), sp]
  rw [M0Crypto.Armv6M.write32_other, M0Crypto.Armv6M.write32_other, pm, mP_out c y hy]
  all_goals
    intro k hk heq; apply hy
    first
    | (refine ⟨4*slotMsg+k, by omega, ?_⟩; rw [heq, slot, ofNat_add_assoc]; done)
    | (refine ⟨4*slotCount+k, by omega, ?_⟩; rw [heq, slot, ofNat_add_assoc]; done)

theorem start_words (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s) (j : Nat) (hj : j < 16) :
    read32 (start c s).mem (slot c.ctx j) = read32 c.m0 (slot c.ctx j) := by
  apply read32_congr
  intro k hk
  apply start_out c s he
  rintro ⟨o, ho, heq⟩
  apply ne_of_disj hv.ctxS.1 hv.ctxS.2.1 hv.ctxS.2.2 (i := 4*j+k) (j := o) (by omega) ho
  rw [slot, ofNat_add_assoc] at heq
  exact heq

theorem setup_hval (s : State) : hval (execAll setup s) = accAt (execAll setup s).mem (s.regs 0) := by
  simp (config := { decide := true }) [hval, accAt, wordAt, setup, execAll, Instr.next, Instr.exec,
    Instr.exec.memOp, MemOp.width, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, lslC, slot]

theorem start_hval (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s) :
    hval (start c s) = accAt c.m0 c.ctx := by
  have h := setup_hval ((execAll prologue s).setReg 15 (c.base + BitVec.ofNat 32 setupAt))
  rw [setReg_regs_ne _ 15 0 _ (by decide), (prologue_effect c s he).2.2.1] at h
  change hval (start c s) = accAt (start c s).mem c.ctx at h
  rw [h]
  simp only [accAt, wordAt, start_words c hv s he 0 (by decide), start_words c hv s he 1 (by decide),
    start_words c hv s he 2 (by decide), start_words c hv s he 3 (by decide), start_words c hv s he 4 (by decide)]

theorem start_mp (c : BCtx) (s : State) (he : BEntry c s) : mp (start c s) = c.msg := by
  obtain ⟨pm, sp, _, r1, _⟩ := prologue_effect c s he
  rw [mp, start, (setup_effect _).2.2.1, (setup_effect _).2.2.2,
    setReg_regs_ne _ 15 13 _ (by decide), sp,
    M0Crypto.Armv6M.read32_write32_slot _ _ _ slotCount slotMsg (by decide) (by decide),
    ite_eq_right (by decide : slotCount ≠ slotMsg), M0Crypto.Armv6M.read32_write32_same,
    setReg_regs_ne _ 15 1 _ (by decide), r1]

attribute [local irreducible] setup prologue start body loadState oneBlock loopState

theorem start_cw (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s) (j : Nat) (hj : j < 16) :
    cw (start c s) j = wordAt c.m0 c.ctx j := by
  rw [cw, (start_regs c s he).1, start_words c hv s he j hj]; rfl

theorem finalLoop_correct (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hn : c.count ≠ 0#32) (hk : keyAtOK c.m0 c.ctx)
    (hh : accAt c.m0 c.ctx < 5*2^128) (hp : c.pad.toNat ≤ 1) :
    hval (finalLoop c s) % p = Poly1305Spec.polyBlocks (keyAt c.m0 c.ctx) c.pad.toNat (accAt c.m0 c.ctx % p)
      (Ctx.bytesAt c.m0 c.msg (16*c.count.toNat)) ∧ hval (finalLoop c s) < 5*2^128 := by
  have hfw : frameWords ≤ 16 := by decide
  let u := start c s
  have regs := start_regs c s he
  have us : Sep u := by
    change Disj (u.regs 7) 64 (u.regs 13) (4 * frameWords)
    rw [regs.1, regs.2.2]
    obtain ⟨ha, hb, hd⟩ := hv.ctxS
    exact ⟨ha, by omega, by omega⟩
  have words : ∀ j < 16, cw u j = wordAt c.m0 c.ctx j := start_cw c hv s he
  have uk : KeyOK u := by
    unfold KeyOK
    rw [words 5 (by decide), words 6 (by decide), words 7 (by decide), words 8 (by decide),
      words 9 (by decide), words 10 (by decide), words 11 (by decide)]
    exact hk
  have uh : hval u < 5*2^128 := by rw [start_hval c hv s he]; exact hh
  have uh4 : (u.regs 14).toNat ≤ 4 := by simp only [hval, Poly1305Arith.val5] at uh; omega
  have mp' : mp u = c.msg := start_mp c s he
  have ur : rval u = keyAt c.m0 c.ctx := by
    simp only [rval, keyAt, words 5 (by decide), words 6 (by decide), words 7 (by decide), words 8 (by decide)]
  have um : Disj (mp u) (16*c.count.toNat) (u.regs 13) (4 * frameWords) := by
    rw [mp', regs.2.2]
    obtain ⟨ha, hb, hd⟩ := hv.msgS
    exact ⟨ha, by omega, by omega⟩
  have h := loop_correct c.base c.count.toNat (by
    have hn' : c.count.toNat ≠ 0 := by intro hz; apply hn; apply BitVec.eq_of_toNat_eq; exact hz
    omega) u us uk uh4 (by rw [regs.2.1]; exact hp) um
  have bm : Ctx.bytesAt u.mem c.msg (16*c.count.toNat) = Ctx.bytesAt c.m0 c.msg (16*c.count.toNat) := by
    apply bytes_congr
    intro o ho
    apply start_out c s he
    rintro ⟨q, hq, heq⟩
    exact ne_of_disj hv.msgS.1 hv.msgS.2.1 hv.msgS.2.2 ho hq heq
  rw [ur, regs.2.1, start_hval c hv s he, mp', bm] at h
  have eq : finalLoop c s = loopState c.base c.count.toNat (start c s) := by unfold finalLoop start; rfl
  rw [eq]
  exact h

theorem result_acc (c : BCtx) (hv : BValid c) (s t : State) (he : BEntry c s)
    (ht : BResult c s t) (hn : c.count ≠ 0#32) : accAt t.mem c.ctx = hval (finalLoop c s) := by
  unfold accAt wordAt
  rw [result_h c hv s t he ht hn 0 (by decide), result_h c hv s t he ht hn 1 (by decide),
    result_h c hv s t he ht hn 2 (by decide), result_h c hv s t he ht hn 3 (by decide),
    result_h c hv s t he ht hn 4 (by decide)]
  rfl

/-- Functional refinement of the entire `blocks` call, including count zero.
The key layout, lazy bound and high-bit argument are explicit preconditions. -/
theorem result_blocks_correct (c : BCtx) (hv : BValid c) (s t : State) (he : BEntry c s)
    (ht : BResult c s t) (hk : keyAtOK c.m0 c.ctx)
    (hh : accAt c.m0 c.ctx < 5*2^128) (hp : c.pad.toNat ≤ 1) :
    accAt t.mem c.ctx % p = Poly1305Spec.polyBlocks (keyAt c.m0 c.ctx) c.pad.toNat (accAt c.m0 c.ctx % p)
      (Ctx.bytesAt c.m0 c.msg (16*c.count.toNat)) ∧ accAt t.mem c.ctx < 5*2^128 := by
  by_cases hz : c.count = 0#32
  · have hm := (result_zero c s t he ht hz).1
    have hw : ∀ j, j < 5 → read32 t.mem (slot c.ctx j) = read32 c.m0 (slot c.ctx j) := by
      intro j hj
      rw [hm]; apply read32_congr
      intro k hkb; apply mP_out
      rintro ⟨q, hq, heq⟩
      apply ne_of_disj hv.ctxS.1 hv.ctxS.2.1 hv.ctxS.2.2 (i := 4*j+k) (j := q) (by omega) hq
      rw [slot, ofNat_add_assoc] at heq; exact heq
    have ha : accAt t.mem c.ctx = accAt c.m0 c.ctx := by
      simp only [accAt, wordAt, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
        hw 3 (by decide), hw 4 (by decide)]
    rw [ha, hz]
    change accAt c.m0 c.ctx % p = Poly1305Spec.polyBlocks _ _ _ [] ∧ _
    rw [Poly1305Spec.polyBlocks_nil]
    exact ⟨rfl, hh⟩
  · rw [result_acc c hv s t he ht hz]
    exact finalLoop_correct c hv s he hz hk hh hp

/-- Full single-memory execution with the RFC block-fold result. -/
theorem blocks_correct (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hk : keyAtOK c.m0 c.ctx) (hh : accAt c.m0 c.ctx < 5*2^128) (hp : c.pad.toNat ≤ 1)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧ BResult c s t ∧ WritesTo c.Wr tr ∧
      accAt t.mem c.ctx % p = Poly1305Spec.polyBlocks (keyAt c.m0 c.ctx) c.pad.toNat (accAt c.m0 c.ctx % p)
        (Ctx.bytesAt c.m0 c.msg (16*c.count.toNat)) ∧ accAt t.mem c.ctx < 5*2^128 := by
  obtain ⟨n, h⟩ := blocks_execution c hv s he hlr hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hr, ht, hw⟩ := h fuel hf
  exact ⟨t, tr, hr, ht, hw, result_blocks_correct c hv s t he ht hk hh hp⟩

end M0Crypto.Release.Poly1305Blocks
