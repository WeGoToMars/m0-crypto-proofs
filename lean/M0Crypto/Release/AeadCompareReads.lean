import M0Crypto.Release.AeadMacReads
import M0Crypto.Release.AeadCompare

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read policy of the tag comparison

The first `ldrb` of the compare loop (`decCmpLAt`) reads the caller's tag; the second reads the
stack copy of the expected tag.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5

theorem cmpL_ok (base : Word) (Rd : Word → Prop) (u : State)
    (h1 : Rd (u.regs 1 + u.regs 4)) (h2 : Rd (u.regs 2 + u.regs 4)) :
    BlockOk (RdP base Rd) cmpL u := by
  have := (blockOk_events_iff (p := fun e => SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y)
    cmpL u).mpr ?_
  · exact this
  intro e he _ y hy
  simp only [cmpL, traceAll, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Instr.accesses, Instr.exec, Reads, MemOp.isLoad, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg] at hy
  · obtain ⟨k, hk, rfl⟩ := hy
    simp [MemOp.width] at hk; subst hk
    simpa using h1
  · obtain ⟨k, hk, rfl⟩ := hy
    simp [MemOp.width] at hk; subst hk
    simpa [Instr.next, Instr.exec, Instr.exec.memOp, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg] using h2

theorem compare_loop_r {Rd : Word → Prop} (base tag expected : Word) (M : Mem) (R : Reg → Word)
    (hb : base.toNat % 4 = 0)
    (hrb : NoSite base (base + BitVec.ofNat 32 decCmpBrAt))
    (hRt : ∀ j < 16, Rd (tag + BitVec.ofNat 32 j)) (hRe : ∀ j < 16, Rd (expected + BitVec.ofNat 32 j)) :
    ∀ rem k, k+rem=16 → k<16 → ∀ s : State,
      s.pc = base+BitVec.ofNat 32 decCmpLAt → s.regs 1=tag → s.regs 2=expected → s.regs 4=BitVec.ofNat 32 k →
      s.mem=M → (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → s.regs r = R r) →
      (s.regs 3=0#32 ↔ ∀ j<k, M (tag+BitVec.ofNat 32 j)=M (expected+BitVec.ofNat 32 j)) →
      ReachS base (RdP base Rd) s (fun t => t.pc=base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=M ∧
        (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r = R r) ∧
        (t.regs 3=0#32 ↔ Ctx.bytesAt M tag 16 = Ctx.bytesAt M expected 16))
  | 0, k, h, hk, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | rem+1, k, h, hk, s, hp, h1, h2, h4, hm, hr, hz => by
    obtain ⟨e3, e4, ez, em, er⟩ := cmpL_effect s
    refine ReachS.block (by omega) cmpL decCmpLAt s hp (by decide) (by decide) (by decide)
      (by simp [alignedAll, cmpL, Instr.accesses, Access.aligned, MemOp.isLoad, MemOp.width, Nat.mod_one])
      (cmpL_ok base Rd s (by rw [h1, h4]; exact hRt k hk) (by rw [h2, h4]; exact hRe k hk)) ?_
    generalize ht : execAll cmpL s = t at e3 e4 ez em er
    have tp : t.pc = base+BitVec.ofNat 32 decCmpBrAt := by rw [← ht, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
    have teq : t.regs 3=0#32 ↔ ∀ j<k+1, M (tag+BitVec.ofNat 32 j)=M (expected+BitVec.ofNat 32 j) := by
      rw [e3, BitVec.or_eq_zero_iff, hz, hm, h1, h2, h4, read8_xor_zero]
      constructor
      · rintro ⟨hprev, hnew⟩ j hj
        by_cases hjk : j<k
        · exact hprev j hjk
        · simpa only [show j=k by omega] using hnew
      · intro hall; exact ⟨fun j hj => hall j (by omega), hall k (by omega)⟩
    have t4 : t.regs 4=BitVec.ofNat 32 (k+1) := by rw [e4, h4]; bv_omega
    have tz : t.z = decide (k+1=16) := by
      rw [ez, h4]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro e; have := congrArg BitVec.toNat e
        simp [BitVec.toNat_add, BitVec.toNat_sub] at this; omega
      · intro e
        rw [show BitVec.ofNat 32 k+1#32 = 16#32 by bv_omega, BitVec.sub_self]
    apply ReachS.bcondW (Pn := NoSite base) (Wr := fun _ => False) (noP base Rd) hrb (by omega) decCmpLAt 1 (brImm8 decCmpBrAt decCmpLAt) tp (by decide) (by decide +kernel)
      (by decide) (by rw [se_f8]; exact back_target decCmpLAt (seqSize cmpL))
    · intro hn
      have hne : k+1≠16 := by simpa [condPassed, tz] using hn
      apply compare_loop_r base tag expected M R hb hrb hRt hRe rem (k+1) (by omega) (by omega)
        (t.setReg 15 (base+BitVec.ofNat 32 decCmpLAt)) (by rw [M0Crypto.Armv6M.State.pc, setReg_eq])
        (by rw [setReg_ne _ _ _ _ (by decide), er 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1])
        (by rw [setReg_ne _ _ _ _ (by decide), er 2 (by decide) (by decide) (by decide) (by decide) (by decide), h2])
        (by rw [setReg_ne _ _ _ _ (by decide)]; exact t4) (by rw [setReg_mem, em, hm])
        (fun r a b => by rw [setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), er r (by omega) (by omega) (by omega) (by omega) b, hr r a b])
        (by rw [setReg_ne _ _ _ _ (by decide)]; exact teq)
    · intro heq
      have hk1 : k+1=16 := by simpa [condPassed, tz] using heq
      have hfall : decCmpBrAt + 2 = decVerdictAt := by decide
      apply ReachS.done
      refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq, hfall], by rw [setReg_mem, em, hm],
        fun r a b => by rw [setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), er r (by omega) (by omega) (by omega) (by omega) b, hr r a b], ?_⟩
      rw [setReg_ne _ _ _ _ (by decide), teq, hk1]
      constructor
      · intro he
        apply List.ext_getElem?
        intro j
        by_cases hj : j<16
        · rw [Frame.bytesAt_get _ _ _ _ hj, Frame.bytesAt_get _ _ _ _ hj, he j hj]
        · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega),
            List.getElem?_eq_none (by rw [bytesAt_length]; omega)]
      · intro eq j hj
        have := congrArg (fun bs => bs[j]?) eq
        simpa only [Frame.bytesAt_get _ _ _ _ hj, Option.some.injEq] using this
theorem compare_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decCmpAAt) (hs : s.regs 13=c.A) (hh : Hi c s.mem)
    (hrA : InRegion (NoSite c.base) c.base decCmpAAt (seqSize cmpA))
    (hrb : NoSite c.base (c.base + BitVec.ofNat 32 decCmpBrAt))
    (hRt : ∀ j < 16, Rd (c.tag + BitVec.ofNat 32 j)) (hRe : ∀ j < 16, Rd (c.A + 72#32 + BitVec.ofNat 32 j)) :
    ReachS c.base (RdP c.base Rd) s (fun t => t.pc=c.base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=s.mem ∧
      (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r=s.regs r) ∧
      (t.regs 3=0#32 ↔ Ctx.bytesAt s.mem c.tag 16=Ctx.bytesAt s.mem (c.A+72#32) 16)) := by
  obtain ⟨e1, e2, e3, e4, em, er⟩ := cmpA_effect s
  rw [hs, hh.tag] at e1
  rw [hs] at e2
  apply ReachS.blockW (Pn := NoSite c.base) (Wr := fun _ => False) (noP c.base Rd) hrA (by have := hv.base4; omega) hp (by decide) (by decide) (by decide)
    (alignedAll_sp _ _ (sp_al (by decide)) (by rw [hs, hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega))
    (WritesTo.of_noWritesMem _ _ (by decide) _)
  generalize hu : execAll cmpA s=u at e1 e2 e3 e4 em er
  have up : u.pc=c.base+BitVec.ofNat 32 decCmpLAt := by rw [←hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  exact compare_loop_r c.base c.tag (c.A+72#32) s.mem s.regs hv.base4 hrb hRt hRe 16 0 rfl (by decide) u up e1 e2 e4 em er
    (by simp [e3])


end M0Crypto.Release.Aead
