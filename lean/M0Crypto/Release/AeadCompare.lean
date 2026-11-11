import M0Crypto.Release.AeadPrologue
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5

theorem cmpA_effect (s : State) :
    (execAll cmpA s).regs 1 = read32 s.mem (s.regs 13+108#32) ∧
    (execAll cmpA s).regs 2 = s.regs 13+72#32 ∧
    (execAll cmpA s).regs 3 = 0#32 ∧ (execAll cmpA s).regs 4 = 0#32 ∧
    (execAll cmpA s).mem = s.mem ∧
    (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → (execAll cmpA s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, fun r a b => execAll_regs_other _ _ _ b (by
    have h1 : r.val ≠ 1 := by omega
    have h2 : r.val ≠ 2 := by omega
    have h3 : r.val ≠ 3 := by omega
    have h4 : r.val ≠ 4 := by omega
    simp [cmpA, Instr.dsts, Fin.ext_iff, h1, h2, h3, h4]; omega)⟩ <;>
    simp [cmpA, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg]

theorem cmpL_effect (s : State) :
    (execAll cmpL s).regs 3 = s.regs 3 ||| (read8 s.mem (s.regs 1+s.regs 4) ^^^ read8 s.mem (s.regs 2+s.regs 4)) ∧
    (execAll cmpL s).regs 4 = s.regs 4+1#32 ∧
    (execAll cmpL s).z = (s.regs 4+1#32-16#32 == 0#32) ∧
    (execAll cmpL s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 3 → r.val ≠ 4 → r.val ≠ 5 → r.val ≠ 15 →
      (execAll cmpL s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, fun r h0 h3 h4 h5 h15 => execAll_regs_other _ _ _ h15
    (by simp [cmpL, Instr.dsts, MemOp.isLoad, Fin.ext_iff, h0, h3, h4, h5]; omega)⟩ <;>
    simp [cmpL, execAll, Instr.next, Instr.exec, Instr.exec.memOp, addFlags, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
      M0Crypto.Release.add_flags, M0Crypto.Release.sub_flags]
  all_goals rw [show (4294967279#32 : Word) = ~~~16#32 from rfl, M0Crypto.Release.sub_flags]

theorem read8_xor_zero (m : Mem) (a b : Word) : read8 m a ^^^ read8 m b = 0#32 ↔ m a = m b := by
  rw [BitVec.xor_eq_zero_iff, read8, read8]
  constructor
  · intro h
    have hh := congrArg (BitVec.setWidth 8) h
    simpa [byte_copy] using hh
  · intro h; rw [h]

theorem se_f8 : (((brImm8 decCmpBrAt decCmpLAt) ++ 0#1).signExtend 32 : Word) = -(BitVec.ofNat 32 (seqSize cmpL+4)) := by decide +kernel

/-- The compare always consumes all 16 bytes; the OR accumulator is zero exactly
when all bytes compared so far agree. This is a functional loop statement, not
a relational address and control trace theorem. -/
theorem compare_loop_w {Pc : Word → Prop} (base tag expected : Word) (M : Mem) (R : Reg → Word)
    (hb : base.toNat % 4 = 0)
    (hrL : InRegion Pc base decCmpLAt (seqSize cmpL)) (hrb : Pc (base + BitVec.ofNat 32 decCmpBrAt)) :
    ∀ rem k, k+rem=16 → k<16 → ∀ s : State,
      s.pc = base+BitVec.ofNat 32 decCmpLAt → s.regs 1=tag → s.regs 2=expected → s.regs 4=BitVec.ofNat 32 k →
      s.mem=M → (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → s.regs r = R r) →
      (s.regs 3=0#32 ↔ ∀ j<k, M (tag+BitVec.ofNat 32 j)=M (expected+BitVec.ofNat 32 j)) →
      ReachW base Pc (fun _ => False) s (fun t => t.pc=base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=M ∧
        (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r = R r) ∧
        (t.regs 3=0#32 ↔ Ctx.bytesAt M tag 16 = Ctx.bytesAt M expected 16))
  | 0, k, h, hk, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | rem+1, k, h, hk, s, hp, h1, h2, h4, hm, hr, hz => by
    obtain ⟨e3, e4, ez, em, er⟩ := cmpL_effect s
    apply ReachW.blockR hrL (by omega) hp (by decide) (by decide)
      (by decide) (by simp [alignedAll, cmpL, Instr.accesses, Access.aligned, MemOp.isLoad, MemOp.width, Nat.mod_one])
      (WritesTo.of_noWritesMem _ _ (by decide) _)
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
    apply ReachW.bcondR hrb (by omega) decCmpLAt 1 (brImm8 decCmpBrAt decCmpLAt) tp (by decide) (by decide +kernel)
      (by decide) (by rw [se_f8]; exact back_target decCmpLAt (seqSize cmpL))
    · intro hn
      have hne : k+1≠16 := by simpa [condPassed, tz] using hn
      apply compare_loop_w base tag expected M R hb hrL hrb rem (k+1) (by omega) (by omega)
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
/-- The comparison loop (see `compare_loop_w` for the region-tracked form). -/
theorem compare_loop (base tag expected : Word) (M : Mem) (R : Reg → Word)
    (hb : base.toNat % 4 = 0) :
    ∀ rem k, k+rem=16 → k<16 → ∀ s : State,
      s.pc = base+BitVec.ofNat 32 decCmpLAt → s.regs 1=tag → s.regs 2=expected → s.regs 4=BitVec.ofNat 32 k →
      s.mem=M → (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → s.regs r = R r) →
      (s.regs 3=0#32 ↔ ∀ j<k, M (tag+BitVec.ofNat 32 j)=M (expected+BitVec.ofNat 32 j)) →
      Reach base (fun _ => False) s (fun t => t.pc=base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=M ∧
        (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r = R r) ∧
        (t.regs 3=0#32 ↔ Ctx.bytesAt M tag 16 = Ctx.bytesAt M expected 16)) :=
  fun rem k h hk s hp h1 h2 h4 hm hr hz =>
    (compare_loop_w (Pc := fun _ => True) base tag expected M R hb (fun _ _ => trivial) trivial
      rem k h hk s hp h1 h2 h4 hm hr hz).toReach

/-- Complete 16-byte tag comparison, with no writes and no early exit. -/
theorem compare_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decCmpAAt) (hs : s.regs 13=c.A) (hh : Hi c s.mem)
    (hrA : InRegion Pc c.base decCmpAAt (seqSize cmpA))
    (hrL : InRegion Pc c.base decCmpLAt (seqSize cmpL)) (hrb : Pc (c.base + BitVec.ofNat 32 decCmpBrAt)) :
    ReachW c.base Pc (fun _ => False) s (fun t => t.pc=c.base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=s.mem ∧
      (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r=s.regs r) ∧
      (t.regs 3=0#32 ↔ Ctx.bytesAt s.mem c.tag 16=Ctx.bytesAt s.mem (c.A+72#32) 16)) := by
  obtain ⟨e1, e2, e3, e4, em, er⟩ := cmpA_effect s
  rw [hs, hh.tag] at e1
  rw [hs] at e2
  apply ReachW.blockR hrA (by have := hv.base4; omega) hp (by decide) (by decide) (by decide)
    (alignedAll_sp _ _ (sp_al (by decide)) (by rw [hs, hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega))
    (WritesTo.of_noWritesMem _ _ (by decide) _)
  generalize hu : execAll cmpA s=u at e1 e2 e3 e4 em er
  have up : u.pc=c.base+BitVec.ofNat 32 decCmpLAt := by rw [←hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  exact compare_loop_w c.base c.tag (c.A+72#32) s.mem s.regs hv.base4 hrL hrb 16 0 rfl (by decide) u up e1 e2 e4 em er
    (by simp [e3])


theorem compare_reach (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc=c.base+BitVec.ofNat 32 decCmpAAt) (hs : s.regs 13=c.A) (hh : Hi c s.mem) :
    Reach c.base (fun _ => False) s (fun t => t.pc=c.base+BitVec.ofNat 32 decVerdictAt ∧ t.mem=s.mem ∧
      (∀ r : Reg, 6 ≤ r.val → r.val ≠ 15 → t.regs r=s.regs r) ∧
      (t.regs 3=0#32 ↔ Ctx.bytesAt s.mem c.tag 16=Ctx.bytesAt s.mem (c.A+72#32) 16)) :=
  (compare_reach_w (Pc := fun _ => True) c hv s hp hs hh (fun _ _ => trivial) (fun _ _ => trivial) trivial).toReach

end M0Crypto.Release.Aead
