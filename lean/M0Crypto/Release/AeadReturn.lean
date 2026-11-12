import M0Crypto.Release.AeadClear
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7

theorem popSize_eq : seqSize [.pop 0xf0 true] = 2 := by decide

theorem pop_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (Wr : Word → Prop) (off : Nat)
    (hat : instrAt B off = some (.pop 0xf0 true)) (ho : off % 2 = 0)
    (hx : off + seqSize [.pop 0xf0 true] ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 off) (hs : s.regs 13 = (c.sp0 - 20#32))
    (hsv : ∀ j < 5, read32 s.mem (slot (c.sp0 - 20#32) j) =
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14].getD j 0#32)
    (hlr : (c.regs0 14).getLsbD 0 = true) (hrp : Pc (c.base + BitVec.ofNat 32 off)) :
    ReachW c.base Pc Wr s fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 8 → t.regs r = c.regs0 r) ∧
      (∀ r : Reg, (r.val < 4 ∨ 8 ≤ r.val) → r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) ∧ t.mem = s.mem := by
  have sv0 := hsv 0 (by decide); have sv1 := hsv 1 (by decide)
  have sv2 := hsv 2 (by decide); have sv3 := hsv 3 (by decide); have sv4 := hsv 4 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ, slot, Nat.reduceMul, BitVec.add_zero] at sv0 sv1 sv2 sv3 sv4
  have hfp4 : (c.sp0 - 20#32).toNat % 4 = 0 := by have := hv.sp8; have := hv.spLo; simp [BitVec.toNat_sub]; omega
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hsp1 : s.regs 13 + BitVec.ofNat 32 (4 * bitCount 0xf0) = (c.sp0 - 20#32) + 16#32 := by
    rw [hs, Frame.bitCount_f0]
  obtain ⟨t, hex⟩ : ∃ t, (Instr.pop 0xf0 true).exec s = .ok t := by
    simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, sv4, hlr, ite_true]
    exact ⟨_, rfl⟩
  have hex' := hex
  simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, sv4, hlr, ite_true, Except.ok.injEq] at hex'
  subst hex'
  apply ReachW.stepR hrp hb2 _ hp ho hat
    (by rw [B_len]; have := popSize_eq; show off + 2 ≤ _; omega)
    (by
      have := hv.sp8; have := hv.spLo
      have bc240 : bitCount 240#8 = 4 := by decide
      simp [Instr.accesses, wordAccesses, List.range_succ, Access.aligned, Frame.bitCount_f0, bc240,
          M0Crypto.Armv6M.State.sp, hs, BitVec.toNat_add, BitVec.toNat_sub]; constructor <;> omega)
    hex (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses, wordAccesses] at ha
            obtain ⟨_, _, rfl⟩ := ha; cases hw)
  apply ReachS.done
  generalize hF : (((loadRegs (s.setReg 15 (s.pc + BitVec.ofNat 32 (Instr.pop 240 true).size)) (s.regs 13)
      (List.map M0Crypto.Armv6M.LowReg.toReg (listRegs 240))).setReg 13
      (s.regs 13 + BitVec.ofNat 32 (4 * (bitCount 240 + true.toNat)))).setReg
      15 (c.regs0 14 &&& ~~~1#32)) = F
  have q : ∀ r : Reg, F.regs r = (if r = 15 then c.regs0 14 &&& ~~~1#32 else if r = 13 then (c.sp0 - 20#32) + 20#32
      else if r = 4 then c.regs0 4 else if r = 5 then c.regs0 5 else if r = 6 then c.regs0 6
      else if r = 7 then c.regs0 7 else s.regs r) := by
    intro r; rw [← hF]
    simp (config := { decide := true }) only [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240,
      List.map, loadRegs, M0Crypto.Armv6M.LowReg.toReg, hs, Frame.bitCount_f0, BitVec.add_assoc,
      BitVec.reduceAdd, sv0, sv1, sv2, sv3, Bool.toNat_true, Nat.reduceAdd, Nat.reduceMul,
      M0Crypto.Armv6M.State.pc]
    by_cases h15 : r = 15
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg]
    by_cases h13 : r = 13
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg]
    by_cases h4 : r = 4
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv0, BitVec.add_assoc]
    by_cases h5 : r = 5
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv1, BitVec.add_assoc]
    by_cases h6 : r = 6
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv2, BitVec.add_assoc]
    by_cases h7 : r = 7
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv3, BitVec.add_assoc]
    simp only [h4, h5, h6, h7, h13, h15, ite_false]
    rw [loadRegs_regs_other _ _ _ _ (by
      simp only [Frame.listRegs_240, Frame.listRegs_f0, List.map, List.mem_cons, List.not_mem_nil, or_false]
      rcases r with ⟨v, hv⟩; simp only [Fin.ext_iff] at h4 h5 h6 h7; simp at h4 h5 h6 h7 ⊢; omega)]
    simp [h15]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact q 15
  · rw [q]; simp (config := { decide := true }) [BitVec.sub_add_cancel]
  · intro r hlo hhi
    rcases (by omega : r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7) with hr | hr | hr | hr <;>
      have er : r = ⟨r.val, r.isLt⟩ := rfl <;> rw [q] <;>
      simp (config := { decide := true }) [Fin.ext_iff, hr]
    all_goals congr 1 <;> apply Fin.ext <;> omega
  · intro r hr h13 h15
    rw [q]
    simp only [show r ≠ 15 from fun h => h15 (congrArg Fin.val h),
      show r ≠ 13 from fun h => h13 (congrArg Fin.val h), ite_false]
    have h4 : r ≠ 4 := by intro h; have := congrArg Fin.val h; omega
    have h5 : r ≠ 5 := by intro h; have := congrArg Fin.val h; omega
    have h6 : r ≠ 6 := by intro h; have := congrArg Fin.val h; omega
    have h7 : r ≠ 7 := by intro h; have := congrArg Fin.val h; omega
    simp [h4, h5, h6, h7]
  · rw [← hF]; simp [M0Crypto.Armv6M.State.setReg, loadRegs_mem]

def epilogue (dec : Bool) : List Instr := if dec then epiD else epiE

theorem epilogue_size (dec : Bool) : seqSize (epilogue dec) = 10 := by cases dec <;> decide

theorem epi_effect (dec : Bool) (s : State) :
    (execAll (epilogue dec) s).mem = s.mem ∧
    (execAll (epilogue dec) s).regs 13 = s.regs 13 + 124#32 ∧
    (execAll (epilogue dec) s).regs 0 = (if dec then s.regs 4 else 0#32) ∧
    (∀ r : Reg, 1 ≤ r.val → r.val < 4 → (execAll (epilogue dec) s).regs r = 0#32) ∧
    (∀ r : Reg, 4 ≤ r.val → r.val < 12 → (execAll (epilogue dec) s).regs r = s.regs r) := by
  have rr : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → (execAll (epilogue dec) s).regs r = s.regs r := by
    intro r a b
    apply execAll_regs_other _ _ _ (by omega)
    have h0 : r.val ≠ 0 := by omega
    have h1 : r.val ≠ 1 := by omega
    have h2 : r.val ≠ 2 := by omega
    have h3 : r.val ≠ 3 := by omega
    have h13 : r.val ≠ 13 := by omega
    cases dec <;> simp [epilogue, epiE, epiD, Instr.dsts, Fin.ext_iff, h0, h1, h2, h3, h13] <;> omega
  refine ⟨?_, ?_, ?_, ?_, rr⟩
  all_goals cases dec <;> simp [epilogue, epiE, epiD, execAll, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lslC]
  all_goals intro r a b
  all_goals rcases r with ⟨v, hv⟩
  all_goals simp only [Fin.val_mk] at a b
  all_goals have hr : v = 1 ∨ v = 2 ∨ v = 3 := by omega
  all_goals rcases hr with rfl | rfl | rfl <;> rfl

theorem epilogue_reach_w {Pc : Word → Prop} (c : ACall) (hv : AValid c) (Wr : Word → Prop) (dec : Bool) (off : Nat)
    (hseq : seqAt B off (epilogue dec) = true)
    (hpop : instrAt B (off + seqSize (epilogue dec)) = some (.pop 0xf0 true))
    (ho : off % 2 = 0)
    (hx : off + seqSize (epilogue dec) + seqSize [.pop 0xf0 true] ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 off) (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (hr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → s.regs r = c.regs0 r)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hrE : InRegion Pc c.base off (seqSize (epilogue dec)))
    (hrp : Pc (c.base + BitVec.ofNat 32 (off + seqSize (epilogue dec)))) :
    ReachW c.base Pc Wr s (fun t => RetPost c (if dec then s.regs 4 else 0#32) t ∧ t.mem = s.mem) := by
  have hf : (epilogue dec).all Instr.falls = true := by cases dec <;> decide
  have he := epilogue_size dec
  obtain ⟨em, es, e0, ec, er⟩ := epi_effect dec s
  apply ReachW.blockR hrE (by have := hv.base4; omega) hp ho hseq hf
    (by cases dec <;> simp [epilogue, epiE, epiD, alignedAll, Instr.accesses])
    (WritesTo.of_noWritesMem _ _ (by cases dec <;> decide) _)
  generalize hu : execAll (epilogue dec) s = u at em es e0 ec er
  have up : u.pc = c.base + BitVec.ofNat 32 (off + seqSize (epilogue dec)) := by
    rw [← hu, execAll_pc _ _ hf, hp, ofNat_add_assoc]
  have us : u.regs 13 = c.sp0 - 20#32 := by rw [es, hs, ACall.A]; bv_omega
  have saved : ∀ j < 5, read32 u.mem (slot (c.sp0-20#32) j) =
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14].getD j 0#32 := by
    intro j hj
    have hb : c.sp0 - 20#32 = c.A + 124#32 := by rw [ACall.A]; bv_omega
    rw [em, hb, slot, ofNat_add_assoc]
    have h := hh.saved j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> exact h
  apply (pop_reach_w c hv Wr (off + seqSize (epilogue dec)) hpop (by omega) hx u up us saved hlr hrp).mono (fun _ _ h => h)
  rintro t ⟨tp, ts, tc, tr, tm⟩
  refine ⟨⟨tp, ts, ?_, ?_, ?_⟩, tm.trans em⟩
  · intro r a b
    by_cases hr8 : r.val < 8
    · exact tc r a hr8
    · rw [tr r (.inr (by omega)) (by omega) (by omega), er r a b, hr r (by omega) b]
  · rw [tr 0 (.inl (by decide)) (by decide) (by decide), e0]
  · intro r a b
    rw [tr r (.inl b) (by omega) (by omega), ec r a b]

theorem epilogue_reach (c : ACall) (hv : AValid c) (Wr : Word → Prop) (dec : Bool) (off : Nat)
    (hseq : seqAt B off (epilogue dec) = true)
    (hpop : instrAt B (off + seqSize (epilogue dec)) = some (.pop 0xf0 true))
    (ho : off % 2 = 0)
    (hx : off + seqSize (epilogue dec) + seqSize [.pop 0xf0 true] ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 off) (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (hr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → s.regs r = c.regs0 r)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base Wr s (fun t => RetPost c (if dec then s.regs 4 else 0#32) t ∧ t.mem = s.mem) :=
  (epilogue_reach_w (Pc := fun _ => True) c hv Wr dec off hseq hpop ho hx s hp hs hh hr hlr
    (fun _ _ => trivial) trivial).toReach

end M0Crypto.Release.Aead
