import M0Crypto.Thumb.SpBlock
import M0Crypto.Artifacts.Release
import M0Crypto.Proofs.Common
import M0Crypto.Proofs.ChaCha20DRound
import M0Crypto.Release.ChaChaRoundDefs
import M0Crypto.Release.ChaChaLayout
import M0Crypto.Sym.PilotCore
import M0Crypto.Sym.PilotDRound

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release.ChaChaRound

open M0Crypto.Armv6M (Word Reg State read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Proofs (toReg_0 toReg_1 toReg_2 toReg_3)
open M0Crypto.Spec.ChaCha20 (quarterRound)
open M0Crypto.Release.ChaChaLayout (droundOff)

set_option maxRecDepth 100000 in
theorem dround_at : seqAt Artifacts.Release.bytes droundOff dround = true := by decide

/-! ## Register core -/

/-- The quarter round on r0-r3, through the approach-C checker (`Sym.core_regs_sym`). -/
theorem core_regs (s : State) (h : RotRegs s) :
    let s' := execAll core s
    (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
      quarterRound (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) :=
  M0Crypto.Sym.core_regs_sym s h

theorem core_frame (s : State) :
    let s' := execAll core s
    s'.mem = s.mem ∧ ∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r :=
  ⟨execAll_mem core s (by decide), fun r h4 h14 => execAll_regs_other core s r (by omega)
    (by simp [core, Instr.dsts]; omega)⟩

/-! ## Loads and stores -/

/-- Stack word slot `k` as the model computes it for `LDR/STR Rt, [SP, #4k]`. -/
theorem sp_off (sp : Word) (k : Nat) (hk : k < 64) :
    sp + BitVec.ofNat 32 ((BitVec.ofNat 8 k).toNat * 4) = slot sp k := by
  simp only [slot, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

/-- The d-row registers r8-r11 differ from r0-r3, SP and PC. -/
structure DReg (dreg : Reg) : Prop where
  lo : 8 ≤ dreg.val
  hi : dreg.val ≤ 11

theorem pre_regs (s : State) (a b c : Nat) (dreg : Reg) (haveA : Bool)
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : DReg dreg) :
    let s' := execAll (pre a b c dreg haveA) s
    s'.regs 0 = (if haveA then s.regs 0 else read32 s.mem (slot (s.regs 13) a)) ∧
    s'.regs 1 = read32 s.mem (slot (s.regs 13) b) ∧
    s'.regs 2 = read32 s.mem (slot (s.regs 13) c) ∧
    s'.regs 3 = s.regs dreg := by
  obtain ⟨h8, h11⟩ := hd
  have f : ∀ k : Reg, k.val ≤ 7 ∨ 12 ≤ k.val → (dreg = k) = False := by
    intro k hk; apply eq_false; intro e; subst e; omega
  cases haveA <;>
  simp only [pre, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, execAll,
    Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
    M0Crypto.Armv6M.State.pc, toReg_0, toReg_1, toReg_2, toReg_3] <;>
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false,
    sp_off _ _ ha, sp_off _ _ hb, sp_off _ _ hc, and_self, true_and,
    f 0 (by decide), f 1 (by decide), f 2 (by decide), f 15 (by decide)]

theorem post_effect (s : State) (a b c : Nat) (dreg : Reg) (keepA : Bool)
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : DReg dreg) :
    let s' := execAll (post a b c dreg keepA) s
    s'.mem = write32 (write32 (if keepA then s.mem else write32 s.mem (slot (s.regs 13) a) (s.regs 0))
        (slot (s.regs 13) b) (s.regs 1)) (slot (s.regs 13) c) (s.regs 2) ∧
    s'.regs dreg = s.regs 3 := by
  obtain ⟨h8, h11⟩ := hd
  have f : ∀ k : Reg, k.val ≤ 7 ∨ 12 ≤ k.val → (dreg = k) = False := by
    intro k hk; apply eq_false; intro e; subst e; omega
  have f' : ∀ k : Reg, k.val ≤ 7 ∨ 12 ≤ k.val → (k = dreg) = False := by
    intro k hk; apply eq_false; intro e; subst e; omega
  cases keepA <;>
  simp only [post, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, execAll,
    Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
    M0Crypto.Armv6M.State.pc, M0Crypto.Armv6M.State.reg, toReg_0, toReg_1, toReg_2, toReg_3] <;>
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false,
    sp_off _ _ ha, sp_off _ _ hb, sp_off _ _ hc, and_self, true_and,
    f 0 (by decide), f 1 (by decide), f 2 (by decide), f 13 (by decide), f 15 (by decide),
    f' 13 (by decide), f' 15 (by decide)]

theorem pre_dsts (a b c : Nat) (dreg : Reg) (haveA : Bool) :
    ∀ i ∈ pre a b c dreg haveA, ∀ x ∈ i.dsts, x ≤ 3 := by
  cases haveA <;> simp [pre, Instr.dsts] <;> decide

theorem post_dsts (a b c : Nat) (dreg : Reg) (keepA : Bool) :
    ∀ i ∈ post a b c dreg keepA, ∀ x ∈ i.dsts, x = dreg.val := by
  cases keepA <;> simp [post, Instr.dsts]

theorem execAll_regs_of_dsts (is : List Instr) (s : State) (r : Reg) (h15 : r.val ≠ 15)
    (P : Nat → Prop) (hP : ∀ i ∈ is, ∀ x ∈ i.dsts, P x) (hr : ¬ P r.val) :
    (execAll is s).regs r = s.regs r := by
  apply execAll_regs_other is s r h15
  rw [List.all_eq_true]
  intro i hi
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  exact fun hm => hr (hP i hi _ hm)

/-- The effect of one `QR_REG_D` on registers and memory. -/
theorem qr_effect (s : State) (a b c : Nat) (dreg : Reg) (haveA keepA : Bool)
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : DReg dreg) (hrot : RotRegs s) :
    let s' := execAll (qr a b c dreg haveA keepA) s
    let A := if haveA then s.regs 0 else read32 s.mem (slot (s.regs 13) a)
    let q := quarterRound A (read32 s.mem (slot (s.regs 13) b)) (read32 s.mem (slot (s.regs 13) c))
      (s.regs dreg)
    s'.regs 0 = q.1 ∧ s'.regs dreg = q.2.2.2 ∧
    s'.mem = write32 (write32 (if keepA then s.mem else write32 s.mem (slot (s.regs 13) a) q.1)
        (slot (s.regs 13) b) q.2.1) (slot (s.regs 13) c) q.2.2.1 ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → r ≠ dreg → s'.regs r = s.regs r) := by
  intro s' A q
  have hd' := hd
  obtain ⟨h8, h11⟩ := hd'
  -- intermediate states
  have e1 := pre_regs s a b c dreg haveA ha hb hc hd
  let s1 := execAll (pre a b c dreg haveA) s
  let s2 := execAll core s1
  have hs' : s' = execAll (post a b c dreg keepA) s2 := by
    simp only [s', s2, s1, qr, execAll_append]
  have m1 : s1.mem = s.mem := execAll_mem _ s (by cases haveA <;> simp [pre, Instr.writesMem])
  have r1 : ∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → s1.regs r = s.regs r := fun r h4 h15 =>
    execAll_regs_of_dsts _ s r h15 (· ≤ 3) (pre_dsts a b c dreg haveA) (by omega)
  have hrot1 : RotRegs s1 := ⟨by rw [r1 4 (by decide) (by decide)]; exact hrot.r4,
    by rw [r1 5 (by decide) (by decide)]; exact hrot.r5,
    by rw [r1 6 (by decide) (by decide)]; exact hrot.r6,
    by rw [r1 7 (by decide) (by decide)]; exact hrot.r7⟩
  have e2 := core_regs s1 hrot1
  obtain ⟨m2, r2⟩ := core_frame s1
  have sp1 : s1.regs 13 = s.regs 13 := r1 13 (by decide) (by decide)
  have sp2 : s2.regs 13 = s.regs 13 := by rw [r2 13 (by decide) (by decide), sp1]
  have hq : (s2.regs 0, s2.regs 1, s2.regs 2, s2.regs 3) = q := by
    rw [e2]; simp only [q, A]; rw [e1.1, e1.2.1, e1.2.2.1, e1.2.2.2]
  have hq' := hq
  simp only [Prod.ext_iff] at hq'
  obtain ⟨q0, q1, q2, q3⟩ := hq'
  obtain ⟨m3, d3⟩ := post_effect s2 a b c dreg keepA ha hb hc hd
  rw [hs']
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [execAll_regs_of_dsts _ s2 0 (by decide) (· = dreg.val) (post_dsts a b c dreg keepA)
      (by show ¬ (0 = dreg.val); omega)]
    exact q0
  · rw [d3]; exact q3
  · rw [m3, sp2, m2, m1, q0, q1, q2]
  · intro r h4 h14 hne
    have h15 : r.val ≠ 15 := by omega
    rw [execAll_regs_of_dsts _ s2 r h15 (· = dreg.val) (post_dsts a b c dreg keepA)
      (fun e => hne (Fin.ext e)), r2 r h4 h14, r1 r h4 h15]

open M0Crypto.Proofs.ChaCha20DRound (upd qroundF innerBlockF)

theorem dregOf_DReg (d : Nat) (h1 : 12 ≤ d) (h2 : d < 16) : DReg (dregOf d) :=
  ⟨by simp [dregOf]; omega, by simp [dregOf]; omega⟩

theorem dregOf_inj (j k : Nat) (hj : 12 ≤ j) (hj' : j < 16) (hk : 12 ≤ k) (hk' : k < 16)
    (h : dregOf j = dregOf k) : j = k := by
  have := congrArg Fin.val h; simp [dregOf] at this; omega

theorem rd_slot (m : M0Crypto.Armv6M.Mem) (sp v : Word) (i j : Nat) (hi : i < 16) (hj : j < 16) (h : i ≠ j) :
    read32 (write32 m (slot sp i) v) (slot sp j) = read32 m (slot sp j) := by
  rw [M0Crypto.Armv6M.read32_write32_slot m sp v i j hi hj]; simp [h]

theorem rd_slot_same (m : M0Crypto.Armv6M.Mem) (sp v : Word) (i : Nat) :
    read32 (write32 m (slot sp i) v) (slot sp i) = v := M0Crypto.Armv6M.read32_write32_same _ _ _

/-- One `QR_REG_D` is `QUARTERROUND(a, b, c, d)` on the view. -/
theorem qr_view (s : State) (a b c d : Nat) (haveA keepA : Bool)
    (ha : a < 12) (hb : b < 12) (hc : c < 12) (hd1 : 12 ≤ d) (hd2 : d < 16)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hrot : RotRegs s) :
    view (if keepA then some a else none) (execAll (qr a b c (dregOf d) haveA keepA) s) =
      qroundF (view (if haveA then some a else none) s) a b c d := by
  obtain ⟨e0, ed, em, eo⟩ := qr_effect s a b c (dregOf d) haveA keepA (by omega) (by omega) (by omega)
    (dregOf_DReg d hd1 hd2) hrot
  generalize execAll (qr a b c (dregOf d) haveA keepA) s = s' at e0 ed em eo ⊢
  have sp' : s'.regs 13 = s.regs 13 :=
    eo 13 (by decide) (by decide) (fun h => by have := congrArg Fin.val h; simp [dregOf] at this; omega)
  -- the four inputs as the view sees them
  have va : view (if haveA then some a else none) s a =
      (if haveA then s.regs 0 else read32 s.mem (slot (s.regs 13) a)) := by
    cases haveA <;> simp [view, ha]
  have vb : view (if haveA then some a else none) s b = read32 s.mem (slot (s.regs 13) b) := by
    cases haveA <;> simp [view, hb, hab, Ne.symm hab]
  have vc : view (if haveA then some a else none) s c = read32 s.mem (slot (s.regs 13) c) := by
    cases haveA <;> simp [view, hc, hac, Ne.symm hac]
  have vd : view (if haveA then some a else none) s d = s.regs (dregOf d) := by
    simp [view, show ¬ d < 12 by omega, hd2]
  funext k
  simp only [qroundF, upd, va, vb, vc, vd]
  generalize hq : quarterRound _ _ _ _ = q at e0 ed em
  -- case analysis on k
  by_cases hkd : d = k
  · subst hkd; simp [view, show ¬ d < 12 by omega, hd2, ed]
  by_cases hkc : c = k
  · subst hkc
    simp only [hkd, ite_false, ite_true]
    simp only [view, hc, ite_true, sp', em]
    cases keepA <;> simp [hac, Ne.symm hac, rd_slot_same]
  by_cases hkb : b = k
  · subst hkb
    simp only [hkd, hkc, ite_false, ite_true]
    simp only [view, hb, ite_true, sp', em]
    cases keepA <;> simp [hab, Ne.symm hab, rd_slot _ _ _ c b (by omega) (by omega) hbc.symm, rd_slot_same]
  by_cases hka : a = k
  · subst hka
    simp only [hkd, hkc, hkb, ite_false, ite_true]
    cases keepA
    · simp only [view, ha, ite_true, sp', em, Bool.false_eq_true, ite_false, reduceCtorEq]
      rw [rd_slot _ _ _ c a (by omega) (by omega) (Ne.symm hac),
        rd_slot _ _ _ b a (by omega) (by omega) (Ne.symm hab), rd_slot_same]
    · simp [view, ha, e0]
  · simp only [hkd, hkc, hkb, hka, ite_false]
    by_cases hk12 : k < 12
    · have nA : ∀ o : Bool, ((if o then some a else none) = some k) = False := by
        intro o; cases o <;> simp [hka]
      simp only [view, hk12, ite_true, nA, ite_false, sp', em]
      cases keepA <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        rw [rd_slot _ _ _ c k (by omega) (by omega) hkc, rd_slot _ _ _ b k (by omega) (by omega) hkb]
      rw [rd_slot _ _ _ a k (by omega) (by omega) hka]
    · by_cases hk16 : k < 16
      · simp only [view, hk12, hk16, ite_false, ite_true]
        apply eo
        · simp [dregOf]; omega
        · simp [dregOf]; omega
        · intro h; exact hkd (dregOf_inj _ _ hd1 hd2 (by omega) hk16 h.symm)
      · simp [view, hk12, hk16]

/-- **Double round.** `DOUBLE_ROUND_REG_D` at loop entry (x[2] in r0) is RFC 8439
`inner_block` on the view, and leaves x[2] in r0 again. Proved through the approach-C
checker (`Sym.dround_view_sym`). -/
theorem dround_view (s : State) (hrot : RotRegs s) :
    view (some 2) (execAll dround s) = innerBlockF (view (some 2) s) :=
  M0Crypto.Sym.dround_view_sym s hrot

/-! ## Frame, alignment and trace of the double round -/

theorem dround_spB : spBlockB dround (fun p => p.2 % 4 == 0 && p.2 + 4 ≤ droundBytes) = true := by decide

theorem dround_sp : SpBlock dround (fun p => p.2 % 4 = 0 ∧ p.2 + 4 ≤ droundBytes) :=
  (spBlock_of_B dround_spB).mono fun p h => by simpa using h

/-- Every access of the double round is aligned when SP is. -/
theorem dround_aligned (s : State) (hsp : (s.regs 13).toNat % 4 = 0) : alignedAll dround s = true :=
  alignedAll_sp dround s (dround_sp.mono fun _ h => h.1) hsp

/-- The double round writes memory only in the `droundBytes` above SP (stack slots 0..11). -/
theorem dround_mem (s : State) (y : Word) (hy : ∀ o < droundBytes, y ≠ s.regs 13 + BitVec.ofNat 32 o) :
    (execAll dround s).mem y = s.mem y :=
  execAll_mem_sp_window dround s droundBytes (dround_sp.mono fun _ h => .inr h.2) y hy

/-- The double round writes only r0-r3 and r8-r11. -/
theorem dround_regs (s : State) (r : Reg) (h15 : r.val ≠ 15) (h : 3 < r.val ∧ (r.val < 8 ∨ 11 < r.val)) :
    (execAll dround s).regs r = s.regs r :=
  execAll_regs_of_dsts dround s r h15 (fun x => x ≤ 3 ∨ (8 ≤ x ∧ x ≤ 11))
    (by
      have h : (dround.all fun i => i.dsts.all fun x => decide (x ≤ 3 ∨ (8 ≤ x ∧ x ≤ 11))) = true := by
        decide
      intro i hi x hx
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h i hi x hx) (by omega)

/-- Constant time: the double round's trace depends only on PC and SP. -/
theorem dround_trace_congr (s t : State) (hpc : s.pc = t.pc) (hsp : s.regs 13 = t.regs 13) :
    traceAll dround s = traceAll dround t :=
  traceAll_sp_congr dround s t (dround_sp.mono fun _ _ => trivial) dround_falls hpc hsp

end M0Crypto.Release.ChaChaRound
