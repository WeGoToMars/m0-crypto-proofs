import M0Crypto.Release.X25519InlBase

set_option linter.unusedSimpArgs false

/-!
The accesses of the carry chains shared by `fe_add_body` and `fe_sub_body`: every load and
store of `sumOp` and `outOp` (`Field25519AddSubChain`) is aligned and inside the given bounds.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Frame (FrameOk upd)
open M0Crypto.Release.Field25519Facts (psum)
open M0Crypto.Release.Field25519Block (AccAll AccOk accAll_cons accAll_nil accAll_append)
open M0Crypto.Release.Field25519Mem (toReg0 toReg1 toReg2 toReg3 toReg4 toReg5 toReg6 toReg7)
open M0Crypto.Release.Field25519Carry (adc_nat carry_le)

open M0Crypto.Release.Field25519AddSubChain

/-! ## Accesses -/

theorem pairOp_acc {Wr : Word → Prop} (s : State) (neg k : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (pairOp neg k) s :=
  accAll_append (ld34_acc s h1 h2)
    (X25519MulcWord.accAll_regOnly _ _ (by cases k <;> simp [regOnly_dop, regOnly_op3]))

theorem topOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (topOp neg) s := by
  refine accAll_cons (ldm_acc s 1 _ h1) (accAll_cons (ldm_acc _ 2 _ ?_)
    (X25519MulcWord.accAll_regOnly _ _ (by simp [regOnly_dop])))
  have : ((Instr.ldm 1 0x60).next s).regs 2 = s.regs 2 := by
    simp (config := {decide := true}) only [Field25519Mem.regs_ldm, listRegs_60, List.map,
      toReg5, toReg6, toReg1, List.mem_cons, List.not_mem_nil, ite_false, or_self]
  show (((Instr.ldm 1 0x60).next s).regs (LowReg.toReg 2)).toNat % 4 = 0
  rw [toReg2, this]; exact h2

theorem mv2_acc {Wr : Word → Prop} (s : State) (a b x y : Reg) :
    AccAll (AccOk Wr) [.movHi a x, .movHi b y] s :=
  X25519MulcWord.accAll_regOnly _ _ rfl

theorem sumOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (sumOp neg) s := by
  rw [sumOp_split]
  obtain ⟨-, p1, q1, -, -⟩ := pairOp_exec s neg false
  refine accAll_append (pairOp_acc s neg false h1 h2) ?_
  generalize execAll (pairOp neg false) s = s1 at p1 q1
  obtain ⟨-, -, -, -, uo⟩ := mv2_exec s1 8 10 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine accAll_append (mv2_acc s1 _ _ _ _) ?_
  generalize execAll [.movHi 8 3, .movHi 10 4] s1 = s2 at uo
  have e1 : s2.regs 1 = slot (s.regs 1) 2 := by rw [uo 1 (by decide) (by decide) (by decide), p1]
  have e2 : s2.regs 2 = slot (s.regs 2) 2 := by rw [uo 2 (by decide) (by decide) (by decide), q1]
  obtain ⟨-, p2, q2, -, -⟩ := pairOp_exec s2 neg true
  refine accAll_append (pairOp_acc s2 neg true (by rw [e1]; exact slot_al h1 2)
    (by rw [e2]; exact slot_al h2 2)) ?_
  generalize execAll (pairOp neg true) s2 = s3 at p2 q2
  obtain ⟨-, -, -, -, wo⟩ := mv2_exec s3 11 12 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine accAll_append (mv2_acc s3 _ _ _ _) ?_
  generalize execAll [.movHi 11 3, .movHi 12 4] s3 = s4 at wo
  have f1 : s4.regs 1 = slot (s.regs 1) 4 := by
    rw [wo 1 (by decide) (by decide) (by decide), p2, e1, slot_slot]
  have f2 : s4.regs 2 = slot (s.regs 2) 4 := by
    rw [wo 2 (by decide) (by decide) (by decide), q2, e2, slot_slot]
  obtain ⟨-, p3, q3, -, -⟩ := pairOp_exec s4 neg true
  refine accAll_append (pairOp_acc s4 neg true (by rw [f1]; exact slot_al h1 4)
    (by rw [f2]; exact slot_al h2 4)) ?_
  refine topOp_acc _ neg (by rw [p3, f1, slot_slot]; exact slot_al h1 6)
    (by rw [q3, f2, slot_slot]; exact slot_al h2 6)

theorem regs0_keep (s : State) (is : List Instr) (h : is.all (fun i => !(i.dsts.contains 0)) = true) :
    (execAll is s).regs 0 = s.regs 0 :=
  execAll_regs_other is s 0 (by decide) h

theorem loOp_split (neg : Bool) : loOp neg =
    [.movHi 1 8, .movHi 2 10, op3 neg 1 1 7, .movImm 7 0, .dp (dop neg) 2 7] ++ [.stm 0 0x06] := rfl

theorem hiOp_split (neg : Bool) : hiOp neg =
    [.movHi 1 11, .movHi 2 12, .dp (dop neg) 1 7, .dp (dop neg) 2 7, .dp (dop neg) 3 7,
      .dp (dop neg) 4 7, .dp (dop neg) 5 7, .dp (dop neg) 6 7] ++ [.stm 0 0x7e] := rfl

theorem outOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h0 : (s.regs 0).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) (outOp neg) s := by
  obtain ⟨-, -, l0, -, -⟩ := loOp_exec s neg
  refine accAll_append ?_ ?_
  · rw [loOp_split]
    refine accAll_append (X25519MulcWord.accAll_regOnly _ _ (by cases neg <;> decide))
      (accAll_cons (stm_acc _ 0 _ ?_ ?_) (accAll_nil _ _))
    all_goals
      have e : (execAll [.movHi 1 8, .movHi 2 10, op3 neg 1 1 7, .movImm 7 0, .dp (dop neg) 2 7]
          s).reg 0 = s.regs 0 := regs0_keep _ _ (by cases neg <;> decide)
      rw [e]
    · exact h0
    · intro i hi q hq
      have := wr_words hW (k := 0) (n := 2) (by omega) i (by rw [bitCount_06] at hi; exact hi) q hq
      rwa [slot_zero] at this
  · rw [hiOp_split]
    generalize execAll (loOp neg) s = s1 at l0
    refine accAll_append (X25519MulcWord.accAll_regOnly _ _ (by cases neg <;> decide))
      (accAll_cons (stm_acc _ 0 _ ?_ ?_) (accAll_nil _ _))
    all_goals
      have e : (execAll [.movHi 1 11, .movHi 2 12, .dp (dop neg) 1 7, .dp (dop neg) 2 7,
          .dp (dop neg) 3 7, .dp (dop neg) 4 7, .dp (dop neg) 5 7, .dp (dop neg) 6 7] s1).reg 0 =
          s1.regs 0 := regs0_keep _ _ (by cases neg <;> decide)
      rw [e, l0]
    · exact slot_al h0 2
    · intro i hi q hq
      exact wr_words hW (k := 2) (n := 6) (by omega) i (by rw [bitCount_7e] at hi; exact hi) q hq

end M0Crypto.Release.X25519Inl
