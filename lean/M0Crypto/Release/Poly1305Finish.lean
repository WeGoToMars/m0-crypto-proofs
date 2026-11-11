import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305FinishStore
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace M0Crypto.Release.Poly1305Finish
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (p leBytes)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

structure FCtx where
  base : Word
  sp0 : Word
  ctx : Word
  tag : Word
  m0 : Mem
  regs0 : Reg → Word
namespace FCtx
def fp (c : FCtx) : Word := c.sp0 - 20#32
def mP (c : FCtx) : Mem := storeWords c.m0 c.fp [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14]
def w (c : FCtx) (j : Nat) : Word := read32 c.m0 (slot c.ctx j)
def acc (c : FCtx) : Nat := Poly1305Arith.val5 (c.w 0).toNat (c.w 1).toNat (c.w 2).toNat (c.w 3).toNat (c.w 4).toNat
def padVal (c : FCtx) : Nat := Poly1305Arith.val4 (c.w 12).toNat (c.w 13).toNat (c.w 14).toNat (c.w 15).toNat
def Wr (c : FCtx) (y : Word) : Prop := InFrame c.fp 5 y ∨ InFrame c.tag 4 y
end FCtx
structure FValid (c : FCtx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 20 ≤ c.sp0.toNat
  ctx4 : c.ctx.toNat % 4 = 0
  codeS : Disj c.base Artifacts.Release.size c.fp 20
  codeT : Disj c.base Artifacts.Release.size c.tag 16
  ctxS : Disj c.ctx 64 c.fp 20
  tagS : Disj c.tag 16 c.fp 20
  code : CodeAt c.m0 c.base B
structure FEntry (c : FCtx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 entryAt
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.ctx
  r1 : c.regs0 1 = c.tag

theorem fp4 (c : FCtx) (hv : FValid c) : c.fp.toNat % 4 = 0 := by
  have := hv.spLo; have := hv.sp8
  simp [FCtx.fp, BitVec.toNat_sub]; omega

theorem header_effect (c : FCtx) (s : State) (he : FEntry c s) :
    (execAll header s).mem = c.mP ∧ (execAll header s).regs 7 = c.ctx ∧
    (execAll header s).regs 12 = c.tag ∧ (execAll header s).regs 13 = c.fp ∧
    (execAll header s).regs 6 = 0#32 ∧
    (∀ r : Reg, 8 ≤ r.val → r.val < 12 → (execAll header s).regs r = c.regs0 r) := by
  have hr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → (execAll header s).regs r = c.regs0 r := by
    intro r hlo hhi
    rw [execAll_regs_other _ _ _ (by omega) (by simp [header, Instr.dsts, Frame.listRegs_f0]; omega), he.regs]
  refine ⟨?_, ?_, ?_, ?_, ?_, hr⟩
  all_goals
    simp (config := { decide := true }) [header, execAll, Instr.next, Instr.exec, bitCount,
      Frame.listRegs_f0, Frame.listRegs_240, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp,
      M0Crypto.Armv6M.State.setReg, lslC, he.regs, he.mem, he.sp, he.r0, he.r1,
      FCtx.mP, FCtx.fp]

theorem mP_other (c : FCtx) (y : Word) (hy : ¬ InFrame c.fp 5 y) : c.mP y = c.m0 y := by
  apply storeWords_other
  intro i k hi hk heq
  apply hy
  refine ⟨4*i+k, by simp at hi; omega, ?_⟩
  rw [heq, ofNat_add_assoc]

theorem header_words (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s) (j : Nat) (hj : j < 16) :
    hw (execAll header s) j = c.w j := by
  rw [hw, (header_effect c s he).1, (header_effect c s he).2.1]
  apply read32_congr
  intro k hk
  apply mP_other
  rintro ⟨o, ho, heq⟩
  apply ne_of_disj hv.ctxS.1 hv.ctxS.2.1 hv.ctxS.2.2 (i := 4*j+k) (j := o) (by omega) ho
  rw [slot, ofNat_add_assoc] at heq
  exact heq

/-- Values that the tag-output stores see, before registers are shifted. -/
def tagState (s : State) : State := execAll arithmetic (execAll header s)

theorem tagState_value (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s) (hh : c.acc < 2*p) :
    low (tagState s) = (c.acc % p + c.padVal) % 2^128 := by
  have hc : Poly1305Finish.hv (execAll header s) < 2*p := by
    simpa only [Poly1305Finish.hv, FCtx.acc, header_words c hv s he 0 (by decide),
      header_words c hv s he 1 (by decide), header_words c hv s he 2 (by decide),
      header_words c hv s he 3 (by decide), header_words c hv s he 4 (by decide)] using hh
  rw [tagState, arithmetic_correct _ (header_effect c s he).2.2.2.2.1 hc]
  simp only [Poly1305Finish.hv, pv, FCtx.acc, FCtx.padVal,
    header_words c hv s he 0 (by decide), header_words c hv s he 1 (by decide),
    header_words c hv s he 2 (by decide), header_words c hv s he 3 (by decide),
    header_words c hv s he 4 (by decide), header_words c hv s he 12 (by decide),
    header_words c hv s he 13 (by decide), header_words c hv s he 14 (by decide),
    header_words c hv s he 15 (by decide)]
end M0Crypto.Release.Poly1305Finish
