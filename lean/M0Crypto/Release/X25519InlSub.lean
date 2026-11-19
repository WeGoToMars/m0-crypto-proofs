import M0Crypto.Release.X25519InlAdd

set_option linter.unusedSimpArgs false

/-!
`fe_sub_body` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = a - b`
modulo `p`, `r0 = dst`, `r1 = a`, `r2 = b`.

* `sumOp true`: the 256-bit difference `d + b = a + 2^256 br`, the borrow `br = 1 - C`.
* `subQ`: `r7 = 19 * k`, `k = (1 - bit 255 of d) + 2 br`; bit 255 of `d` set.
* `outOp true`: subtract `r7` from the low word, propagate, store the eight words to `dst`.

As for the add, every load comes before the first store: no aliasing hypothesis.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region ReachW InRegion)
open M0Crypto.Release.Field25519Block (AccAll AccOk accAll_append)
open M0Crypto.Release.Field25519Mem (toReg0 toReg1 toReg6 toReg7)
open M0Crypto.Release.Field25519Carry (adc_nat)
open M0Crypto.Release.Field25519Congr
open M0Crypto.Release.Field25519AddSubChain
open M0Crypto.Release.Field25519AddSub

theorem feSubBody_at : SiteOk feSubBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel


theorem subQ_acc {Wr : Word → Prop} (s : State) : AccAll (AccOk Wr) subQ s :=
  X25519MulcWord.accAll_regOnly _ _ (by decide)

theorem feSub_acc {Wr : Word → Prop} (s : State) (h0 : (s.regs 0).toNat % 4 = 0)
    (h1 : (s.regs 1).toNat % 4 = 0) (h2 : (s.regs 2).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) feSubBody s := by
  simp only [feSubBody]
  obtain ⟨-, -, so⟩ := sumOp_exec s true
  refine accAll_append (accAll_append (sumOp_acc s true h1 h2) (subQ_acc _)) ?_
  obtain ⟨-, -, -, qo⟩ := subQ_exec (execAll (sumOp true) s)
  have e0 : (execAll subQ (execAll (sumOp true) s)).regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  rw [execAll_append]
  exact outOp_acc _ true (by rw [e0]; exact h0) (by rw [e0]; exact hW)

/-- One `fe_sub_body` block in a `ReachW` proof: `dst = a - b` modulo `p`. `a`, `b`, `dst`
may alias in any way. -/
theorem feSub_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {dst a b : Word}
    (hseq : seqAt B off feSubBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize feSubBody))
    (h0 : t.regs 0 = dst) (h1 : t.regs 1 = a) (h2 : t.regs 2 = b)
    (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0) (hbb : b.toNat % 4 = 0)
    (hf : dst.toNat + 32 ≤ 2 ^ 32)
    (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize feSubBody) →
      (Field25519Routines.feVal t'.mem dst : Int) ≡p
          Field25519Routines.feVal t.mem a - Field25519Routines.feVal t.mem b →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst h0 h1 h2
  obtain ⟨ev, em, eo⟩ := feSub_exec t hf
  refine Field25519Block.ReachW.blockAcc hb _ off hpc hoff hseq feSubBody_falls
    (feSub_acc t hd ha hbb hW) hr (k _ ?_ ev em eo)
  rw [execAll_pc _ _ feSubBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
