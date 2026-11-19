import M0Crypto.Release.X25519InlChain
import M0Crypto.Release.Field25519AddSub
import M0Crypto.Release.Field25519Reduce

set_option linter.unusedSimpArgs false

/-!
`fe_add_body` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = a + b`
modulo `p`, `r0 = dst`, `r1 = a`, `r2 = b`.

* `sumOp false`: the 256-bit sum `s + 2^256 c = a + b` (`X25519InlChain`).
* `addQ`: `r7 = 19 * (2 c + bit 255 of s)`, bit 255 of `s` cleared.
* `outOp false`: add `r7` to the low word, propagate, store the eight words to `dst`.

Every load comes before the first store, so `a`, `b` and `dst` may overlap in any way; the
run lemma has no aliasing hypothesis.
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

theorem feAddBody_at : SiteOk feAddBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel


theorem addQ_acc {Wr : Word → Prop} (s : State) : AccAll (AccOk Wr) addQ s :=
  X25519MulcWord.accAll_regOnly _ _ (by decide)

theorem feAdd_acc {Wr : Word → Prop} (s : State) (h0 : (s.regs 0).toNat % 4 = 0)
    (h1 : (s.regs 1).toNat % 4 = 0) (h2 : (s.regs 2).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) feAddBody s := by
  simp only [feAddBody]
  obtain ⟨-, -, so⟩ := sumOp_exec s false
  refine accAll_append (accAll_append (sumOp_acc s false h1 h2) (addQ_acc _)) ?_
  obtain ⟨-, -, -, qo⟩ := addQ_exec (execAll (sumOp false) s)
  have e0 : (execAll addQ (execAll (sumOp false) s)).regs 0 = s.regs 0 := by
    rw [qo 0 (by decide) (by decide), so 0 (by decide) (by decide)]
  rw [execAll_append]
  exact outOp_acc _ false (by rw [e0]; exact h0) (by rw [e0]; exact hW)

/-- One `fe_add_body` block in a `ReachW` proof: `dst = a + b` modulo `p`. `a`, `b`, `dst`
may alias in any way. -/
theorem feAdd_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {dst a b : Word}
    (hseq : seqAt B off feAddBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize feAddBody))
    (h0 : t.regs 0 = dst) (h1 : t.regs 1 = a) (h2 : t.regs 2 = b)
    (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0) (hbb : b.toNat % 4 = 0)
    (hf : dst.toNat + 32 ≤ 2 ^ 32)
    (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize feAddBody) →
      (Field25519Routines.feVal t'.mem dst : Int) ≡p
          Field25519Routines.feVal t.mem a + Field25519Routines.feVal t.mem b →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12] : List Reg) →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst h0 h1 h2
  obtain ⟨ev, em, eo⟩ := feAdd_exec t hf
  refine Field25519Block.ReachW.blockAcc hb _ off hpc hoff hseq feAddBody_falls (feAdd_acc t hd ha hbb hW) hr
    (k _ ?_ ev em eo)
  rw [execAll_pc _ _ feAddBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
