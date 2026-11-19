import M0Crypto.Release.X25519InlBase
import M0Crypto.Release.Field25519Select

set_option linter.unusedSimpArgs false

/-!
`select_words` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = r7 = 0 ? a :
b` over eight words, `r0 = dst`, `r1 = a`, `r2 = b`, the mask `r7` either `0` or all ones.

The body is four copies of `selPair`: load two words of `a` and of `b`, select with
`a ^ ((b ^ a) & m)` (`Field25519Word.select_word`), store the two words to `dst`. One generic
lemma (`selPair_step`) carries the invariant over pair `k`: words below `2k` of `dst` are
selected, the others still hold their initial value. An input that is `dst` itself is read at
words `≥ 2k` only, before they are overwritten, so `a` and `b` may each be `dst` or disjoint
from it.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519AddSubChain
open M0Crypto.Release (B Region ReachW InRegion)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Frame (FrameOk upd)
open M0Crypto.Release.Field25519Facts (psum psum_congr)
open M0Crypto.Release.Field25519Block (AccAll AccOk accAll_cons accAll_nil accAll_append)
open M0Crypto.Release.Field25519Mem (toReg0 toReg1 toReg2 toReg3 toReg4 toReg5 toReg6 toReg7)

export M0Crypto.Release.Field25519Select
  (selPair selBody selBody_falls sel selVs selPair_exec selG SelInv slot_two selPair_step selBody_split sel_exec)

theorem selBody_at : SiteOk selBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel

theorem selPair_acc {Wr : Word → Prop} {m : Mem} {dst a b M : Word} {k : Nat} (hk : k < 4)
    {s : State} (h : SelInv m dst a b M k s) (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0)
    (hb : b.toNat % 4 = 0) (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) :
    AccAll (AccOk Wr) selPair s := by
  obtain ⟨-, e0, e1, e2, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, lo⟩ := ld34_exec s
  refine accAll_append (ld34_acc s (by rw [e1]; exact slot_al ha _) (by rw [e2]; exact slot_al hb _)) ?_
  generalize hs1 : execAll ld34 s = s1 at lo
  have l0 : s1.regs 0 = slot dst (2 * k) := by rw [lo 0 (by decide) (by decide), e0]
  have pre : AccAll (AccOk Wr) [.dp .eors 5 3, .dp .eors 6 4, .dp .ands 5 7, .dp .ands 6 7,
      .dp .eors 3 5, .dp .eors 4 6] s1 := X25519MulcWord.accAll_regOnly _ _ (by decide)
  have e : (execAll [.dp .eors 5 3, .dp .eors 6 4, .dp .ands 5 7, .dp .ands 6 7, .dp .eors 3 5,
      .dp .eors 4 6] s1).reg 0 = slot dst (2 * k) := by
    rw [← l0]; exact execAll_regs_other _ _ 0 (by decide) (by decide)
  have := accAll_append (s := s1) pre (accAll_cons (stm_acc _ 0 0x18 (by rw [e]; exact slot_al hd _)
    (fun i hi q hq => by
      rw [e]; exact wr_words hW (k := 2 * k) (n := 2) (by omega) i (by rw [bitCount_18] at hi; exact hi)
        q hq)) (accAll_nil _ _))
  exact this

theorem sel_acc {Wr : Word → Prop} (s : State) {dst a b : Word} (h0 : s.regs 0 = dst)
    (h1 : s.regs 1 = a) (h2 : s.regs 2 = b) (hm : s.regs 7 = 0 ∨ s.regs 7 = BitVec.allOnes 32)
    (hf : dst.toNat + 32 ≤ 2 ^ 32) (ha : a = dst ∨ Disj a 32 dst 32)
    (hb : b = dst ∨ Disj b 32 dst 32) (hd : dst.toNat % 4 = 0) (hal : a.toNat % 4 = 0)
    (hbl : b.toNat % 4 = 0) (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) :
    AccAll (AccOk Wr) selBody s := by
  have I0 : SelInv s.mem dst a b (s.regs 7) 0 s :=
    ⟨⟨_, frame_init s.mem hf, fun i _ => by simp [selG]⟩, by rw [h0, slot_zero],
      by rw [h1, slot_zero], by rw [h2, slot_zero], rfl⟩
  rw [selBody_split]
  refine accAll_append (selPair_acc (by decide) I0 hd hal hbl hW) ?_
  obtain ⟨I1, -⟩ := selPair_step (by decide) hm ha hb I0
  generalize execAll selPair s = s1 at I1
  refine accAll_append (selPair_acc (by decide) I1 hd hal hbl hW) ?_
  obtain ⟨I2, -⟩ := selPair_step (by decide) hm ha hb I1
  generalize execAll selPair s1 = s2 at I2
  refine accAll_append (selPair_acc (by decide) I2 hd hal hbl hW) ?_
  obtain ⟨I3, -⟩ := selPair_step (by decide) hm ha hb I2
  generalize execAll selPair s2 = s3 at I3
  exact selPair_acc (by decide) I3 hd hal hbl hW

/-- One `select_words` block in a `ReachW` proof: `dst = r7 = 0 ? a : b`. `a` and `b` may
each be `dst` or disjoint from it; `r7` is unchanged. -/
theorem sel_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {dst a b : Word}
    (hseq : seqAt B off selBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize selBody))
    (h0 : t.regs 0 = dst) (h1 : t.regs 1 = a) (h2 : t.regs 2 = b)
    (hm : t.regs 7 = 0 ∨ t.regs 7 = BitVec.allOnes 32)
    (hd : dst.toNat % 4 = 0) (ha : a.toNat % 4 = 0) (hbb : b.toNat % 4 = 0)
    (hf : dst.toNat + 32 ≤ 2 ^ 32)
    (hda : a = dst ∨ Disj a 32 dst 32) (hdb : b = dst ∨ Disj b 32 dst 32)
    (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize selBody) →
      Field25519Routines.feVal t'.mem dst =
          (if t.regs 7 = 0 then Field25519Routines.feVal t.mem a else Field25519Routines.feVal t.mem b) →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) → t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  obtain ⟨ev, em, eo⟩ := sel_exec t h0 h1 h2 hm hf hda hdb
  refine Field25519Block.ReachW.blockAcc hb _ off hpc hoff hseq selBody_falls
    (sel_acc t h0 h1 h2 hm hf hda hdb hd ha hbb hW) hr (k _ ?_ ev em eo)
  rw [execAll_pc _ _ selBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
