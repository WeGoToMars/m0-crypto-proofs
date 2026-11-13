import M0Crypto.Release.X25519CRPhaseBC
import M0Crypto.Release.X25519CRTop
import M0Crypto.Release.X25519CRLoop
import M0Crypto.Release.X25519CRArith

set_option linter.unusedSimpArgs false

/-!
The machine effect of `X25519Macros.combineReduce sq` (both `sq = false`, `m0c_fe_mul`, and
`sq = true`, `m0c_fe_sqr`): phases A, B, C, the top word and the loop composed, and the value
closed by `X25519Reduce.combine_reduce_nat`.

Frame (slot numbers from `X25519Macros`): `L` at `SP_`, `H` at `SH`, the middle product `P` at
`SPP` with `P2, P3` in `r0, r1` (`pval`), the sign mask at `SN` (`NOk`), the output pointer at
`SDST`.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Congr
open M0Crypto.Release.X25519Macros (sl SH SP_ SPP SN SDST combineReduce reducePhaseA reducePhaseB
  reducePhaseC reduceTop reduceLoop)
open M0Crypto.Release.X25519Reduce (combine_reduce_nat)

/-- Eight frame words from slot `k` as one 256-bit value. -/
def w8 (m : Mem) (sp : Word) (k : Nat) : Nat :=
  w4 (fr m sp k) (fr m sp (k + 1)) (fr m sp (k + 2)) (fr m sp (k + 3)) +
    2 ^ 128 * w4 (fr m sp (k + 4)) (fr m sp (k + 5)) (fr m sp (k + 6)) (fr m sp (k + 7))

/-- The middle product as `mul128 SPP true` / `sqr128 SPP true` leave it: `P0, P1` in slots
`SPP, SPP + 1`, `P2, P3` in `r0, r1`, `P4..P7` in slots `SPP + 4 ..`. -/
def pval (s : State) : Nat :=
  w4 (fr s.mem s.sp SPP) (fr s.mem s.sp (SPP + 1)) (s.regs 0) (s.regs 1) +
    2 ^ 128 * w4 (fr s.mem s.sp (SPP + 4)) (fr s.mem s.sp (SPP + 5)) (fr s.mem s.sp (SPP + 6))
      (fr s.mem s.sp (SPP + 7))

/-- The Karatsuba middle term `Y`: `L + H - P` when `neg`, else `L + H + P`; below `2^257`. -/
def YOk (s : State) (neg : Bool) (Y : Nat) : Prop :=
  (if neg then Y + pval s = w8 s.mem s.sp SP_ + w8 s.mem s.sp SH
    else Y = w8 s.mem s.sp SP_ + w8 s.mem s.sp SH + pval s) ∧ Y < 2 ^ 257

/-- The effect of `combineReduce` from `s` to `t`: four words stored over `H0..H3`, eight words
at the output pointer (slot `SDST`) congruent to `L + 2^128 Y + 2^256 H` modulo `p`, registers
from `r13` up unchanged. -/
def CRPost (s : State) (Y : Nat) (t : State) : Prop :=
  ∃ f0 f1 f2 f3 o0 o1 o2 o3 o4 o5 o6 o7 : Word,
    t.mem = storeWords (storeWords s.mem (slot s.sp SH) [f0, f1, f2, f3]) (fr s.mem s.sp SDST)
      [o0, o1, o2, o3, o4, o5, o6, o7] ∧
    ((w4 o0 o1 o2 o3 + 2 ^ 128 * w4 o4 o5 o6 o7 : Nat) : Int) ≡p
      ((w8 s.mem s.sp SP_ + 2 ^ 128 * Y + 2 ^ 256 * w8 s.mem s.sp SH : Nat) : Int) ∧
    ∀ r : Reg, r ≠ 15 → 13 ≤ r.val → t.regs r = s.regs r

theorem lt3 (a b c : Word) : a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat < 2 ^ 96 := by
  have := a.isLt; have := b.isLt; have := c.isLt; omega

theorem lt7 (a b c d e f g : Word) :
    a.toNat + 2 ^ 32 * b.toNat + 2 ^ 64 * c.toNat + 2 ^ 96 * d.toNat + 2 ^ 128 * e.toNat +
      2 ^ 160 * f.toNat + 2 ^ 192 * g.toNat < 2 ^ 224 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; have := e.isLt; have := f.isLt
  have := g.isLt; omega

theorem combineReduce_exec (s : State) (sq neg : Bool) (Y : Nat) (hN : NOk sq s neg)
    (hY : YOk s neg Y) (hD : Disj (fr s.mem s.sp SDST) 32 s.sp (4 * (SH + 8))) :
    CRPost s Y (execAll (combineReduce sq) s) := by
  obtain ⟨hYe, hYlt⟩ := hY
  have h13 : (13 : Reg) ≠ 15 := by decide
  have e : execAll (combineReduce sq) s = execAll reduceLoop (execAll reduceTop
      (execAll reducePhaseC (execAll (reducePhaseB sq) (execAll (reducePhaseA sq) s)))) := by
    simp only [combineReduce, execAll_append]
  rw [e]
  -- phase A
  obtain ⟨a1, am, ao⟩ := phaseA_exec s sq neg hN
  generalize execAll (reducePhaseA sq) s = sA at a1 am ao
  have aSp : sA.sp = s.sp := ao 13 h13 (.inr (by decide))
  have hNA : NOk sq sA neg := by
    unfold NOk at hN ⊢; rw [am, aSp]; exact hN
  -- phase B
  obtain ⟨b1, bm, bo⟩ := phaseB_exec sA sq neg hNA
  generalize execAll (reducePhaseB sq) sA = sB at b1 bm bo
  have bSp : sB.sp = s.sp := by rw [← aSp]; exact bo 13 h13 (by decide)
  rw [am, aSp] at b1
  -- the middle term
  have hv := y_value neg _ _ _ _ _ _ _ _ _ _ _ (w4_lt _ _ _ _) (w4_lt _ _ _ _) (w4_lt _ _ _ _)
    (w4_lt _ _ _ _) (sB.regs 6).isLt (by rw [← xor4]; exact a1)
    (by rw [← xor4, ← mask_toNat]; exact b1) (by simpa only [pval, w8] using hYe) hYlt
  obtain ⟨hYv, hY8⟩ := hv
  -- phase C
  obtain ⟨f0, f1, f2, f3, cm, c1, co⟩ := phaseC_exec sB
  generalize execAll reducePhaseC sB = sC at cm c1 co
  have cSp : sC.sp = s.sp := by rw [← bSp]; exact co 13 h13 (by decide) (by decide)
  rw [bm, am, bSp] at c1 cm
  have hrd : ∀ j, j < 2 ^ 20 → (j < SH ∨ SH + 4 ≤ j) → fr sC.mem s.sp j = fr s.mem s.sp j :=
    fun j hj hj' => by
      have hS : SH + 4 < 2 ^ 27 := by decide
      rw [cm]
      exact fr_store_out s.sp (j := j) (by omega) [f0, f1, f2, f3] s.mem SH hS hj'
  obtain ⟨g0, g1, g2, g3⟩ := fr_store4 s.mem s.sp SH (by decide) f0 f1 f2 f3
  rw [← cm] at g0 g1 g2 g3
  -- top word
  obtain ⟨q, t4, t12, t12lt, t7, t2, t0, tm, tO⟩ := reduceTop_exec sC
  generalize execAll reduceTop sC = sT at t4 t12 t12lt t7 t2 t0 tm tO
  rw [cSp, hrd _ (by decide) (.inl (by decide)), hrd _ (by decide) (.inr (by decide))] at t12
  rw [cSp, hrd _ (by decide) (.inr (by decide))] at t0
  have tSp : sT.sp = s.sp := by rw [← cSp]; exact tO 13 h13 (by decide) (by decide)
  -- registers parked across phases B, C and the top word
  have hi : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 9 → sC.regs r = sA.regs r := fun r h15 h8 h9 => by
    rw [co r h15 h8 h9, bo r h15 h8]
  have r8 : sT.regs 8 = sA.regs 8 := by rw [tO 8 (by decide) (by decide) (by decide), hi 8 (by decide) (by decide) (by decide)]
  have r10 : sT.regs 10 = sA.regs 10 := by rw [tO 10 (by decide) (by decide) (by decide), hi 10 (by decide) (by decide) (by decide)]
  have r11 : sT.regs 11 = sA.regs 11 := by rw [tO 11 (by decide) (by decide) (by decide), hi 11 (by decide) (by decide) (by decide)]
  have r12 : sC.regs 12 = sA.regs 12 := hi 12 (by decide) (by decide) (by decide)
  have r9 : sT.regs 9 = sC.regs 9 := tO 9 (by decide) (by decide) (by decide)
  rw [r12] at t12
  have := w4_lt f0 f1 f2 f3; have := w4_lt (sB.regs 0) (sB.regs 1) (sB.regs 2) (sB.regs 3)
  have := w4_lt (fr s.mem s.sp SH) (fr s.mem s.sp (SH + 1)) (fr s.mem s.sp (SH + 2))
    (fr s.mem s.sp (SH + 3))
  have hC : w4 f0 f1 f2 f3 + 2 ^ 128 * (sC.regs 9).toNat =
      w4 (sB.regs 0) (sB.regs 1) (sB.regs 2) (sB.regs 3) + 2 ^ 128 * (sB.regs 6).toNat +
        w4 (fr s.mem s.sp SH) (fr s.mem s.sp (SH + 1)) (fr s.mem s.sp (SH + 2))
          (fr s.mem s.sp (SH + 3)) := by
    rw [c1]; exact Nat.mod_eq_of_lt (by omega)
  have h9 : (sT.regs 9).toNat ≤ 2 := by rw [r9]; omega
  have hL7 := (fr s.mem s.sp (SP_ + 7)).isLt; have hH7 := (fr s.mem s.sp (SH + 7)).isLt
  have := (sA.regs 12).isLt
  have hk : (sT.reg 4).toNat < 2 ^ 20 := by rw [t4]; omega
  have hD' : Disj (sT.reg 0) 32 sT.sp (4 * (SH + 8)) := by rw [t0, tSp]; exact hD
  -- the loop
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, k7, lm, l1, l7, lk, lO⟩ :=
    reduceLoop_exec sT t7 t2 hD' hk h9
  generalize execAll reduceLoop sT = sL at lm l1 l7 lk lO
  simp only [tm, tSp, Nat.add_zero, g0, g1, g2, g3, r8, r10, r11, r9, t4] at l1
  simp (disch := decide) only [hrd] at l1
  refine ⟨f0, f1, f2, f3, o0, o1, o2, o3, o4, o5, o6, o7, by rw [lm, tm, cm, t0], ?_, ?_⟩
  · let F := fun j => (fr s.mem s.sp j).toNat
    have hlo := lt3 o4 o5 o6
    have hw := w4_lt o0 o1 o2 o3
    obtain ⟨hno, hc⟩ := combine_reduce_nat (w8 s.mem s.sp SP_) (w8 s.mem s.sp SH) Y
      (F SP_ + 2 ^ 32 * F (SP_ + 1) + 2 ^ 64 * F (SP_ + 2) + 2 ^ 96 * F (SP_ + 3) +
        2 ^ 128 * F (SP_ + 4) + 2 ^ 160 * F (SP_ + 5) + 2 ^ 192 * F (SP_ + 6)) (F (SP_ + 7))
      (w4 (fr s.mem s.sp SH) (fr s.mem s.sp (SH + 1)) (fr s.mem s.sp (SH + 2))
        (fr s.mem s.sp (SH + 3)))
      (F (SH + 4) + 2 ^ 32 * F (SH + 5) + 2 ^ 64 * F (SH + 6)) (F (SH + 7))
      ((sA.regs 8).toNat + 2 ^ 32 * (sA.regs 10).toNat + 2 ^ 64 * (sA.regs 11).toNat)
      (sA.regs 12).toNat (w4 (sB.regs 0) (sB.regs 1) (sB.regs 2) (sB.regs 3)) (sB.regs 6).toNat
      (w4 f0 f1 f2 f3) ((sC.regs 9).toNat - (sB.regs 6).toNat) (sC.regs 9).toNat
      (F (SP_ + 7) + (sA.regs 12).toNat + 38 * F (SH + 7)) q (sT.regs 12).toNat
      (w4 o0 o1 o2 o3 + 2 ^ 128 * (o4.toNat + 2 ^ 32 * o5.toNat + 2 ^ 64 * o6.toNat)) k7
      (by simp only [w8, w4, F]; omega) (by simp only [w8, w4, F]; omega)
      (by simp only [w4] at hYv ⊢; omega)
      (lt7 _ _ _ _ _ _ _) hL7 (w4_lt _ _ _ _) (lt3 _ _ _) hH7 (lt3 _ _ _) (sA.regs 12).isLt
      (w4_lt _ _ _ _) hY8 (by omega) (w4_lt _ _ _ _) (by omega) rfl t12 t12lt
      (by simp only [w4, F] at l1 ⊢; omega) (by omega)
    have ev : w4 o0 o1 o2 o3 + 2 ^ 128 * w4 o4 o5 o6 o7 =
        w4 o0 o1 o2 o3 + 2 ^ 128 * (o4.toNat + 2 ^ 32 * o5.toNat + 2 ^ 64 * o6.toNat) +
          2 ^ 224 * ((sT.regs 12).toNat + k7) := by
      rw [Nat.mod_eq_of_lt hno] at l7
      simp only [w4]; rw [l7]; omega
    rw [ev]; exact hc
  · intro r h15 h13'
    have h8 : 8 ≤ r.val := by omega
    have h9 : r ≠ 9 := fun e => by rw [e] at h13'; exact absurd h13' (by decide)
    have h12 : r ≠ 12 := fun e => by rw [e] at h13'; exact absurd h13' (by decide)
    rw [lO r h15 h8, tO r h15 h8 h12, co r h15 h8 h9, bo r h15 h8, ao r h15 (.inr h13')]

end M0Crypto.Release.X25519CR
