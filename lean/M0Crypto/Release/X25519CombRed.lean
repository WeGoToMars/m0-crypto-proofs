import M0Crypto.Release.X25519CRAcc

set_option linter.unusedSimpArgs false

/-!
Macro `combineReduce sq` of `m0c_fe_mul` (`sq = false`) and `m0c_fe_sqr` (`sq = true`): the
fused Karatsuba combine and reduction modulo `p = 2^255 - 19`.

* `combineReduce_exec` (in `X25519CRExec`): the effect `CRPost` — four words stored over
  `H0..H3`, eight output words at the pointer in slot `SDST` congruent to
  `L + 2^128 Y + 2^256 H`, registers from `r13` up unchanged.
* `combineReduce_acc`: every access is aligned; writes only to the 16 bytes at slot `SH` and
  the 32 output bytes.
* `combineReduce_run_w`: the `ReachW` block lemma, the size taken from `seqSize`.

The proof is split over `X25519CRBase` (frame words), `X25519CRWord` and `X25519CRLoop`
(the loop), `X25519CRPhase` (phase A), `X25519CRAddH` and `X25519CRPhaseBC` (phases B, C),
`X25519CRTop` (the top word), `X25519CRArith` (the 9-word middle term), `X25519CRExec`
(composition) and `X25519CRAcc` (accesses).
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Macros (SH SDST combineReduce reducePhaseA reducePhaseB reducePhaseC
  reduceTop reduceLoop)

/-- The accesses of `combineReduce`: aligned; writes only to the four words at slot `SH` and the
eight words at the output pointer (slot `SDST`). -/
theorem combineReduce_acc {Wr : Word → Prop} (s : State) (sq : Bool) (hsp : s.sp.toNat % 4 = 0)
    (hd : (fr s.mem s.sp SDST).toNat % 4 = 0)
    (hWH : ∀ j < 16, Wr (slot s.sp SH + BitVec.ofNat 32 j))
    (hWd : ∀ j < 32, Wr (fr s.mem s.sp SDST + BitVec.ofNat 32 j)) :
    AccAll (AccOk Wr) (combineReduce sq) s := by
  simp only [combineReduce, List.append_assoc]
  refine accAll_append (phaseA_acc sq s hsp) ?_
  have mA : (execAll (reducePhaseA sq) s).mem = s.mem :=
    execAll_mem _ _ (by cases sq <;> decide)
  have pA : (execAll (reducePhaseA sq) s).sp = s.sp := sp_keep _ _ (by cases sq <;> decide)
  generalize execAll (reducePhaseA sq) s = sA at mA pA ⊢
  refine accAll_append (phaseB_acc sq sA (by rw [pA]; exact hsp)) ?_
  have mB : (execAll (reducePhaseB sq) sA).mem = s.mem := by
    rw [execAll_mem _ _ (by cases sq <;> decide), mA]
  have pB : (execAll (reducePhaseB sq) sA).sp = s.sp := by
    rw [sp_keep _ _ (by cases sq <;> decide), pA]
  generalize execAll (reducePhaseB sq) sA = sB at mB pB ⊢
  refine accAll_append (phaseC_acc sB (by rw [pB]; exact hsp) (by rw [pB]; exact hWH)) ?_
  obtain ⟨f0, f1, f2, f3, cm, -, co⟩ := phaseC_exec sB
  have pC : (execAll reducePhaseC sB).sp = s.sp := by
    rw [← pB]; exact co 13 (by decide) (by decide) (by decide)
  rw [mB, pB] at cm
  generalize execAll reducePhaseC sB = sC at cm pC ⊢
  refine accAll_append (top_acc sC (by rw [pC]; exact hsp)) ?_
  obtain ⟨-, -, -, -, -, -, t0, -, tO⟩ := reduceTop_exec sC
  have pT : (execAll reduceTop sC).sp = s.sp := by
    rw [← pC]; exact tO 13 (by decide) (by decide) (by decide)
  have r0 : (execAll reduceTop sC).reg 0 = fr s.mem s.sp SDST := by
    rw [t0, pC, cm]
    exact fr_store_out s.sp (by decide) _ _ _ (by simp only [List.length_cons, List.length_nil]; decide)
      (.inr (by simp only [List.length_cons, List.length_nil]; decide))
  exact loop_acc _ hd hWd _ (by rw [pT]; exact hsp) r0

theorem combineReduce_falls (sq : Bool) : (combineReduce sq).all Instr.falls = true := by
  cases sq <;> decide

/-- One `combineReduce` block in a `ReachW` proof. -/
theorem combineReduce_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {sq neg : Bool} {Y : Nat}
    (hseq : seqAt B off (combineReduce sq) = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (combineReduce sq)))
    (hsp : t.sp.toNat % 4 = 0) (hd : (fr t.mem t.sp SDST).toNat % 4 = 0)
    (hWH : ∀ j < 16, Wr (slot t.sp SH + BitVec.ofNat 32 j))
    (hWd : ∀ j < 32, Wr (fr t.mem t.sp SDST + BitVec.ofNat 32 j))
    (hN : NOk sq t neg) (hY : YOk t neg Y)
    (hD : Disj (fr t.mem t.sp SDST) 32 t.sp (4 * (SH + 8))) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (combineReduce sq)) →
      CRPost t Y t' → ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hf := combineReduce_falls sq
  refine ReachW.blockAcc hb _ off hpc hoff hseq hf (combineReduce_acc t sq hsp hd hWH hWd) hr
    (k _ ?_ (combineReduce_exec t sq neg Y hN hY hD))
  rw [execAll_pc _ _ hf, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519CR
