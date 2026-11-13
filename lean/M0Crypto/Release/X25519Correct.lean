import M0Crypto.Release.X25519Prologue
import M0Crypto.Release.X25519LadderTail
import M0Crypto.Release.X25519ChainRun
import M0Crypto.Release.X25519Finish
import M0Crypto.Release.X25519OutAt
import M0Crypto.Release.X25519Ev

set_option linter.unusedSimpArgs false

/-!
The functional claim for `m0c_x25519`: `x25519_correct`.

The run is composed from the segment lemmas in code order: prologue (`prologue_w`), the ladder
over bits 254 to 3 (`loop_w`), the pending swap (`swap_w`), three doublings (`dbl_loop`), the
inversion chain (`chain_w`), the final product and canonical reduction (`finish_w`), and the
stores, wipe and epilogue (`tail_w`). Between segments the frame words that a later segment
needs (`LV_OUT`, `X2`) are carried by each segment's frame clause; the saved registers and
everything outside the wiped stack are carried by `Body`. `x25519_tail` and `output_canon`
connect the final slot value to RFC 7748 `X25519`; `reachW_runUntil` turns the run into the
model's `runUntil`.
-/

namespace M0Crypto.Release.X25519Correct
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW ReachS Region B B_len)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519SlotEnv
open M0Crypto.Release.X25519LadderStep
open M0Crypto.Release.X25519LadderLoop (Inv KeepL steps)
open M0Crypto.Release.X25519LadderTail (KeepT dblN)
open M0Crypto.Release.X25519Prologue (PrologueOut kWords kWords_val kWords_words kWords_length
  saveLo savedList)
open M0Crypto.Release.X25519OutAt (Saved)
open M0Crypto.Release.X25519OutEpi (savedReg)
open M0Crypto.Release.X25519Ladder (dbl3 ladderTop tailOut x25519_tail output_canon)
open M0Crypto.Spec.X25519 (LadderState ladderInit cswap)

section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

/-- The code bytes survive any change inside the stack window. -/
theorem code_of {m : Mem} (h : ∀ y, ¬ Region c.fp X25519.stackBytes y → m y = c.m0 y) :
    CodeAt m c.base B := fun i hi => by
  rw [h _ fun hy => X25519MulcFacts.region_ne hv.codeS hy i (by rw [B_len] at hi; exact hi) rfl]
  exact hv.code i hi

/-- The 4 bytes of `LV_OUT` lie outside every band a segment after the prologue changes. -/
theorem out_bytes {y : Word} (h : Region (slotAt c lvOut) 4 y) :
    Region (E c) LFRAME y ∧ ¬ Region (slotAt c sX2) (sK - sX2) y ∧ ¬ Region (slotAt c lvT) 8 y ∧
      ¬ Region (slotAt c lvT) 4 y ∧ ¬ Region (slotAt c sA) 128 y ∧ ¬ Region (slotAt c sZ2) 32 y ∧
      ¬ Region (slotAt c sX2) 32 y :=
  ⟨band_frame hv (by decide) h, band_disj hv (by decide) (by decide) (by decide) h,
    band_disj hv (by decide) (by decide) (by decide) h, band_disj hv (by decide) (by decide) (by decide) h,
    band_disj hv (by decide) (by decide) (by decide) h, band_disj hv (by decide) (by decide) (by decide) h,
    band_disj hv (by decide) (by decide) (by decide) h⟩

/-- The bytes of slot `X2` lie outside the bands the inversion chain changes. -/
theorem x2_bytes {y : Word} (h : Region (slotAt c sX2) 32 y) :
    Region (E c) LFRAME y ∧ ¬ Region (slotAt c sA) 128 y ∧ ¬ Region (slotAt c sZ2) 32 y ∧
      ¬ Region (slotAt c lvT) 4 y :=
  ⟨band_frame hv (by decide) h, band_disj hv (by decide) (by decide) (by decide) h,
    band_disj hv (by decide) (by decide) (by decide) h, band_disj hv (by decide) (by decide) (by decide) h⟩

theorem fp_le {y : Word} (h : Region c.fp X25519.wipeBytes y) : Region c.fp X25519.stackBytes y := by
  have hF := fp_toNat hv
  have := hv.spLo
  exact region_sub (by simp only [X25519.stackBytes] at *; omega) (Nat.le_refl _)
    (by simp only [X25519.stackBytes, X25519.wipeBytes] at *; omega) h

/-- The save area: word `i` of it, read from `E c`, is word `i` from `saveLo c`. -/
theorem save_addr (i : Nat) (hi : i < 9) :
    E c + BitVec.ofNat 32 (LFRAME + 4 * i) = saveLo c + BitVec.ofNat 32 (4 * i) := by
  have hsp := hv.spLo
  have e1 := E_add hv (d := LFRAME + 4 * i) (by simp only [LFRAME, SAVED]; omega)
  have hE := E_toNat hv
  apply BitVec.eq_of_toNat_eq
  rw [e1, Frame.toNat_add_ofNat _ _ (by
    simp only [saveLo, BitVec.toNat_sub, BitVec.toNat_ofNat, SAVED, X25519.stackBytes] at *
    have := c.sp0.isLt; omega)]
  simp only [saveLo, BitVec.toNat_sub, BitVec.toNat_ofNat, SAVED, LFRAME, X25519.stackBytes] at *
  have := c.sp0.isLt
  omega

/-- Save-area words are outside the wiped bytes. -/
theorem save_out (i : Nat) (hi : i < 9) {y : Word}
    (h : Region (E c + BitVec.ofNat 32 (LFRAME + 4 * i)) 4 y) : ¬ Region c.fp X25519.wipeBytes y := by
  have hsp := hv.spLo
  have e1 := E_add hv (d := LFRAME + 4 * i) (by simp only [LFRAME, SAVED]; omega)
  have hE := E_toNat hv
  have hF := fp_toNat hv
  have := c.sp0.isLt
  rw [region_iff (by simp only [LFRAME, SAVED, X25519.stackBytes] at *; omega)] at h
  rw [region_iff (by simp only [X25519.wipeBytes, X25519.stackBytes] at *; omega)]
  simp only [LFRAME, SAVED, X25519.stackBytes, X25519.wipeBytes] at *
  omega

omit hv in
theorem saved_list (i : Nat) (hi : i < 9) (hl : i < (savedList c).length) :
    (savedList c)[i] = c.regs0 (savedReg i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => rfl

end

theorem cswap_fst (sw : Nat) (a b : Int) : (cswap sw a b).1 = if sw = 1 then b else a := by
  unfold cswap; split <;> rfl

/-- The value whose canonical residue the code stores: `x * z ^ (p - 2)` of the RFC route
(`tailOut`). -/
def route (k : Nat) (u : Int) : Int :=
  let S := ladderTop k u
  let d := dbl3 (cswap S.swap S.x2 S.x3).1 (cswap S.swap S.z2 S.z3).1
  d.1 * d.2 ^ (2 ^ 255 - 21)

/-- Byte `i` of a canonical residue `cv` of `route` is byte `i` of RFC 7748 `X25519`. -/
theorem out_value (c : X25519.Ctx) (cv : Nat) (hlt : cv < 2 ^ 255 - 19)
    (hm : ModP cv (route (Spec.X25519.decodeScalar25519 c.scalarB)
      (Spec.X25519.decodeUCoordinate c.pointB : Int)))
    (i : Nat) (hi : i < 32) : c.outB i = BitVec.ofNat 8 (cv / 2 ^ (8 * i)) := by
  have hk : Spec.X25519.decodeScalar25519 c.scalarB % 8 = 0 := by
    rw [← kWords_val]; exact (X25519Decode.clamped_bounds c.scalarB).1
  have hp : (cv : Int) < Spec.X25519.p := by unfold Spec.X25519.p; omega
  unfold X25519.Ctx.outB
  rw [x25519_tail _ _ hk]
  unfold tailOut
  rw [output_canon _ _ cv hp hm]
  simp [hi]

/-- The whole run: from a valid entry to the return with `Result`, every event satisfying
`X25519Ev.Ev` (allowed PCs and writes, input reads at load sites, `out` writes at store sites). -/
theorem x25519_run {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s) :
    ReachS c.base (X25519Ev.Ev c) s fun t => t.pc = c.ret ∧ X25519.Result c t := by
  have hv := hp.valid
  have hWr0 : ∀ y, Region c.fp X25519.stackBytes y → X25519.WrOk c y := fun y h => Or.inl h
  have hPO := X25519Ev.midPcOk c
  have hL : oLadder ≤ oLadder := Nat.le_refl _
  have hH : oStore ≤ oStore := Nat.le_refl _
  refine X25519Block.seg (fun _ _ h => X25519Ev.liftPro h)
    (X25519Prologue.prologue_w hp (fun y h => h) (X25519Ev.proPc c) ?_)
  intro t1 t1pc P
  refine ReachS.done ?_
  refine X25519Block.seg (fun _ _ h => X25519Ev.liftMid h) ?_
  have hcode := code_of hv P.outside
  generalize hu : (Spec.X25519.decodeUCoordinate c.pointB : Int) = u
  -- the ladder over bits 254 to 3
  have I0 : Inv c u (kWords c) t1.mem (251 + 3) (ladderInit u) := by
    refine ⟨P.tctr, ?_, Nat.zero_le _, ?_, ⟨?_, ?_, ?_, ?_⟩, P.scalar⟩
    · show (read32 t1.mem (E c + BitVec.ofNat 32 lvSwap)).toNat = 0
      rw [P.swap]; rfl
    · show ModP ((feVal t1.mem (E c + BitVec.ofNat 32 sX1) : Nat) : Int) u
      rw [P.x1, ← hu]; exact ModP.refl _
    · show ModP ((feVal t1.mem (E c + BitVec.ofNat 32 sX2) : Nat) : Int) 1
      rw [P.x2]; exact ModP.refl _
    · show ModP ((feVal t1.mem (E c + BitVec.ofNat 32 sZ2) : Nat) : Int) 0
      rw [P.z2]; exact ModP.refl _
    · show ModP ((feVal t1.mem (E c + BitVec.ofNat 32 sX3) : Nat) : Int) u
      rw [P.x3, ← hu]; exact ModP.refl _
    · show ModP ((feVal t1.mem (E c + BitVec.ofNat 32 sZ3) : Nat) : Int) 1
      rw [P.z3]; exact ModP.refl _
  refine X25519LadderLoop.loop_w X25519OpInline.add_opW X25519OpInline.sub_opW
    X25519OpInline.sel_opW hv hcode hWr0 hPO hL hH (kWords_words c) (kWords_length c) 251 (by decide)
    (ladderInit u) t1 t1pc P.body I0 ?_
  intro t2 t2pc b2 I2 K2
  generalize hS : steps (X25519Val.val (kWords c)) u (ladderInit u) 251 = S at I2
  -- the pending swap
  refine X25519LadderTail.swap_w hv hcode hWr0 hPO hL hH X25519OpInline.sel_opW t2pc b2
    (by rw [I2.sw]; exact I2.swle) ?_
  intro t3 t3pc b3 ex ez tw3 K3
  have hx3 : ModP (env c t3.mem sX2) (cswap S.swap S.x2 S.x3).1 := by
    rw [ex, I2.sw, cswap_fst]
    split
    · exact I2.mt.x3
    · exact I2.mt.x2
  have hz3 : ModP (env c t3.mem sZ2) (cswap S.swap S.z2 S.z3).1 := by
    rw [ez, I2.sw, cswap_fst]
    split
    · exact I2.mt.z3
    · exact I2.mt.z2
  -- three doublings
  refine X25519LadderTail.dbl_loop hv hcode hWr0 hPO hL hH X25519OpInline.add_opW X25519OpInline.sub_opW 2
    (by decide) _ _ t3 t3pc b3 tw3 hx3 hz3 ?_
  intro t4 t4pc b4 vx vz _ K4
  -- the inversion chain
  refine X25519ChainRun.chain_w hv hcode hWr0 hPO hL hH t4pc b4 ?_
  intro t5 t5pc b5 hz5 K5
  -- the final product and reduction
  refine X25519Finish.finish_w hv hcode hWr0 hPO hL hH t5pc b5 ?_
  intro t6 t6pc b6 r6 hv6 hlt6 K6
  refine ReachS.done ?_
  -- frame words needed by the tail
  have hout : read32 t6.mem (E c + BitVec.ofNat 32 lvOut) = c.out := by
    rw [← P.out]
    refine read32_congr' fun y hy => ?_
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := out_bytes hv hy
    rw [K6 y f1 f7, K5 y f1 f5 f6 f4, K4 y f1 f2 f4, K3 y f1 f2 f4, K2 y f1 f2 f3]
  have hsv : Saved c t6.mem := by
    intro i hi
    rw [← saved_list i hi (by rw [show (savedList c).length = 9 from rfl]; exact hi),
      ← P.saved i (by rw [show (savedList c).length = 9 from rfl]; exact hi), ← save_addr hv i hi]
    exact read32_congr' fun y hy => b6.keep y (save_out hv i hi hy)
  -- the value of `X2`
  have e54 : env c t5.mem sX2 = env c t4.mem sX2 :=
    congrArg (fun n : Nat => (n : Int)) (feVal_congr fun y hy => by
      obtain ⟨f1, f2, f3, f4⟩ := x2_bytes hv hy
      exact K5 y f1 f2 f3 f4)
  have hval : ModP (feVal t6.mem (slotAt c sX2) : Int)
      ((dblN (2 + 1) (cswap S.swap S.x2 S.x3).1 (cswap S.swap S.z2 S.z3).1).1 *
        (dblN (2 + 1) (cswap S.swap S.x2 S.x3).1 (cswap S.swap S.z2 S.z3).1).2 ^ (2 ^ 255 - 21)) := by
    refine hv6.trans (ModP.mul (by rw [e54]; exact vx) (hz5.trans (ModP.pow vz _)))
  have hSt : S = ladderTop (Spec.X25519.decodeScalar25519 c.scalarB) u := by
    rw [← hS, ← kWords_val]; rfl
  subst hSt
  subst hu
  have hval' : ModP (feVal t6.mem (slotAt c sX2) : Int) (route (Spec.X25519.decodeScalar25519 c.scalarB)
      (Spec.X25519.decodeUCoordinate c.pointB : Int)) := hval
  refine (X25519OutAt.tail_w hv hp.thumb (fun _ _ h => X25519Ev.liftS h)
    (fun _ _ h => X25519Ev.liftW h) t6pc b6.sp r6 hout hsv).mono (fun _ _ h => h) ?_
  rintro t ⟨tpc, tsp, tcal, t0, t1', t2', t3', t12, tout, twipe, tmem⟩
  refine ⟨tpc, tpc, tsp, tcal, t0, t1', t2', t3', t12, fun y hy => ?_, twipe⟩
  by_cases ho : Region c.out 32 y
  · simp only [ho, ↓reduceIte]
    have hi : c.oidx y < 32 := ho
    have ey : y = c.out + BitVec.ofNat 32 (c.oidx y) := by
      unfold X25519.Ctx.oidx
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [ey, tout _ hi, ← ey]
    exact (out_value c _ hlt6 hval' _ hi).symm
  · simp only [ho, ↓reduceIte]
    rw [tmem y (fun h => hy (fp_le hv h)) ho]
    rw [b6.keep y fun h => hy (fp_le hv h)]
    exact P.outside y hy

theorem x25519_correct : X25519.Correct := by
  intro c s hp
  have hv := hp.valid
  have hc0 : CodeAt s.mem c.base B := by rw [hp.entry.mem]; exact hv.code
  have hwc : ∀ y, X25519.WrOk c y → ∀ i < B.length, y ≠ c.base + BitVec.ofNat 32 i := by
    intro y hy i hi
    rw [B_len] at hi
    rcases hy with hy | hy
    · exact X25519MulcFacts.region_ne hv.codeS hy i hi
    · exact X25519MulcFacts.region_ne hv.codeO hy i hi
  exact X25519MulcFacts.reachW_runUntil hc0 hwc hp.retOut
    ((x25519_run hp).mono (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ h => h)

end M0Crypto.Release.X25519Correct

namespace M0Crypto.Release.X25519

/-- Every valid call of `m0c_x25519` returns with `Result` (RFC 7748 output in
`out`, callee-saved registers and SP restored, r0-r3 and r12 zero, the 480 stack bytes below the
saved registers zero) and writes
only its stack window and `out`. -/
theorem x25519_correct : Correct := X25519Correct.x25519_correct

end M0Crypto.Release.X25519
