import M0Crypto.Release.X25519LadderStep
import M0Crypto.Release.X25519ChainLoop
import M0Crypto.Release.X25519EntrySeg
import M0Crypto.Release.X25519Decode
import M0Crypto.Release.X25519Branch

set_option linter.unusedSectionVars false

/-!
The ladder loop of `m0c_x25519` (`X25519EntryCode.ladderAt`).

`Inv` is the loop invariant at the head with counter `t` in `LV_T`: the swap word is the RFC
`swap`, `X1` is `u`, the slots `X2, Z2, X3, Z3` match the RFC state (`X25519Ladder.Matches`)
and the scalar words are `ws`. `iter_w` runs one iteration (`step_w`, `decT`, `cmp r0, #3`, the
exit test and the back branch); `loop_w` runs the loop from `t = n + 3` to the exit with
`t = 2`, after the RFC steps `n + 3, ..., 3` (`steps`).
-/

namespace M0Crypto.Release.X25519LadderLoop
open M0Crypto.Armv6M (Word State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519SlotEnv
open M0Crypto.Release.X25519LadderStep
open M0Crypto.Release.X25519Block (Runs AccOk)
open M0Crypto.Release.X25519Val (val Words)
open M0Crypto.Spec.X25519 (LadderState ladderStep)
open M0Crypto.Release.X25519Ladder (Matches)

/-! ## Exit test -/

/-- `cmp r0, #3; blt`: the signed `r0 < 3` test. -/
def lt3 (x : Word) : Bool :=
  (M0Crypto.Armv6M.addWithCarry x 4294967292#32 true).1.msb !=
    (M0Crypto.Armv6M.addWithCarry x 4294967292#32 true).2.2

theorem cmp3 (u : State) : condPassed 11#4 ((Instr.cmpImm 0 3#8).next u) = lt3 (u.regs 0) := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg,
    condPassed, X25519Mem.toReg0, lt3]

theorem lt3_ofNat : ∀ j : Fin 256, lt3 (BitVec.ofNat 32 j.val) = decide (j.val < 3) := by
  decide +kernel

/-- `decT` then `cmp r0, #3`, from `LV_T = j + 1`. -/
theorem tail_runs {Wr : Word → Prop} (u : State) {j : Nat} (hj : j + 1 < 256)
    (hT : read32 u.mem (u.sp + BitVec.ofNat 32 lvT) = BitVec.ofNat 32 (j + 1))
    (hal : (u.sp + BitVec.ofNat 32 lvT).toNat % 4 = 0)
    (hw : ∀ k < 4, Wr (u.sp + BitVec.ofNat 32 lvT + BitVec.ofNat 32 k)) :
    Runs (AccOk Wr) (decT ++ [.cmpImm 0 3]) u (fun t => t.regs 13 = u.regs 13 ∧
      t.mem = write32 u.mem (u.sp + BitVec.ofNat 32 lvT) (BitVec.ofNat 32 j) ∧
      condPassed 11#4 t = decide (j < 3)) := by
  have hd := X25519ChainLoop.decT_runs u hal hw
  have r0 : (execAll decT u).regs 0 = BitVec.ofNat 32 j := by
    have : (execAll decT u).regs 0 = read32 u.mem (u.sp + BitVec.ofNat 32 lvT) - 1#32 := by
      simp [decT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZCV, State.setNZ,
        addFlags, State.sp, State.reg, X25519Mem.toReg0, X25519ChainLoop.lvT_off,
        X25519ChainLoop.lvT_off', X25519ChainLoop.awc_dec]
    rw [this, hT, X25519ChainLoop.ofNat_dec hj]
  rw [hT, X25519ChainLoop.ofNat_dec hj] at hd
  refine Runs.append (Q1 := fun t => (t.regs 13 = u.regs 13 ∧
      t.mem = write32 u.mem (u.sp + BitVec.ofNat 32 lvT) (BitVec.ofNat 32 j) ∧ _) ∧
      t.regs 0 = BitVec.ofNat 32 j) ⟨hd.1, hd.2, r0⟩ fun t ⟨⟨h13, hm, _⟩, h0⟩ => ?_
  refine X25519Block.Runs.reg (by decide) (by decide) ⟨?_, ?_, ?_⟩
  · simp [execAll, Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, h13]
  · simp [execAll, Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, hm]
  · show condPassed 11#4 ((Instr.cmpImm 0 3#8).next t) = _
    rw [cmp3, h0]
    exact lt3_ofNat ⟨j, by omega⟩

/-! ## The scalar bit -/

theorem bit_val {c : X25519.Ctx} {m : Mem} {ws : List Nat} (hw : Words ws) (hl : ws.length = 8)
    (hkw : ∀ i, i < 8 → (read32 m (slotAt c (sK + 4 * i))).toNat = ws.getD i 0)
    {t : Nat} (ht : t < 256) (htw : tWord c m = BitVec.ofNat 32 t) :
    (bitWord c m).toNat = (val ws >>> t) &&& 1 := by
  unfold bitWord
  rw [htw]
  have e1 : (BitVec.ofNat 32 t >>> 3) &&& 28#32 = BitVec.ofNat 32 (4 * (t / 32)) := by
    apply BitVec.eq_of_toNat_eq
    have h := X25519Decode.word_index t ht
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show t < 2 ^ 32 by omega), Nat.reducePow, Nat.reduceMod]
    omega
  have e2 : slotAt c sK + BitVec.ofNat 32 (4 * (t / 32)) = slotAt c (sK + 4 * (t / 32)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [slotAt, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hn : (BitVec.ofNat 32 t).toNat % 256 % 32 = t % 32 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [e1, e2, X25519Decode.ror_bit, hn, hkw _ (by omega),
    X25519Decode.scalar_bit ws hw t (by rw [hl]; omega)]
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t / 32 < ws.length by rw [hl]; omega), Option.getD_some]

/-! ## Invariant -/

/-- The frame at the loop head with counter `t` and RFC state `st`. -/
structure Inv (c : X25519.Ctx) (u : Int) (ws : List Nat) (m : Mem) (t : Nat)
    (st : LadderState) : Prop where
  tw : tWord c m = BitVec.ofNat 32 t
  sw : (swWord c m).toNat = st.swap
  swle : st.swap ≤ 1
  x1 : ModP (env c m sX1) u
  mt : Matches st (env c m sX2) (env c m sZ2) (env c m sX3) (env c m sZ3)
  kw : ∀ i, i < 8 → (read32 m (slotAt c (sK + 4 * i))).toNat = ws.getD i 0

/-- Frame bytes outside the slots `X2..D` and the words `LV_T`, `LV_SWAP`. -/
def KeepL (c : X25519.Ctx) (s t : State) : Prop :=
  ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sX2) (sK - sX2) y →
    ¬ Region (slotAt c lvT) 8 y → t.mem y = s.mem y

theorem KeepL.trans {c : X25519.Ctx} {s t v : State} (h1 : KeepL c s t) (h2 : KeepL c t v) :
    KeepL c s v := fun y a b d => (h2 y a b d).trans (h1 y a b d)

/-- The RFC steps `n + 3, ..., 3` from `st`. -/
def steps (k : Nat) (u : Int) (st : LadderState) (n : Nat) : LadderState :=
  ((List.range' 3 (n + 1)).reverse).foldl (ladderStep k u) st

theorem steps_succ (k : Nat) (u : Int) (st : LadderState) (n : Nat) :
    steps k u st (n + 1) = steps k u (ladderStep k u st (n + 4)) n := by
  unfold steps
  rw [List.range'_concat]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.foldl_cons]
  congr 2
  omega

theorem steps_zero (k : Nat) (u : Int) (st : LadderState) :
    steps k u st 0 = ladderStep k u st 3 := rfl

section
variable (hAdd : OpW .add) (hSub : OpW .sub) (hSel : OpW .sel)
  {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
  (hL : lo ≤ oLadder) (hH : oStore ≤ hi)
  {u : Int} {ws : List Nat} (hw : Words ws) (hl : ws.length = 8)
include hAdd hSub hSel hv hcode hWr hPO hL hH hw hl

/-- One iteration from the head with `t = n + 3`. -/
theorem iter_w {Q : State → Prop} {n : Nat} (hn : n + 3 ≤ 254) {st : LadderState} {s : State}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oLadder) (hs : Body c m1 s)
    (hI : Inv c u ws s.mem (n + 3) st)
    (kExit : n = 0 → ∀ t, t.pc = c.base + BitVec.ofNat 32 oSwap → Body c m1 t →
      Inv c u ws t.mem 2 (ladderStep (val ws) u st 3) → KeepL c s t →
      ReachW c.base Pc Wr t Q)
    (kBack : ∀ j, n = j + 1 → ∀ t, t.pc = c.base + BitVec.ofNat 32 oLadder → Body c m1 t →
      Inv c u ws t.mem (j + 3) (ladderStep (val ws) u st (n + 3)) → KeepL c s t →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have hseq := X25519EntrySeg.ladder_seg
  have hev : oLadder % 2 = 0 := by decide +kernel
  have hSS : oSwap ≤ oStore := by decide +kernel
  have hn' : seqSize (stepAt oLadder) + 10 < 2045 := by decide +kernel
  have hn := X25519OpRun.seqSize_even (stepAt oLadder)
  have e : ladderAt oLadder = stepAt oLadder ++ ((decT ++ [.cmpImm 0 3]) ++
      [bcTo 0xb (oLadder + seqSize (stepAt oLadder) + 6 + 2) (oLadder + seqSize (stepAt oLadder) + 6 + 6),
       bTo (oLadder + seqSize (stepAt oLadder) + 6 + 4) oLadder]) := by
    simp only [ladderAt, List.append_assoc, List.cons_append, List.nil_append]
  have h8 : seqSize (decT ++ [Instr.cmpImm 0 3]) = 8 := by decide
  have hW : oSwap = oLadder + seqSize (stepAt oLadder) + 8 + 4 := by
    show oLadder + seqSize (ladderAt oLadder) = _
    have h4 : ∀ a b d, seqSize [bcTo 0xb a b, bTo d oLadder] = 4 := fun _ _ _ => rfl
    rw [e, seqSize_append, seqSize_append, h8, h4]; omega
  rw [e, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true, h8] at hseq
  obtain ⟨hA, hB, hC⟩ := hseq
  simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hC
  rw [hW] at kExit
  generalize oLadder = o at hpc hev hn hn' hA hB hC hW hSS kExit kBack hL
  generalize hN : seqSize (stepAt o) = sz at hn hn' hB hC hW kExit
  have hC1 : instrAt B (o + sz + 8) = some (bcTo 0xb (o + sz + 8) (o + sz + 8 + 4)) := by
    have h := hC.1.1
    rwa [show o + sz + 6 + 2 = o + sz + 8 by omega, show o + sz + 6 + 6 = o + sz + 8 + 4 by omega] at h
  have hC2 : instrAt B (o + sz + 8 + 2) = some (bTo (o + sz + 8 + 2) o) := by
    have h := hC.2.1
    simp only [bcTo, Instr.size] at h
    rwa [show o + sz + 6 + 4 = o + sz + 8 + 2 by omega] at h
  -- the step
  refine step_w hAdd hSub hSel hv hcode hWr hPO hA hev hL (by omega) hpc hs
    (by rw [hI.sw]; exact hI.swle) ?_
  intro t1 pc1 hb1 so
  rw [hN] at pc1
  have t1sp : t1.sp = E c := hb1.sp
  obtain ⟨al, wr, lv⟩ := X25519ChainLoop.lvT_facts hv (d := sX2) (by decide +kernel)
  -- LV_T after the step
  have hT1 : read32 t1.mem (E c + BitVec.ofNat 32 lvT) = BitVec.ofNat 32 (n + 3) := by
    rw [← hI.tw]
    refine read32_congr' fun y hy => so.keep y (band_frame hv (by decide +kernel) hy)
      (band_disj hv (by decide +kernel) (by decide +kernel) (by decide +kernel) hy)
      (band_disj hv (by decide +kernel) (by decide +kernel) (by decide +kernel) hy)
  -- decrement and compare
  have hrun := tail_runs (Wr := Wr) t1 (j := n + 2) (by omega)
    (by rw [t1sp, show n + 2 + 1 = n + 3 from rfl]; exact hT1)
    (by rw [t1sp]; exact al) (fun q hq => hWr _ (by rw [t1sp]; exact wr q hq))
  have hreg : M0Crypto.Release.InRegion Pc c.base (o + sz)
      (seqSize (decT ++ [Instr.cmpImm 0 3])) := hPO.inE (by omega) (by rw [h8]; omega)
  have hfalls : (decT ++ [Instr.cmpImm 0 3]).all Instr.falls = true := by decide
  refine X25519Block.ReachW.blockRuns hb0 (decT ++ [.cmpImm 0 3]) (o + sz) pc1 ?g1 ?g2 ?g3 hrun ?g5 ?_
  case g1 => omega
  case g2 => exact hB
  case g3 => exact hfalls
  case g5 => exact hreg
  rintro t2 pc2 ⟨h13, hm2, hcp⟩
  have hcp' : condPassed 11 t2 = decide (n + 2 < 3) := hcp
  rw [h8] at pc2
  rw [t1sp] at hm2
  -- facts on t2
  have k21 : ∀ y, ¬ Region (slotAt c lvT) 4 y → t2.mem y = t1.mem y := fun y hy => by
    rw [hm2]; exact X25519LadderBit.write32_out hy
  have keep : KeepL c s t2 := fun y h1 h2 h3 => by
    rw [k21 y fun h => h3 (band_sub hv (Nat.le_refl _) (by decide +kernel) (by decide +kernel) h)]
    exact so.keep y h1 h2 fun h => h3 (band_sub hv (by decide +kernel) (by decide +kernel) (by decide +kernel) h)
  have hb2 : Body c m1 t2 := ⟨by rw [h13]; exact hb1.sp, fun y hy => by
    rw [k21 y fun h => hy (lv y h).1]; exact hb1.keep y hy⟩
  have envE : ∀ e, SlotOk e → env c t2.mem e = env c t1.mem e := fun e he =>
    congrArg (fun n : Nat => (n : Int)) (feVal_congr fun y hy => k21 y
      (band_disj hv (by have := he.1; have := he.2; simp only [LFRAME, lvT] at *; omega) he.2
        (by decide +kernel) hy))
  -- the RFC step
  obtain ⟨A, B', C, D, SA, SB, DA, CB, X3s, Z3d, Z3s, AA, BB, E', T, hsl⟩ := so.slots
  have hbit := bit_val hw hl hI.kw (by omega) hI.tw
  have hx : (swWord c s.mem ^^^ bitWord c s.mem).toNat =
      st.swap ^^^ ((val ws >>> (n + 3)) &&& 1) := by
    rw [BitVec.toNat_xor, hI.sw, hbit]
  rw [hx] at hsl
  obtain ⟨hm, hsw⟩ := X25519Ladder.ladderStep_congr (val ws) u (env c s.mem sX1) st (n + 3)
    hI.swle hI.x1 hI.mt hsl
  have hI2 : ∀ j, j = n + 2 → Inv c u ws t2.mem j (ladderStep (val ws) u st (n + 3)) := by
    intro j hj
    subst hj
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show read32 t2.mem (slotAt c lvT) = _
      rw [hm2]; exact M0Crypto.Armv6M.read32_write32_same _ _ _
    · have e1 : swWord c t2.mem = swWord c t1.mem := read32_congr' fun y hy => k21 y
        (band_disj hv (by decide +kernel) (by decide +kernel) (by decide +kernel) hy)
      rw [e1, so.swap, hbit, hsw]
    · rw [hsw]; exact Nat.and_le_right
    · have e1 : env c t2.mem sX1 = env c s.mem sX1 :=
        congrArg (fun n : Nat => (n : Int)) (feVal_congr fun y hy => keep y
          (band_frame hv (by decide +kernel) hy) (band_disj hv (by decide +kernel) (by decide +kernel) (by decide +kernel) hy)
          (band_disj hv (by decide +kernel) (by decide +kernel) (by decide +kernel) hy))
      rw [e1]; exact hI.x1
    · rw [envE _ (by decide +kernel), envE _ (by decide +kernel), envE _ (by decide +kernel), envE _ (by decide +kernel)]
      exact hm
    · intro i hi
      rw [← hI.kw i hi]
      refine congrArg BitVec.toNat (read32_congr' fun y hy => keep y (band_frame hv (by simp only [sK, LFRAME]; omega) hy)
        (band_disj hv (by simp only [sK, sX2]; omega) (by simp only [sK, LFRAME]; omega)
          (by decide +kernel) hy)
        (band_disj hv (by simp only [sK, lvT]; omega) (by simp only [sK, LFRAME]; omega)
          (by decide +kernel) hy))
  -- exit test
  have hb2' : ∀ x, Body c m1 (t2.setReg 15 x) := fun x => X25519ChainLoop.setReg15_body hb2 x
  refine ReachW.bcond hb0 (o + sz + 8) (o + sz + 8 + 4) 11 _ pc2 (by omega) hC1 (by omega)
    (X25519Branch.bc_fwd4 _) (hPO.atE (by omega) (by omega)) ?_ ?_
  · intro hc
    rw [hcp'] at hc
    have hn0 : n = 0 := by simp at hc; omega
    subst hn0
    exact kExit rfl _ (by simp [State.setReg, State.pc]) (hb2' _) (hI2 2 rfl) keep
  · intro hc
    rw [hcp'] at hc
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp at hc; omega⟩
    have ht := X25519Branch.b_back o (sz + 8 + 2) (by omega) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at ht
    refine ReachW.b hb0 (o + sz + 8 + 2) o _ (by simp [State.setReg, State.pc]) (by omega) hC2
      (by omega) ht (hPO.atE (by omega) (by omega)) ?_
    refine kBack j rfl _ (by simp [State.setReg, State.pc]) (hb2' _ |> fun h =>
      X25519ChainLoop.setReg15_body h _) (hI2 (j + 3) rfl) keep

/-- The loop from the head with `t = n + 3` to the exit with `t = 2`. -/
theorem loop_w {Q : State → Prop} : ∀ n, n + 3 ≤ 254 → ∀ (st : LadderState) (s : State),
    s.pc = c.base + BitVec.ofNat 32 oLadder → Body c m1 s → Inv c u ws s.mem (n + 3) st →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 oSwap → Body c m1 t →
      Inv c u ws t.mem 2 (steps (val ws) u st n) → KeepL c s t →
      ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q := by
  intro n
  induction n with
  | zero =>
    intro hn st s hpc hs hI k
    exact iter_w hAdd hSub hSel hv hcode hWr hPO hL hH hw hl hn hpc hs hI
      (fun _ t tp tb tI tk => k t tp tb (by rw [steps_zero]; exact tI) tk)
      fun j hj => absurd hj (by omega)
  | succ m ih =>
    intro hn st s hpc hs hI k
    refine iter_w hAdd hSub hSel hv hcode hWr hPO hL hH hw hl hn hpc hs hI (fun h => absurd h (by omega)) ?_
    intro j hj t tp tb tI tk
    obtain rfl : j = m := by omega
    refine ih (by omega) _ t tp tb tI fun v vp vb vI vk => k v vp vb ?_ (tk.trans vk)
    rw [steps_succ]; exact vI

end

end M0Crypto.Release.X25519LadderLoop
