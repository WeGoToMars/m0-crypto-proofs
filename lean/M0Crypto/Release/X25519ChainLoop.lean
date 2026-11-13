import M0Crypto.Release.X25519OpRun

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
The counted squaring loop of the inversion chain of `m0c_x25519` (plan `x25519-proofs.md`,
phase 9).

`sqrLoopAt o d n` is `setT (n - 1)`, then a loop of `opAt (o + 4) (sqr d d)`, `decT` and a
`bne` back to the squaring. `sqrLoop_w` runs it: slot `d` ends congruent to its old value
raised to `2 ^ (n - 1)`, `Body` is kept, and of the frame only slot `d` and the four bytes of
`LV_T` (which ends at zero) change. The proof is an induction on the counter (`loop_w`).

The macro lemmas `setT_runs` and `decT_runs` give the effect of the counter updates, and
`bc_back` the target of the backward `bne` from the code size of the loop body.
-/

namespace M0Crypto.Release.X25519ChainLoop
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Block (Runs AccOk accAll_cons accAll_nil)

/-! ## Memory frame facts -/

theorem write32_out {m : Mem} {a v y : Word} (h : ¬ Region a 4 y) : write32 m a v y = m y := by
  apply M0Crypto.Armv6M.write32_other
  intro k hk e
  apply h; subst e
  show (a + BitVec.ofNat 32 k - a).toNat < 4
  rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact hk

theorem read32_congr {m m' : Mem} {a : Word} {n : Nat} (hn : 4 ≤ n)
    (h : ∀ y, Region a n y → m y = m' y) : read32 m a = read32 m' a := by
  have hr : ∀ k : Nat, k < 4 → m (a + BitVec.ofNat 32 k) = m' (a + BitVec.ofNat 32 k) := fun k hk =>
    h _ (by show (a + BitVec.ofNat 32 k - a).toNat < n; rw [Frame.sub_ofNat_toNat _ _ (by omega)]; omega)
  have h0 := hr 0 (by omega)
  rw [BitVec.add_zero] at h0
  simp only [read32]
  rw [hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), h0]

theorem region_shift {a y : Word} {i n : Nat} (hi : i + n < 2 ^ 32)
    (h : Region (a + BitVec.ofNat 32 i) n y) : Region a (i + n) y := by
  show (y - a).toNat < i + n
  have h' : (y - (a + BitVec.ofNat 32 i)).toNat < n := h
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h' ⊢
  have := a.isLt; have := y.isLt
  omega

/-- A field value depends only on its 32 bytes. -/
theorem feVal_congr {m m' : Mem} {a : Word} (h : ∀ y, Region a 32 y → m y = m' y) :
    feVal m a = feVal m' a := by
  unfold feVal
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [read32_congr (n := 32 - 4 * i) (by omega) fun y hy => h y ?_]
  have := region_shift (by omega) hy
  rwa [show 4 * i + (32 - 4 * i) = 32 by omega] at this

/-! ## Counter updates -/

theorem lvT_off : (BitVec.ofNat 8 (lvT / 4)).toNat * 4 = lvT := by decide
theorem lvT_off' : lvT / 4 % 256 * 4 = lvT := by decide

theorem setWidth_ofNat8 {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 8 j).setWidth 32 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `setT j`: `LV_T` set to `j`, SP kept. -/
theorem setT_runs {Wr : Word → Prop} (u : State) {j : Nat} (hj : j < 256)
    (hal : (u.sp + BitVec.ofNat 32 lvT).toNat % 4 = 0)
    (hw : ∀ k < 4, Wr (u.sp + BitVec.ofNat 32 lvT + BitVec.ofNat 32 k)) :
    Runs (AccOk Wr) (setT j) u (fun t => t.regs 13 = u.regs 13 ∧
      t.mem = write32 u.mem (u.sp + BitVec.ofNat 32 lvT) (BitVec.ofNat 32 j)) := by
  refine ⟨accAll_cons ?_ (accAll_cons ?_ (accAll_nil _ _)), ?_⟩
  · simp [Instr.accesses]
  · simp only [Instr.accesses, List.mem_singleton, forall_eq]
    have e : ((Instr.movImm 0 (BitVec.ofNat 8 j)).next u).sp = u.sp := by
      simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, X25519Mem.toReg0]
    rw [e, lvT_off]
    exact ⟨X25519Block.aligned_word hal, fun _ => hw⟩
  · refine ⟨?_, ?_⟩
    · simp [setT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, X25519Mem.toReg0]
    · simp [setT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, State.reg,
        X25519Mem.toReg0, lvT_off, lvT_off', setWidth_ofNat8 hj]

theorem awc_dec (x : Word) : (M0Crypto.Armv6M.addWithCarry x 4294967294#32 true).1 = x - 1#32 := by
  rw [show (4294967294#32 : Word) = ~~~1#32 by decide]; exact Release.sub_flags x 1#32

/-- `decT`: `LV_T` decremented, Z set from the new value, SP kept. -/
theorem decT_runs {Wr : Word → Prop} (u : State)
    (hal : (u.sp + BitVec.ofNat 32 lvT).toNat % 4 = 0)
    (hw : ∀ k < 4, Wr (u.sp + BitVec.ofNat 32 lvT + BitVec.ofNat 32 k)) :
    Runs (AccOk Wr) decT u (fun t => t.regs 13 = u.regs 13 ∧
      t.mem = write32 u.mem (u.sp + BitVec.ofNat 32 lvT)
        (read32 u.mem (u.sp + BitVec.ofNat 32 lvT) - 1#32) ∧
      t.z = (read32 u.mem (u.sp + BitVec.ofNat 32 lvT) - 1#32 == 0)) := by
  refine ⟨accAll_cons ?_ (accAll_cons ?_ (accAll_cons ?_ (accAll_nil _ _))), ?_⟩
  · simp only [Instr.accesses, List.mem_singleton, forall_eq]
    rw [lvT_off]
    exact ⟨X25519Block.aligned_word hal, fun h => nomatch h⟩
  · simp [Instr.accesses]
  · simp only [Instr.accesses, List.mem_singleton, forall_eq]
    have e : ((Instr.subImm8 0 1).next ((Instr.ldrSp 0 (BitVec.ofNat 8 (lvT / 4))).next u)).sp = u.sp := by
      simp [Instr.next, Instr.exec, State.setReg, State.setNZCV, State.setNZ, State.sp, addFlags,
        X25519Mem.toReg0]
    rw [e, lvT_off]
    exact ⟨X25519Block.aligned_word hal, fun _ => hw⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [decT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZCV, State.setNZ, addFlags,
        X25519Mem.toReg0]
    · simp [decT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZCV, State.setNZ, addFlags,
        State.sp, State.reg, X25519Mem.toReg0, lvT_off, lvT_off', awc_dec]
    · simp [decT, execAll, Instr.next, Instr.exec, State.setReg, State.setNZCV, State.setNZ, addFlags,
        State.sp, State.reg, X25519Mem.toReg0, lvT_off, lvT_off', awc_dec]

/-! ## Backward branch -/

/-- Sign extension of every even backward `b<cond>` offset up to 256 bytes. -/
theorem se_back : ∀ k : Nat, k < 253 → k % 2 = 0 →
    ((BitVec.ofInt 8 (-((k : Int) + 4) / 2)) ++ 0#1).signExtend 32 = -(BitVec.ofNat 32 (k + 4)) := by
  decide +kernel

/-- Target of `bcTo cond (p + k) p`. -/
theorem bc_back (p k : Nat) (hk : k % 2 = 0) (hk2 : k < 253) :
    BitVec.ofNat 32 (p + k) + 4#32 +
      ((BitVec.ofInt 8 (((p : Int) - ((p + k : Nat) + 4)) / 2)) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 p := by
  rw [show ((p : Int) - ((p + k : Nat) + 4)) = -((k : Int) + 4) by omega, se_back k hk2 hk]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

/-! ## Frame regions -/

section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

theorem slot_iff {o n : Nat} (h : o + n ≤ SAVED + LFRAME) {y : Word} :
    Region (slotAt c o) n y ↔ (E c).toNat + o ≤ y.toNat ∧ y.toNat < (E c).toNat + o + n := by
  have e := E_add hv (d := o) (by simp only [SAVED, LFRAME] at h ⊢; omega)
  have := E_toNat hv; have := c.sp0.isLt; have := hv.spLo
  simp only [SAVED, LFRAME, X25519.stackBytes] at *
  rw [region_iff (by rw [e]; omega), e]

theorem fp_iff {n : Nat} (h : n ≤ X25519.stackBytes) {y : Word} :
    Region c.fp n y ↔ c.fp.toNat ≤ y.toNat ∧ y.toNat < c.fp.toNat + n := by
  have := fp_toNat hv; have := c.sp0.isLt; have := hv.spLo
  exact region_iff (by omega)

/-- Facts on the bytes of `LV_T`. -/
theorem lvT_facts {d : Nat} (hd : SlotOk d) :
    (slotAt c lvT).toNat % 4 = 0 ∧
    (∀ k < 4, Region c.fp X25519.stackBytes (slotAt c lvT + BitVec.ofNat 32 k)) ∧
    (∀ y, Region (slotAt c lvT) 4 y → Region c.fp X25519.wipeBytes y ∧ Region (E c) LFRAME y ∧
      ¬ Region (slotAt c d) 32 y) := by
  have eE := E_toNat hv; have eF := fp_toNat hv; have := hv.sp4; have := hv.spLo
  have e := E_add hv (d := lvT) (by decide)
  obtain ⟨hd1, hd2⟩ := hd
  have hl : (E c + BitVec.ofNat 32 lvT).toNat + 4 < 2 ^ 32 := by
    rw [e]; have := c.sp0.isLt; simp only [SAVED, LFRAME, lvT] at *; omega
  simp only [SAVED, LFRAME, lvT, X25519.stackBytes, X25519.wipeBytes, slotAt] at *
  refine ⟨by rw [e]; omega, fun k hk => ?_, fun y hy => ?_⟩
  · rw [fp_iff hv (by decide), Frame.toNat_add_ofNat _ _ (by omega), e]; omega
  · rw [slot_iff hv (by decide)] at hy
    refine ⟨(fp_iff hv (by decide)).mpr (by omega), ?_, ?_⟩
    · have := (slot_iff hv (o := 0) (n := LFRAME) (by decide) (y := y)).mpr (by simp only [LFRAME]; omega)
      rwa [show slotAt c 0 = E c by simp [slotAt]] at this
    · rw [slot_iff hv (by simp only [SAVED, LFRAME]; omega)]; omega

end

/-! ## The loop -/

/-- Frame bytes kept by a run that writes only slot `d` and `LV_T`. -/
def KeepDT (c : X25519.Ctx) (d : Nat) (s t : State) : Prop :=
  ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c d) 32 y → ¬ Region (slotAt c lvT) 4 y →
    t.mem y = s.mem y

theorem sq_pow (x : Int) (j : Nat) : (x * x) ^ (2 ^ j) = x ^ (2 ^ (j + 1)) := by
  rw [X25519Congr.mul_self_eq_sq, ← Int.pow_mul, Nat.pow_succ, Nat.mul_comm]

theorem ofNat_dec {j : Nat} (_hj : j + 1 < 256) : BitVec.ofNat 32 (j + 1) - 1#32 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_eq_zero {j : Nat} (hj : j < 256) : (BitVec.ofNat 32 j == (0 : Word)) = decide (j = 0) := by
  by_cases h : j = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 j ≠ (0 : Word) := fun e => h (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    simpa [h] using this

theorem setReg15_body {c : X25519.Ctx} {m1 : Mem} {u : State} (h : Body c m1 u) (x : Word) :
    Body c m1 (u.setReg 15 x) := ⟨by simp [State.setReg, h.sp], h.keep⟩

theorem sqr_ok {d : Nat} (hd : SlotOk d) : Op.ok (sqr d d) = true := by
  simp [Op.ok, sqr, hd]

theorem sqr_size (p d : Nat) : seqSize (opAt p (sqr d d)) ≤ 10 := by
  have := opPre_size d d none
  simp only [opAt, sqr, seqSize_append] at *
  simp [seqSize, blTo, Instr.size] at *
  omega

section
variable {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
include hv hcode hWr hPO

/-- The loop from its head at `p` with `j ≥ 1` in `LV_T`: `j` squarings of slot `d`. -/
theorem loop_w {Q : State → Prop} {p d : Nat} (hd : SlotOk d)
    (hseq : seqAt B p (opAt p (sqr d d) ++ decT ++
      [bcTo 1 (p + seqSize (opAt p (sqr d d)) + 6) p]) = true)
    (hp : p % 2 = 0) (hlo : lo ≤ p)
    (hend : p + seqSize (opAt p (sqr d d)) + 6 + 2 ≤ hi) :
    ∀ j, 1 ≤ j → j < 256 → ∀ u : State, u.pc = c.base + BitVec.ofNat 32 p → Body c m1 u →
      read32 u.mem (slotAt c lvT) = BitVec.ofNat 32 j →
      (∀ t, t.pc = c.base + BitVec.ofNat 32 (p + seqSize (opAt p (sqr d d)) + 6 + 2) → Body c m1 t →
        ModP (feVal t.mem (slotAt c d)) ((feVal u.mem (slotAt c d) : Int) ^ (2 ^ j)) →
        KeepDT c d u t → ReachW c.base Pc Wr t Q) →
      ReachW c.base Pc Wr u Q
  | 0, h, _, _, _, _, _, _ => absurd h (by decide)
  | j + 1, _, hj, u, hpc, hu, hT, k => by
    have ih := loop_w (Q := Q) hd hseq hp hlo hend j
    have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
    have := hPO.hile
    have hseq' := hseq
    rw [List.append_assoc, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true] at hseq'
    obtain ⟨hB1, hB2, hB3⟩ := hseq'
    have h6 : seqSize decT = 6 := rfl
    rw [h6] at hB3
    have hn := seqSize_even (opAt p (sqr d d))
    have hn' := sqr_size p d
    generalize hn1 : seqSize (opAt p (sqr d d)) = n1 at hn hn' hB2 hB3 hend k
    obtain ⟨al, wr, lv⟩ := lvT_facts hv hd
    refine sqr_opW hv hcode hWr hPO hB1 hp hlo
      (by show p + seqSize (opAt p (sqr d d)) ≤ _; rw [hn1]; omega) hpc hu (sqr_ok hd) (fun h => nomatch h) ?_
    intro u1 u1pc e1
    have v1 : ModP (feVal u1.mem (slotAt c d))
        ((feVal u.mem (slotAt c d) : Int) * (feVal u.mem (slotAt c d) : Int)) := e1.val
    have u1sp : u1.sp = E c := e1.body.sp
    change u1.pc = c.base + BitVec.ofNat 32 (p + seqSize (opAt p (sqr d d))) at u1pc
    rw [hn1] at u1pc
    refine X25519Block.ReachW.blockRuns hb0 decT (p + n1) u1pc (by omega) hB2 (by decide)
      (decT_runs u1 (by rw [u1sp]; exact al) (fun q hq => hWr _ (by rw [u1sp]; exact wr q hq)))
      (hPO.inE (by omega) (by rw [h6]; omega)) ?_
    rintro u2 u2pc ⟨u2sp, u2mem, u2z⟩
    have c1 : read32 u1.mem (E c + BitVec.ofNat 32 lvT) = BitVec.ofNat 32 (j + 1) := by
      rw [← hT]
      exact read32_congr (n := 4) (Nat.le_refl _) fun y hy => e1.keep y (lv y hy).2.1 (lv y hy).2.2
    rw [u1sp, c1, ofNat_dec hj] at u2mem u2z
    rw [ofNat_eq_zero (by omega)] at u2z
    rw [h6] at u2pc
    have k2 : ∀ y, ¬ Region (slotAt c lvT) 4 y → u2.mem y = u1.mem y := fun y hy => by
      rw [u2mem]; exact write32_out hy
    have b2 : ∀ x, Body c m1 (u2.setReg 15 x) := fun x => setReg15_body
      ⟨by rw [u2sp]; exact e1.body.sp,
        fun y hy => by rw [k2 y fun h => hy (lv y h).1]; exact e1.body.keep y hy⟩ x
    have f2 : feVal u2.mem (slotAt c d) = feVal u1.mem (slotAt c d) :=
      feVal_congr fun y hy => k2 y fun h => (lv y h).2.2 hy
    have kk : ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c d) 32 y → ¬ Region (slotAt c lvT) 4 y →
        u2.mem y = u.mem y := fun y h1 h2 h3 => by rw [k2 y h3]; exact e1.keep y h1 h2
    have hi : instrAt B (p + n1 + 6) = some (bcTo 1 (p + n1 + 6) p) := by
      simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hB3; exact hB3.1
    have ht := bc_back p (n1 + 6) (by omega) (by omega)
    rw [← Nat.add_assoc] at ht
    refine ReachW.bcond hb0 (p + n1 + 6) p 1 _ u2pc (by omega) hi (by omega) ht (hPO.atE (by omega) (by omega)) ?_ ?_
    · intro hc
      simp only [condPassed, u2z] at hc
      refine ih (by simp at hc; omega) (by omega) _ (by simp [State.setReg, State.pc]) (b2 _)
        (by show read32 u2.mem _ = _; rw [u2mem]; exact M0Crypto.Armv6M.read32_write32_same _ _ _) ?_
      intro t tpc tb tv tk
      refine k t (by rw [tpc, hn1]) tb ?_ fun y h1 h2 h3 => ?_
      · refine tv.trans ((ModP.pow ?_ _).trans (ModP.of_eq (sq_pow _ j)))
        show ModP (feVal u2.mem (slotAt c d) : Int) _
        rw [f2]; exact v1
      · rw [tk y h1 h2 h3]; exact kk y h1 h2 h3
    · intro hc
      simp only [condPassed, u2z] at hc
      have hj0 : j = 0 := by simp at hc; omega
      subst hj0
      refine k _ (by simp [State.setReg, State.pc]) (b2 _) ?_ kk
      show ModP (feVal u2.mem (slotAt c d) : Int) _
      rw [f2]; exact v1.trans (ModP.of_eq (by rw [← sq_pow _ 0, Nat.pow_zero, Int.pow_one]))
/-- `sqrLoopAt o d n` from `o`: `n - 1` squarings of slot `d` in place. -/
theorem sqrLoop_w {Q : State → Prop} {s : State} {o d n : Nat} (hd : SlotOk d) (hn : 2 ≤ n)
    (hn' : n ≤ 256) (hseq : seqAt B o (sqrLoopAt o d n) = true) (ho : o % 2 = 0)
    (hlo : lo ≤ o) (hend : o + seqSize (sqrLoopAt o d n) ≤ hi)
    (hpc : s.pc = c.base + BitVec.ofNat 32 o) (hs : Body c m1 s)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (sqrLoopAt o d n)) → Body c m1 t →
      ModP (feVal t.mem (slotAt c d)) ((feVal s.mem (slotAt c d) : Int) ^ (2 ^ (n - 1))) →
      KeepDT c d s t → ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have e : sqrLoopAt o d n = setT (n - 1) ++ (opAt (o + 4) (sqr d d) ++ decT ++
      [bcTo 1 (o + 4 + seqSize (opAt (o + 4) (sqr d d)) + 6) (o + 4)]) := by
    simp only [sqrLoopAt, List.append_assoc]
  have h4 : seqSize (setT (n - 1)) = 4 := rfl
  have h6 : seqSize decT = 6 := rfl
  have hsz : seqSize (sqrLoopAt o d n) = 4 + seqSize (opAt (o + 4) (sqr d d)) + 6 + 2 := by
    rw [e]; simp only [seqSize_append, h4, h6]; simp [seqSize, bcTo, Instr.size]; omega
  rw [e, seqAt_append, Bool.and_eq_true, h4] at hseq
  rw [hsz] at hend k
  have hn1 := sqr_size (o + 4) d
  obtain ⟨al, wr, lv⟩ := lvT_facts hv hd
  have ssp : s.sp = E c := hs.sp
  refine X25519Block.ReachW.blockRuns hb0 (setT (n - 1)) o hpc ho hseq.1 rfl
    (setT_runs s (by omega) (by rw [ssp]; exact al) (fun q hq => hWr _ (by rw [ssp]; exact wr q hq)))
    (hPO.inE (by omega) (by rw [h4]; omega)) ?_
  rintro u upc ⟨usp, umem⟩
  rw [ssp] at umem
  have k1 : ∀ y, ¬ Region (slotAt c lvT) 4 y → u.mem y = s.mem y := fun y hy => by
    rw [umem]; exact write32_out hy
  have f1 : feVal u.mem (slotAt c d) = feVal s.mem (slotAt c d) :=
    feVal_congr fun y hy => k1 y fun h => (lv y h).2.2 hy
  refine loop_w hv hcode hWr hPO hd hseq.2 (by omega) (by omega) (by omega) (n - 1) (by omega) (by omega) u
    (by rw [upc, h4]) ⟨by rw [usp]; exact hs.sp, fun y hy => by
      rw [k1 y fun h => hy (lv y h).1]; exact hs.keep y hy⟩
    (by rw [umem]; exact M0Crypto.Armv6M.read32_write32_same _ _ _) ?_
  intro t tpc tb tv tk
  refine k t (by rw [tpc]; congr 2) tb (by rw [← f1]; exact tv) fun y h1 h2 h3 => ?_
  rw [tk y h1 h2 h3]; exact k1 y h3

end

end M0Crypto.Release.X25519ChainLoop
