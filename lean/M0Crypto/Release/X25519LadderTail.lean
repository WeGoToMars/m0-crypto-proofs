import M0Crypto.Release.X25519LadderLoop
import M0Crypto.Release.X25519Branch

set_option linter.unusedSectionVars false

/-!
The ladder tail of `m0c_x25519` (`swapAt`, `dblAt`).

`swap_w` runs the final conditional swap with mask `-swap` and sets `t = 3`. `dbl_loop` runs the
doubling loop: with `t = j + 1` in `LV_T` it applies `dbl` `j + 1` times (`dblN`) to the slots
`X2, Z2` and leaves at the inversion chain with `t = 0`.
-/

namespace M0Crypto.Release.X25519LadderTail
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
open M0Crypto.Release.X25519Block (Runs AccOk accAll_cons accAll_nil)
open M0Crypto.Release.X25519Ladder (dbl dbl3)

/-! ## Mask block -/

theorem lvSwap_off : (BitVec.ofNat 8 (lvSwap / 4)).toNat * 4 = lvSwap := by decide

/-- `ldr r7, [sp, #LV_SWAP]; rsbs r7, r7`. -/
theorem mask_runs {Wr : Word → Prop} (u : State)
    (hal : (u.sp + BitVec.ofNat 32 lvSwap).toNat % 4 = 0) :
    Runs (AccOk Wr) [.ldrSp 7 (BitVec.ofNat 8 (lvSwap / 4)), .dp .rsbs 7 7] u (fun t =>
      t.regs 13 = u.regs 13 ∧ t.mem = u.mem ∧
      t.regs 7 = 0#32 - read32 u.mem (u.sp + BitVec.ofNat 32 lvSwap)) := by
  refine ⟨accAll_cons ?_ (accAll_cons ?_ (accAll_nil _ _)), ?_⟩
  · simp only [Instr.accesses, List.mem_singleton, forall_eq]
    rw [lvSwap_off]
    exact ⟨X25519Block.aligned_word hal, fun h => nomatch h⟩
  · simp [Instr.accesses]
  · refine ⟨?_, ?_, ?_⟩
    · simp [execAll, X25519LadderBit.regs_rsbs, X25519Mem.regs_ldrSp, State.reg,
        X25519Mem.toReg7]
    · simp [execAll, X25519LadderBit.mem_dp, X25519Mem.mem_ldrSp]
    · simp [execAll, X25519LadderBit.regs_rsbs, X25519Mem.regs_ldrSp, X25519LadderBit.rsbs_val,
        X25519LadderBit.mem_dp, X25519Mem.mem_ldrSp, X25519Mem.c_ldrSp, State.reg, State.sp,
        lvSwap, X25519Mem.toReg7]

/-! ## Final swap -/

def swapSels : List Op := [sel sX2 sX2 sX3, sel sZ2 sZ2 sZ3]

/-- Frame bytes outside the slots `X2..D` and `LV_T`. -/
def KeepT (c : X25519.Ctx) (s t : State) : Prop :=
  ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sX2) (sK - sX2) y →
    ¬ Region (slotAt c lvT) 4 y → t.mem y = s.mem y

theorem KeepT.trans {c : X25519.Ctx} {s t v : State} (h1 : KeepT c s t) (h2 : KeepT c t v) :
    KeepT c s v := fun y a b d => (h2 y a b d).trans (h1 y a b d)

section
variable {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
  (hL : lo ≤ oLadder) (hH : oStore ≤ hi)
include hv hcode hWr hPO hL hH

/-- `LV_T` set to `j` from `u`: the slots keep their values. -/
theorem setT_env {u t : State} (hsp : u.sp = E c) {j : Nat}
    (hm : t.mem = write32 u.mem (u.sp + BitVec.ofNat 32 lvT) (BitVec.ofNat 32 j)) :
    (∀ e, SlotOk e → env c t.mem e = env c u.mem e) ∧ KeepT c u t ∧
      tWord c t.mem = BitVec.ofNat 32 j ∧
      (∀ y, ¬ Region (slotAt c lvT) 4 y → t.mem y = u.mem y) := by
  rw [hsp] at hm
  have k : ∀ y, ¬ Region (slotAt c lvT) 4 y → t.mem y = u.mem y := fun y hy => by
    rw [hm]; exact X25519LadderBit.write32_out hy
  refine ⟨fun e he => congrArg (fun n : Nat => (n : Int)) (feVal_congr fun y hy => k y
    (band_disj hv (by have := he.1; have := he.2; simp only [LFRAME, lvT] at *; omega) he.2
      (by decide) hy)), fun y _ _ h3 => k y h3, ?_, k⟩
  show read32 t.mem (slotAt c lvT) = _
  rw [hm]; exact M0Crypto.Armv6M.read32_write32_same _ _ _

theorem swap_w (hSel : OpW .sel) {s : State} {Q : State → Prop}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oSwap) (hs : Body c m1 s)
    (hsw : (swWord c s.mem).toNat ≤ 1)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 oDbl → Body c m1 t →
      env c t.mem sX2 = (if (swWord c s.mem).toNat = 1 then env c s.mem sX3 else env c s.mem sX2) →
      env c t.mem sZ2 = (if (swWord c s.mem).toNat = 1 then env c s.mem sZ3 else env c s.mem sZ2) →
      tWord c t.mem = BitVec.ofNat 32 3 → KeepT c s t →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have hseq := X25519EntrySeg.swap_seg
  have hlo : oLadder ≤ oSwap := by decide +kernel
  have hev : oSwap % 2 = 0 := by decide +kernel
  have hDS : oDbl ≤ oStore := by decide +kernel
  have h4 : seqSize [Instr.ldrSp 7 (BitVec.ofNat 8 (lvSwap / 4)), .dp .rsbs 7 7] = 4 := rfl
  have hD : oDbl = oSwap + 4 + seqSize (opsAt (oSwap + 4) swapSels) + 4 := by
    show oSwap + seqSize (swapAt oSwap) = _
    simp only [swapAt, swapSels, seqSize_append, h4, show seqSize (setT 3) = 4 from rfl]; omega
  have e : swapAt oSwap = [.ldrSp 7 (BitVec.ofNat 8 (lvSwap / 4)), .dp .rsbs 7 7] ++
      (opsAt (oSwap + 4) swapSels ++ setT 3) := by
    simp only [swapAt, List.append_assoc]; rfl
  rw [e, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true, h4] at hseq
  obtain ⟨h1, h2, h3⟩ := hseq
  have hn := X25519OpRun.seqSize_even (opsAt (oSwap + 4) swapSels)
  rw [hD] at k
  generalize oSwap = o at hpc hlo hev hn h1 h2 h3 k hD
  have ssp : s.sp = E c := hs.sp
  obtain ⟨al, wr, lv⟩ := X25519ChainLoop.lvT_facts hv (d := sX2) (by decide)
  have alS : (E c + BitVec.ofNat 32 lvSwap).toNat % 4 = 0 := by
    have := X25519Op.E_add hv (d := lvSwap) (by decide)
    have := X25519ChainLoop.lvT_facts hv (d := sX2) (by decide) |>.1
    simp only [slotAt] at this
    rw [X25519Op.E_add hv (by decide)] at this
    rw [X25519Op.E_add hv (by decide)]; simp only [lvT, lvSwap] at *; omega
  -- mask
  refine X25519Block.ReachW.blockRuns hb0 _ o hpc hev h1 (by decide)
    (mask_runs (Wr := Wr) s (by rw [ssp]; exact alS))
    (hPO.inE (by omega) (by rw [h4]; omega)) ?_
  rintro u1 pc1 ⟨u13, um, u7⟩
  have hb1 : Body c m1 u1 := ⟨by rw [u13]; exact hs.sp, fun y hy => by rw [um]; exact hs.keep y hy⟩
  have hr7 : u1.regs 7 = 0#32 - swWord c s.mem := by rw [u7, ssp]; rfl
  -- selects
  rw [h4] at pc1
  refine selsAt_w hv hcode hWr hPO hSel swapSels (o + 4) u1 (by decide) (by decide) h2 (by omega)
    (by omega) (by omega) pc1 hb1 (fun _ => by rw [hr7]; exact mask_ok hsw) ?_
  intro u2 pc2 E2 r72
  have hb2 := E2.body hb1
  have u2sp : u2.sp = E c := hb2.sp
  -- t = 3
  have hS3 : seqSize (setT 3) = 4 := rfl
  refine X25519Block.ReachW.blockRuns hb0 (setT 3) _ pc2 (by omega) h3 (by decide)
    (X25519ChainLoop.setT_runs u2 (j := 3) (by decide) (by rw [u2sp]; exact al)
      (fun q hq => hWr _ (by rw [u2sp]; exact wr q hq)))
    (hPO.inE (by omega) (by rw [hS3]; omega)) ?_
  rintro t pc3 ⟨t13, tm⟩
  obtain ⟨envT, keepT, twT, kT⟩ := setT_env hv hcode hWr hPO hL hH u2sp tm
  have hbt : Body c m1 t := ⟨by rw [t13]; exact hb2.sp, fun y hy => by
    rw [kT y fun h => hy (lv y h).1]; exact hb2.keep y hy⟩
  have hK2 := opsEff_keep hv (lo := sX2) (hi := sK) (by decide) E2 (by decide)
  -- values
  have V := (selsEff_val hv E2 (by decide) (by decide)).1
  simp only [OpsVal, swapSels, Op.step, sel, Fn.rel, Option.getD_some] at V
  obtain ⟨σ1, ⟨q1, j1⟩, σ2, ⟨q2, j2⟩, e2⟩ := V
  subst e2
  rw [hr7, mask_if hsw] at q1 q2
  have em : ∀ e, env c u1.mem e = env c s.mem e := fun e => by rw [um]
  rw [hS3] at pc3
  refine k t pc3 hbt ?_ ?_ twT (fun y h1 h2 h3 => ?_)
  · rw [envT _ (by decide)]
    simp (disch := decide) only [j2, em] at q1 q2 ⊢
    exact q1
  · rw [envT _ (by decide)]
    simp (disch := decide) only [j1, em] at q2 ⊢
    exact q2
  · rw [keepT y h1 h2 h3, hK2 y h1 h2, um]

/-! ## Doublings -/

/-- `n` doublings. -/
def dblN : Nat → Int → Int → Int × Int
  | 0, x, z => (x, z)
  | n + 1, x, z => dblN n (dbl x z).1 (dbl x z).2

theorem dblN_three (x z : Int) : dblN 3 x z = dbl3 x z := rfl

variable (hAdd : OpW .add) (hSub : OpW .sub)
include hAdd hSub

/-- One iteration of the doubling loop from its head with `t = j + 1`. -/
theorem dbl_iter {Q : State → Prop} {j : Nat} (hj : j + 1 ≤ 3) {x z : Int} {s : State}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oDbl) (hs : Body c m1 s)
    (ht : tWord c s.mem = BitVec.ofNat 32 (j + 1))
    (hx : ModP (env c s.mem sX2) x) (hz : ModP (env c s.mem sZ2) z)
    (kExit : j = 0 → ∀ t, t.pc = c.base + BitVec.ofNat 32 oChain → Body c m1 t →
      ModP (env c t.mem sX2) (dbl x z).1 → ModP (env c t.mem sZ2) (dbl x z).2 →
      tWord c t.mem = 0#32 → KeepT c s t →
      ReachW c.base Pc Wr t Q)
    (kBack : ∀ i, j = i + 1 → ∀ t, t.pc = c.base + BitVec.ofNat 32 oDbl → Body c m1 t →
      ModP (env c t.mem sX2) (dbl x z).1 → ModP (env c t.mem sZ2) (dbl x z).2 →
      tWord c t.mem = BitVec.ofNat 32 (i + 1) → KeepT c s t →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have hseq := X25519EntrySeg.dbl_seg
  have hlo : oLadder ≤ oDbl := by decide +kernel
  have hev : oDbl % 2 = 0 := by decide +kernel
  have hCS : oChain ≤ oStore := by decide +kernel
  have hn' : seqSize (opsAt oDbl dblOps) + 8 < 2045 := by decide +kernel
  have hn := X25519OpRun.seqSize_even (opsAt oDbl dblOps)
  have h6 : seqSize decT = 6 := rfl
  have hC : oChain = oDbl + seqSize (opsAt oDbl dblOps) + 6 + 4 := by
    show oDbl + seqSize (dblAt oDbl) = _
    have h4 : ∀ a b d, seqSize [bcTo 0x0 a b, bTo d oDbl] = 4 := fun _ _ _ => rfl
    simp only [dblAt, seqSize_append, h6, h4]; omega
  have e : dblAt oDbl = opsAt oDbl dblOps ++ (decT ++
      [bcTo 0x0 (oDbl + seqSize (opsAt oDbl dblOps) + 6) (oDbl + seqSize (opsAt oDbl dblOps) + 6 + 4),
       bTo (oDbl + seqSize (opsAt oDbl dblOps) + 6 + 2) oDbl]) := by
    simp only [dblAt, List.append_assoc]
  rw [e, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true, h6] at hseq
  obtain ⟨h1, h2, h3⟩ := hseq
  simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h3
  rw [hC] at kExit
  generalize oDbl = o at hpc hlo hev hn hn' h1 h2 h3 hC kExit kBack
  generalize hN : seqSize (opsAt o dblOps) = n at hn hn' h2 h3 hC kExit
  have hC1 : instrAt B (o + n + 6) = some (bcTo 0x0 (o + n + 6) (o + n + 6 + 4)) := h3.1.1
  have hC2 : instrAt B (o + n + 6 + 2) = some (bTo (o + n + 6 + 2) o) := by
    have h := h3.2.1
    simp only [bcTo, Instr.size] at h
    exact h
  have hW := nonsel_w hAdd hSub
  refine opsAt_w hv hcode hWr hPO dblOps o s
    (fun p hp => ⟨hW _ (nonsel_of (by decide) p hp), nonsel_of (by decide) p hp⟩) (by decide)
    h1 hev (by omega) (by omega) hpc hs ?_
  intro u1 pc1 E1
  rw [hN] at pc1
  have hb1 := E1.body hs
  have u1sp : u1.sp = E c := hb1.sp
  obtain ⟨al, wr, lv⟩ := X25519ChainLoop.lvT_facts hv (d := sX2) (by decide)
  have hK1 := opsEff_keep hv (lo := sX2) (hi := sK) (by decide) E1 (by decide)
  have hT1 : read32 u1.mem (u1.sp + BitVec.ofNat 32 lvT) = BitVec.ofNat 32 (j + 1) := by
    rw [u1sp, ← ht]
    exact read32_congr' fun y hy => hK1 y (band_frame hv (by decide) hy)
      (band_disj hv (by decide) (by decide) (by decide) hy)
  refine X25519Block.ReachW.blockRuns hb0 decT _ pc1 (by omega) h2 (by decide)
    (X25519ChainLoop.decT_runs u1 (by rw [u1sp]; exact al)
      (fun q hq => hWr _ (by rw [u1sp]; exact wr q hq)))
    (hPO.inE (by omega) (by rw [h6]; omega)) ?_
  rintro u2 pc2 ⟨u13, um2, uz⟩
  rw [h6] at pc2
  rw [hT1, X25519ChainLoop.ofNat_dec (by omega)] at um2 uz
  rw [X25519ChainLoop.ofNat_eq_zero (by omega)] at uz
  obtain ⟨envT, keepT, twT, kT⟩ := setT_env hv hcode hWr hPO hL hH u1sp um2
  have hb2 : Body c m1 u2 := ⟨by rw [u13]; exact hb1.sp, fun y hy => by
    rw [kT y fun h => hy (lv y h).1]; exact hb1.keep y hy⟩
  have hb2' : ∀ x, Body c m1 (u2.setReg 15 x) := fun x => X25519ChainLoop.setReg15_body hb2 x
  have keep : KeepT c s u2 := fun y h1 h2 h3 => by rw [keepT y h1 h2 h3, hK1 y h1 h2]
  -- values
  have V := opsEff_val hv 0#32 E1 (by decide) (nonsel_of (by decide))
  simp only [OpsVal, dblOps, Op.step, add, sub, mul, sqr, mulc, Fn.rel, Option.getD_some,
    Option.getD_none] at V
  obtain ⟨τ1, ⟨r1, k1⟩, τ2, ⟨r2, k2⟩, τ3, ⟨r3, k3⟩, τ4, ⟨r4, k4⟩, τ5, ⟨r5, k5⟩,
    τ6, ⟨r6, k6⟩, τ7, ⟨r7, k7⟩, τ8, ⟨r8, k8⟩, e1⟩ := V
  subst e1
  simp (disch := decide) only [k1, k2, k3, k4, k5, k6, k7, k8] at r1 r2 r3 r4 r5 r6 r7 r8
  have hd := X25519Ladder.dbl_congr hx hz r1 r2 r3 r4 r5 r6 r7 r8
  have vx : ModP (env c u2.mem sX2) (dbl x z).1 := by
    rw [envT _ (by decide)]
    simp (disch := decide) only [k6, k7, k8]
    exact hd.1
  have vz : ModP (env c u2.mem sZ2) (dbl x z).2 := by
    rw [envT _ (by decide)]; exact hd.2
  -- exit test
  refine ReachW.bcond hb0 (o + n + 6) (o + n + 6 + 4) 0 _ pc2 (by omega) hC1 (by omega)
    (X25519Branch.bc_fwd4 _) (hPO.atE (by omega) (by omega)) ?_ ?_
  · intro hc
    simp only [condPassed, uz] at hc
    have hj0 : j = 0 := by simpa using hc
    subst hj0
    exact kExit rfl _ (by simp [State.setReg, State.pc]) (hb2' _) vx vz twT keep
  · intro hc
    simp only [condPassed, uz] at hc
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hc; omega⟩
    have ht := X25519Branch.b_back o (n + 6 + 2) (by omega) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at ht
    refine ReachW.b hb0 (o + n + 6 + 2) o _ (by simp [State.setReg, State.pc]) (by omega) hC2 (by omega) ht
      (hPO.atE (by omega) (by omega)) ?_
    exact kBack i rfl _ (by simp [State.setReg, State.pc])
      (X25519ChainLoop.setReg15_body (hb2' _) _) vx vz twT keep

/-- The doubling loop from its head with `t = j + 1`: `j + 1` doublings of `X2, Z2`. -/
theorem dbl_loop {Q : State → Prop} : ∀ j, j + 1 ≤ 3 → ∀ (x z : Int) (s : State),
    s.pc = c.base + BitVec.ofNat 32 oDbl → Body c m1 s → tWord c s.mem = BitVec.ofNat 32 (j + 1) →
    ModP (env c s.mem sX2) x → ModP (env c s.mem sZ2) z →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 oChain → Body c m1 t →
      ModP (env c t.mem sX2) (dblN (j + 1) x z).1 → ModP (env c t.mem sZ2) (dblN (j + 1) x z).2 →
      tWord c t.mem = 0#32 → KeepT c s t →
      ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q := by
  intro j
  induction j with
  | zero =>
    intro hj x z s hpc hs ht hx hz k
    exact dbl_iter hv hcode hWr hPO hL hH hAdd hSub hj hpc hs ht hx hz
      (fun _ t tp tb tx tz tt tk => k t tp tb tx tz tt tk) fun i hi => absurd hi (by omega)
  | succ i ih =>
    intro hj x z s hpc hs ht hx hz k
    refine dbl_iter hv hcode hWr hPO hL hH hAdd hSub hj hpc hs ht hx hz (fun h => absurd h (by omega)) ?_
    intro i' hi t tp tb tx tz tt tk
    obtain rfl : i' = i := by omega
    exact ih (by omega) _ _ t tp tb tt tx tz fun v vp vb vx vz vt vk =>
      k v vp vb vx vz vt (tk.trans vk)

end

end M0Crypto.Release.X25519LadderTail
