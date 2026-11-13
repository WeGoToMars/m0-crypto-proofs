import M0Crypto.Release.X25519OutStore
import M0Crypto.Release.X25519OutWipe
import M0Crypto.Release.X25519OutEpi
import M0Crypto.Release.X25519ReadBlock

set_option linter.unusedSimpArgs false

/-!
The tail of `m0c_x25519` from `oStore` to the return:
`storeOut`, `wipe` and `epilogue` at their offsets in the entry.

`tail_at` takes the three `seqAt` facts from `entry_at` by `seqAt_append` (no offset is written
down). `Saved c m` is the save area left by the prologue (word `i` above `E c + LFRAME` holds
`savedReg i`). `tail_w` runs the three segments: from `pc = base + oStore` with SP at `E c`,
`r0` at slot `X2` and `c.out` in `LV_OUT`, the call returns to `c.ret` with the register fields
of `X25519.Result`, the 32 bytes of `out` holding the little-endian bytes of `feVal` of slot
`X2`, the `wipeBytes` from `c.fp` zero, and no other byte changed. Writes stay in `WrOk c`.
-/

namespace M0Crypto.Release.X25519OutAt
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW ReachS RegionWrites InRegion Region B)
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OutEpi (savedReg)

/-! ## Code facts -/

theorem tail_at : seqAt B oStore storeOut = true ∧ seqAt B oWipe wipe = true ∧
    seqAt B oEpi epilogue = true := by
  have h := entry_at
  simp only [entryList, List.append_assoc, seqAt_append, Bool.and_eq_true] at h
  have e1 : Artifacts.Release.x25519 + seqSize prologue = oLadder := rfl
  have e2 : oLadder + seqSize (ladderAt oLadder) = oSwap := rfl
  have e3 : oSwap + seqSize (swapAt oSwap) = oDbl := rfl
  have e4 : oDbl + seqSize (dblAt oDbl) = oChain := rfl
  have e5 : oChain + seqSize (chainAt oChain X25519Chain.invChain) = oFinish := rfl
  have e6 : oFinish + seqSize (finishAt oFinish) = oStore := rfl
  have e7 : oStore + seqSize storeOut = oWipe := rfl
  have e8 : oWipe + seqSize wipe = oEpi := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8] at h
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem oEpi_end : oEpi + seqSize epilogue = Artifacts.Release.size := by
  have h := entry_size
  simp only [entryList, seqSize_append] at h
  have e1 : oLadder = Artifacts.Release.x25519 + seqSize prologue := rfl
  have e2 : oSwap = oLadder + seqSize (ladderAt oLadder) := rfl
  have e3 : oDbl = oSwap + seqSize (swapAt oSwap) := rfl
  have e4 : oChain = oDbl + seqSize (dblAt oDbl) := rfl
  have e5 : oFinish = oChain + seqSize (chainAt oChain X25519Chain.invChain) := rfl
  have e6 : oStore = oFinish + seqSize (finishAt oFinish) := rfl
  have e7 : oWipe = oStore + seqSize storeOut := rfl
  have e8 : oEpi = oWipe + seqSize wipe := rfl
  omega

theorem oStore_even : oStore % 2 = 0 := by
  have h0 : Artifacts.Release.x25519 % 2 = 0 := by decide
  have h1 : oLadder % 2 = 0 := by have := X25519OpRun.seqSize_even prologue; unfold oLadder; omega
  have h2 : oSwap % 2 = 0 := by have := X25519OpRun.seqSize_even (ladderAt oLadder); unfold oSwap; omega
  have h3 : oDbl % 2 = 0 := by have := X25519OpRun.seqSize_even (swapAt oSwap); unfold oDbl; omega
  have h4 : oChain % 2 = 0 := by have := X25519OpRun.seqSize_even (dblAt oDbl); unfold oChain; omega
  have h5 : oFinish % 2 = 0 := by
    have := X25519OpRun.seqSize_even (chainAt oChain X25519Chain.invChain); unfold oFinish; omega
  have := X25519OpRun.seqSize_even (finishAt oFinish); unfold oStore; omega

theorem oWipe_eq : oWipe = oStore + seqSize storeOut := rfl
theorem oEpi_eq : oEpi = oWipe + seqSize wipe := rfl

/-- Code offsets below the artifact end are in the executed region. -/
theorem inRegion_entry (base : Word) {o n : Nat} (h : o + n ≤ Artifacts.Release.size) :
    InRegion (Region base Artifacts.Release.size) base o n := fun j hj => by
  show (base + BitVec.ofNat 32 (o + j) - base).toNat < _
  have : Artifacts.Release.size < 2 ^ 32 := by decide
  rw [Frame.sub_ofNat_toNat _ _ (by omega)]; omega

/-! ## The save area -/

/-- The save area of the prologue: word `i < 9` above `E c + LFRAME` holds `savedReg i`
(`r8`-`r11`, `r4`-`r7`, `lr`). -/
def Saved (c : X25519.Ctx) (m : Mem) : Prop :=
  ∀ i < 9, read32 m (E c + BitVec.ofNat 32 (LFRAME + 4 * i)) = c.regs0 (savedReg i)

/-! ## The tail -/

theorem add_ofNat_ofNat (a : Word) (x y : Nat) :
    a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem savedReg_8 : savedReg 8 = 14 := rfl

section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

theorem E_sub_callee : E c - BitVec.ofNat 32 CALLEE = c.fp := by
  apply BitVec.eq_of_toNat_eq
  rw [X25519Op.E_sub hv (Nat.le_refl _), X25519Op.E_toNat hv, X25519Op.fp_toNat hv]
  simp only [X25519.stackBytes, SAVED, LFRAME, CALLEE]; omega

theorem fp_lt : c.fp.toNat + X25519.stackBytes ≤ 2 ^ 32 := by
  have := X25519Op.fp_toNat hv; have := hv.spLo; have := c.sp0.isLt; omega

end

/-- **Tail of the entry**: from `oStore` to the return. -/
theorem tail_w {c : X25519.Ctx} (hv : X25519.Valid c) (hlr : (c.regs0 14).getLsbD 0 = true)
    {P : State → Event → Prop}
    (hS : ∀ z e, RegionWrites (Region (c.base + BitVec.ofNat 32 oStore) (oWipe - oStore))
      (Region c.out 32) z e → P z e)
    (hW : ∀ z e, RegionWrites (Region (c.base + BitVec.ofNat 32 oWipe) (Artifacts.Release.size - oWipe))
      (Region c.fp X25519.stackBytes) z e → P z e) {s : State}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oStore) (hsp : s.regs 13 = E c)
    (h0 : s.regs 0 = E c + BitVec.ofNat 32 sX2)
    (hout : read32 s.mem (E c + BitVec.ofNat 32 lvOut) = c.out) (hsv : Saved c s.mem) :
    ReachS c.base P s fun t =>
      t.pc = c.ret ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r) ∧
      t.regs 0 = 0#32 ∧ t.regs 1 = 0#32 ∧ t.regs 2 = 0#32 ∧ t.regs 3 = 0#32 ∧ t.regs 12 = 0#32 ∧
      (∀ k < 32, t.mem (c.out + BitVec.ofNat 32 k) =
        BitVec.ofNat 8 (feVal s.mem (E c + BitVec.ofNat 32 sX2) / 2 ^ (8 * k))) ∧
      (∀ y, Region c.fp X25519.wipeBytes y → t.mem y = 0#8) ∧
      (∀ y, ¬ Region c.fp X25519.wipeBytes y → ¬ Region c.out 32 y → t.mem y = s.mem y) := by
  obtain ⟨atS, atW, atE⟩ := tail_at
  have hb : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hE := X25519Op.E_toNat hv
  have hF := X25519Op.fp_toNat hv
  have hlo := hv.spLo
  have hs4 := hv.sp4
  have hsz := c.sp0.isLt
  have hO := hv.outS
  have hend := oEpi_end
  have hev := oStore_even
  have hevS := X25519OpRun.seqSize_even storeOut
  have hevW := X25519OpRun.seqSize_even wipe
  have hoW := oWipe_eq
  have hoE := oEpi_eq
  simp only [X25519.stackBytes, SAVED, LFRAME, Disj] at hE hF hlo hO
  obtain ⟨-, kX2, -, -, -, -, -, -, kL, kLF⟩ := X25519Layout.lay
  have kW : X25519.wipeBytes = 480 := rfl
  have kS : X25519.stackBytes = 516 := rfl
  have eX2 : (E c + BitVec.ofNat 32 sX2).toNat = (E c).toNat + sX2 := X25519Op.E_add hv (by decide)
  have eLv : ∀ d, d ≤ LFRAME + SAVED → (E c + BitVec.ofNat 32 d).toNat = (E c).toNat + d :=
    fun d hd => X25519Op.E_add hv hd
  -- output stores
  have hS32 : Artifacts.Release.size < 2 ^ 32 := by decide
  refine X25519Block.seg hS (X25519OutStore.storeOut_run_w hb atS hev hpc hsp (by rw [hE]; omega) h0 hout
    (by rw [eX2]; omega)
    ⟨by rw [eX2]; omega, hO.1, by rw [eX2]; omega⟩
    (fun k hk => show Region c.out 32 _ by
      show ((c.out + BitVec.ofNat 32 k) - c.out).toNat < 32
      rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact hk)
    (X25519MulcFacts.inReg ⟨Nat.le_refl _, by omega, by omega⟩) ?_)
  intro u upc ureg ubytes uoth
  refine ReachS.done ?_
  -- wipe
  have u13 : u.regs 13 = E c := by rw [ureg 13 (by decide) (by decide) (by decide), hsp]
  refine X25519Block.seg hW (X25519OutWipe.wipe_run_w hb atW (by omega) (by rw [upc]; rfl)
    (by rw [u13]; exact E_sub_callee hv) (by rw [hF]; omega)
    (by rw [hF]; omega)
    (fun y hy => X25519Op.region_sub (by rw [hF]; omega) (Nat.le_refl _) (by omega) hy)
    (X25519MulcFacts.inReg ⟨Nat.le_refl _, by omega, by omega⟩) ?_)
  intro w wpc w13 wz wreg wzero woth
  refine ReachS.done ?_
  -- epilogue
  have rf : ∀ y, (c.fp.toNat ≤ y.toNat → c.fp.toNat + X25519.wipeBytes ≤ y.toNat) →
      w.mem y = u.mem y := fun y hy => woth y (by rw [X25519Op.region_iff (by omega)]; omega)
  have ro : ∀ y, (c.fp.toNat ≤ y.toNat ∧ y.toNat < c.fp.toNat + X25519.stackBytes) →
      u.mem y = s.mem y := fun y hy => uoth y (by rw [X25519Op.region_iff (by omega)]; omega)
  have hsavW : ∀ i < 9, read32 w.mem (E c + BitVec.ofNat 32 LFRAME + BitVec.ofNat 32 (4 * i)) =
      c.regs0 (savedReg i) := by
    intro i hi
    rw [← hsv i hi, add_ofNat_ofNat]
    apply Frame.read32_congr
    intro k hk
    have ey : (E c + BitVec.ofNat 32 (LFRAME + 4 * i) + BitVec.ofNat 32 k).toNat =
        (E c).toNat + LFRAME + 4 * i + k := by
      rw [add_ofNat_ofNat, eLv _ (by simp only [LFRAME, SAVED]; omega)]; omega
    rw [rf _ (by rw [ey]; omega), ro _ (by rw [ey]; omega)]
  have hF' : w.regs 13 + BitVec.ofNat 32 (CALLEE + LFRAME) = E c + BitVec.ofNat 32 LFRAME := by
    rw [w13]; apply BitVec.eq_of_toNat_eq
    rw [eLv _ (by decide)]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, CALLEE, LFRAME]; omega
  have hF4 : (E c + BitVec.ofNat 32 LFRAME).toNat % 4 = 0 := by
    rw [eLv _ (by decide)]; simp only [LFRAME]; omega
  have hret := hsavW 8 (by decide)
  rw [savedReg_8] at hret
  refine X25519Block.seg hW (X25519OutEpi.epilogue_run_w hb atE (by omega) (by rw [wpc, hoE]) hF' hF4
    (by rw [hret]; exact hlr) (X25519MulcFacts.inReg ⟨by omega, by omega, by omega⟩) ?_)
  intro t tpc t13 tmem t0 t12 t13r tsv
  refine ReachS.done ⟨by rw [tpc, hret]; rfl, ?_, ?_, t0, ?_, ?_, ?_, t12, ?_, ?_, ?_⟩
  · rw [t13, add_ofNat_ofNat]; apply BitVec.eq_of_toNat_eq
    rw [eLv _ (Nat.le_refl _)]; simp only [LFRAME, SAVED]; omega
  · intro r h4 h12
    obtain ⟨i, hi, rfl⟩ := X25519OutEpi.savedReg_cover r h4 h12
    rw [tsv i hi, hsavW i (by omega)]
  · rw [t13r 1 (by decide) (by decide)]; exact wz 1 (by decide) (by decide)
  · rw [t13r 2 (by decide) (by decide)]; exact wz 2 (by decide) (by decide)
  · rw [t13r 3 (by decide) (by decide)]; exact wz 3 (by decide) (by decide)
  · intro k hk
    have ey : (c.out + BitVec.ofNat 32 k).toNat = c.out.toNat + k := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [tmem, rf _ (by rw [ey]; omega)]; exact ubytes k hk
  · intro y hy; rw [tmem]; exact wzero y hy
  · intro y hy1 hy2; rw [tmem, woth y hy1]; exact uoth y hy2

end M0Crypto.Release.X25519OutAt
