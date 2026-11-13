import M0Crypto.Release.X25519OpInline
import M0Crypto.Release.X25519InlCanon
import M0Crypto.Release.X25519SlotEnv
import M0Crypto.Release.X25519ChainLoop
import M0Crypto.Release.X25519EntrySeg

set_option linter.unusedSimpArgs false

/-!
The final multiplication and canonical reduction of `m0c_x25519` (plan `x25519-proofs.md`,
phase 9, step 6): `finishAt oFinish` is `X2 = X2 * Z2` (a call), `add r0, sp, #X2`, and the
inline `canon_body` on `X2`. From `oFinish` to `oStore`, the slot `X2` ends congruent to the
product and below p, `r0` points at it, and the rest of the frame is unchanged.
-/

namespace M0Crypto.Release.X25519Finish
open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B InRegion)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519SlotEnv (env)
open M0Crypto.Release.X25519Block (Runs Runs.reg)

theorem canon_eq : X25519Inl.canonBody = X25519EntryCode.canonBody := by decide

theorem finish_split (o : Nat) : finishAt o =
    opAt o (mul sX2 sX2 sZ2) ++ ([.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] ++ canonBody) := by
  simp only [finishAt, List.append_assoc]

section
variable {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
  (hL : lo ≤ oLadder) (hH : oStore ≤ hi)
include hv hcode hWr hPO hL hH

theorem finish_w {s : State} {Q : State → Prop}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oFinish) (hs : Body c m1 s)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 oStore → Body c m1 t →
      t.regs 0 = E c + BitVec.ofNat 32 sX2 →
      ModP (env c t.mem sX2) (env c s.mem sX2 * env c s.mem sZ2) →
      feVal t.mem (slotAt c sX2) < 2 ^ 255 - 19 →
      (∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sX2) 32 y → t.mem y = s.mem y) →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have hseq := X25519EntrySeg.finish_seg
  have hlo : oLadder ≤ oFinish := by decide +kernel
  have hev : oFinish % 2 = 0 := by decide +kernel
  have hSt : oStore = oFinish + seqSize (opAt oFinish (mul sX2 sX2 sZ2)) + 2 + seqSize canonBody := by
    show oFinish + seqSize (finishAt oFinish) = _
    rw [finish_split, seqSize_append, seqSize_append,
      show seqSize [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] = 2 from rfl, Nat.add_assoc, Nat.add_assoc]
  have hn := X25519OpRun.seqSize_even (opAt oFinish (mul sX2 sX2 sZ2))
  rw [finish_split, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true] at hseq
  obtain ⟨h1, h2, h3⟩ := hseq
  rw [show seqSize [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] = 2 from rfl] at h3
  rw [← canon_eq] at h3
  rw [hSt] at k hH
  generalize oFinish = o at hpc hlo hev hn h1 h2 h3 k hH
  have hN : seqSize (opAt o ⟨Fn.mul, sX2, sX2, some sZ2⟩) = seqSize (opAt o (mul sX2 sX2 sZ2)) := rfl
  refine mul_opW hv hcode hWr hPO h1 hev (by omega) (by omega) hpc hs
    (by decide) (fun h => nomatch h) ?_
  intro u upc E1
  have hb1 := E1.body
  have uv := E1.val
  simp only [mul, bAddr, Fn.rel] at uv
  have u13 : u.regs 13 = E c := hb1.sp
  -- `add r0, sp, #X2`
  have hreg : [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))].all X25519Mul.regOnly = true ∧
      [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))].all (!·.writesMem) = true := ⟨rfl, rfl⟩
  refine X25519Block.ReachW.blockRuns hb0 [.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] _ upc
    (by omega) h2 rfl
    (Runs.reg (Q := fun w => w = execAll [.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] u) hreg.1 hreg.2 rfl)
    (hPO.inE (by omega) (by rw [show seqSize [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] = 2 from rfl]; omega)) ?_
  rintro w wpc rfl
  have w0 : (execAll [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] u).regs 0 =
      E c + BitVec.ofNat 32 sX2 := by
    rw [← u13]
    simp [execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0, sX2]
  have w13 : (execAll [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] u).regs 13 = E c := by
    rw [← u13]
    simp [execAll, Instr.next, Instr.exec, State.setReg, X25519Mem.toReg0]
  have wm : (execAll [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] u).mem = u.mem := by
    simp [execAll, Instr.next, Instr.exec, State.setReg]
  generalize execAll [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] u = w at w0 w13 wm wpc
  simp only [show seqSize [Instr.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] = 2 from rfl] at wpc
  -- address facts
  have hE := E_toNat hv
  have hF := fp_toNat hv
  have hsp := hv.spLo
  have hs4 := hv.sp4
  have eD : (E c + BitVec.ofNat 32 sX2).toNat = (E c).toNat + sX2 :=
    E_add hv (by decide)
  simp only [X25519.stackBytes, X25519.wipeBytes, SAVED, LFRAME, CALLEE, sX2] at *
  have hD : ∀ y, Region (E c + BitVec.ofNat 32 32) 32 y → Region c.fp 480 y := fun y h =>
    region_sub (by omega) (by omega) (by omega) h
  have hRw : ∀ y, Region c.fp 480 y → Region c.fp 516 y := fun y h =>
    region_sub (by omega) (Nat.le_refl _) (by omega) h
  have hW : ∀ j < 32, Wr (E c + BitVec.ofNat 32 32 + BitVec.ofNat 32 j) := fun j hj =>
    hWr _ (hRw _ (hD _ (by
      have := Frame.toNat_add_ofNat (E c + BitVec.ofNat 32 32) j (by omega)
      rw [region_iff (by omega)]; omega)))
  refine X25519Inl.canon_run_w hb0 h3 (by omega) wpc
    (hPO.inE (by omega) (by rw [canon_eq]; omega)) w0 (by rw [eD]; omega)
    (by omega) hW ?_
  intro t tpc tv tlt tm tr
  rw [canon_eq] at tpc
  have tpc' : t.pc = c.base + BitVec.ofNat 32 (o + seqSize (opAt o (mul sX2 sX2 sZ2)) + 2 +
      seqSize canonBody) := by rw [tpc]; rfl
  have t0 : t.regs 0 = E c + BitVec.ofNat 32 32 := by rw [tr 0 (by decide) (by decide)]; exact w0
  have t13 : t.regs 13 = E c := by rw [tr 13 (by decide) (by decide)]; exact w13
  refine k t tpc' ⟨t13, fun y hy => ?_⟩ t0 ?_ tlt fun y hy1 hy2 => ?_
  · rw [tm y fun h => hy (hD y h), wm]; exact hb1.keep y hy
  · rw [wm] at tv
    exact (ModP.trans tv uv)
  · rw [tm y hy2, wm]; exact E1.keep y hy1 hy2

end

end M0Crypto.Release.X25519Finish
