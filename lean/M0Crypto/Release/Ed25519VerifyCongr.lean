import M0Crypto.Release.Ed25519VerifyRun
import M0Crypto.Release.Ed25519CallProgSrcEq

/-!
# `m0c_ed25519_verify`'s trace from the readable buffers

`bodyTr_congr`: for any adapters `D`, two entry memories that agree on the readable regions of
the external buffers (`XAgree`) give the same body trace. The values `E1` … `E12`, the stitched
calls' inputs, their public values `P0` … `P11` and the tests' decisions `d0` … `d4` read the
entry memory only through those regions.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg

section
open VAd
variable {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **The body's trace is a function of the readable buffers' bytes.** -/
theorem bodyTr_congr (D : VAd Rs B BS) {c : Ctx} {m0 m0' : Mem} (h : XAgree verifyGeo c m0 m0') :
    D.bodyTr c m0 = D.bodyTr c m0' := by
  have e1 : D.E1 c m0 = D.E1 c m0' := Prog.ev_congr vpS vbS _ _ h p0 stE _
  have i0 : D.i0 c m0 = D.i0 c m0' := by unfold i0; rw [e1, ioVs_congr h]
  have e2 : D.E2 c m0 = D.E2 c m0' := by unfold E2; rw [e1, i0, xcallEv_congr h]
  have i1 : D.i1 c m0 = D.i1 c m0' := by unfold i1; rw [e2, ioVs_congr h]
  have e3 : D.E3 c m0 = D.E3 c m0' := by unfold E3; rw [e2, i1, xcallEv_congr h]
  have e4 : D.E4 c m0 = D.E4 c m0' := by unfold E4; rw [e3, Prog.ev_congr vpS vbS _ _ h]
  have i2 : D.i2 c m0 = D.i2 c m0' := by unfold i2; rw [e4, ioVs_congr h]
  have e5 : D.E5 c m0 = D.E5 c m0' := by unfold E5; rw [e4, i2, Op.ev_congr vxS vbS _ _ h]
  have e6 : D.E6 c m0 = D.E6 c m0' := by unfold E6; rw [e5, Prog.ev_congr vpS vbS _ _ h]
  have i5 : D.i5 c m0 = D.i5 c m0' := by unfold i5; rw [e6, ioVs_congr h]
  have e7 : D.E7 c m0 = D.E7 c m0' := by unfold E7; rw [e6, xcallEv_congr h]
  have i6 : D.i6 c m0 = D.i6 c m0' := by unfold i6; rw [e7, ioVs_congr h]
  have e8 : D.E8 c m0 = D.E8 c m0' := by unfold E8; rw [e7, xcallEv_congr h]
  have i7 : D.i7 c m0 = D.i7 c m0' := by unfold i7; rw [e8, ioVs_congr h]
  have e9 : D.E9 c m0 = D.E9 c m0' := by unfold E9; rw [e8, xcallEv_congr h]
  have e10 : D.E10 c m0 = D.E10 c m0' := by unfold E10; rw [e9, Prog.ev_congr vpS vbS _ _ h]
  have i9 : D.i9 c m0 = D.i9 c m0' := by unfold i9; rw [e10, ioVs_congr h]
  have e11 : D.E11 c m0 = D.E11 c m0' := by unfold E11; rw [e10, i9, xcallEv_congr h]
  have e12 : D.E12 c m0 = D.E12 c m0' := by unfold E12; rw [e11, Prog.ev_congr vpS vbS _ _ h]
  have i11 : D.i11 c m0 = D.i11 c m0' := by unfold i11; rw [e12, ioVs_congr h]
  unfold bodyTr tC0 tC1 tP2 tB2 tP3 tW5 tW3 tDm tM3 tE3 tM4 tE4 P0 P1 P5 P6 P7 P9 P11 d0 d1 d2 d3 d4
  rw [i0, i1, i2, i5, i6, i7, i9, i11]

end

end M0Crypto.Release.Ed25519VerifyProg
