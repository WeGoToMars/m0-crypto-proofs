import M0Crypto.Release.ConstantTime.Reach
import M0Crypto.Release.ConstantTime.StackForgetFrame

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb

/-- The checked call guard gives its exact public stack and argument offsets. -/
theorem FrameCall.ok_fields {f : FrameCall} {w : StackWindow} {target : Nat} {st : AbsState}
    (h : f.ok w target st = true) :
    target = f.target ∧ st.spOff = f.spOff ∧
      st.get 0 = .sp f.dstOff f.dstOff ∧ st.get 1 = .sp f.srcOff f.srcOff ∧
      w.covers f.spOff (f.spOff + f.frame) = true := by
  simp only [FrameCall.ok,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hT,hSp⟩,hDst⟩,hSrc⟩,hW⟩
  exact ⟨hT,hSp,hDst,hSrc,hW⟩

/-- The abstract return state follows from the concrete return PC, preserved SP,
and confinement of writes to the declared frame. -/
theorem FrameCall.after_sound {f : FrameCall} {w : StackWindow} {p : Params} {st : AbsState}
    {bytes : List (BitVec 8)} {off : Nat} {a b u v : State}
    (h : LowEq p bytes off st a b)
    (hwidth : w.below + w.above < 2 ^ 32)
    (hslots : st.stk.slotsOk w)
    (hwin : w.covers f.spOff (f.spOff + f.frame) = true)
    (hPcu : u.pc = p.base + BitVec.ofNat 32 (off+4)) (hPcv : v.pc = u.pc)
    (hSpu : u.sp = a.sp) (hSpv : v.sp = b.sp)
    (hcU : CodeAt u.mem p.base bytes) (hcV : CodeAt v.mem p.base bytes)
    (hW : ∀ y, (∀ i < f.frame, y ≠ p.sp0 + BitVec.ofInt 32 f.spOff + BitVec.ofNat 32 i) →
      u.mem y = a.mem y ∧ v.mem y = b.mem y) :
    LowEq p bytes (off+4) (f.after st) u v := by
  refine ⟨hPcu,hPcv,?_,?_,?_,?_,?_,?_,?_,?_,h.size,hcU,hcV⟩
  · exact hSpu.trans h.sp
  · exact hSpv.trans (h.sp_eq.trans hSpu.symm)
  · intro i hi _
    simp [FrameCall.after,AbsState.get,regGet,hi,AbsVal.Sem]
  · exact ⟨trivial,trivial,trivial,trivial⟩
  · intro c hc
    cases hc
  · exact stkForget_write_frame w hwidth hslots hwin (Int.le_refl _) (Int.le_refl _) h.stack hW
  · intro fact hf
    cases hf
  · intro link hl
    cases hl

end M0Crypto.Release.ConstantTime
