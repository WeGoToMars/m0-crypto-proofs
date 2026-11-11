import M0Crypto.Release.ConstantTime.SemOffsets
import M0Crypto.Release.ConstantTime.SemRange

/-! Soundness of the guarded intersection used for affine stack pointers. -/
namespace M0Crypto.Release.ConstantTime

/-- If two offsets lie in one narrow window, equal addresses relative to the same
stack base imply equal offsets. -/
theorem offset_eq_of_address_eq (w : StackWindow) (base : M0Crypto.Armv6M.Word) (x y : Int)
    (hw : w.below + w.above < 2 ^ 32)
    (hxlo : -(w.below : Int) ≤ x) (hxhi : x < (w.above : Int))
    (hylo : -(w.below : Int) ≤ y) (hyhi : y < (w.above : Int))
    (heq : base + BitVec.ofInt 32 x = base + BitVec.ofInt 32 y) : x = y := by
  apply ofInt32_injective_on_win w x y hw hxlo hxhi hylo hyhi
  have h := congrArg (fun z : M0Crypto.Armv6M.Word => z - base) heq
  simpa [BitVec.add_comm, BitVec.add_sub_cancel] using h

/-- Guarded affine intersection preserves the concrete stack pointer value. -/
theorem guarded_sp_intersection (p : Params) (w : StackWindow) (a b c k : Int)
    (lo n hi : Nat) (x y : M0Crypto.Armv6M.Word)
    (hw : w.below + w.above < 2 ^ 32)
    (ha : -(w.below : Int) ≤ a) (hb : b < (w.above : Int))
    (hrlo : -(w.below : Int) ≤ (AbsState.lnkRange k c lo hi).1)
    (hrhi : (AbsState.lnkRange k c lo hi).2 < (w.above : Int))
    (hnlo : lo ≤ n) (hnhi : n ≤ hi)
    (hsp : AbsVal.Sem p (.sp a b) x y)
    (hlink : x = p.sp0 + BitVec.ofInt 32 (c + k * (n : Int))) :
    AbsVal.Sem p (.sp (max a (AbsState.lnkRange k c lo hi).1)
      (min b (AbsState.lnkRange k c lo hi).2)) x y := by
  obtain ⟨q, hqa, hqb, hqx, hy⟩ := hsp
  have hr := lnkRange_sound k c lo n hi hnlo hnhi
  have heq : q = c + k * (n : Int) := by
    apply offset_eq_of_address_eq w p.sp0 _ _ hw (by omega) (by omega)
      (by omega) (by omega)
    exact hqx.symm.trans hlink
  refine ⟨q, ?_, ?_, hqx, hy⟩
  · simp only [Int.max_le]; constructor <;> omega
  · simp only [Int.le_min]; constructor <;> omega

end M0Crypto.Release.ConstantTime
