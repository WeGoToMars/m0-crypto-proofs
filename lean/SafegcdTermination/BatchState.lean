import SafegcdTermination.Bank

namespace SafegcdTermination.BatchMachine

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.FoldRefine (value vec)
open M0Crypto.Armv6M (State Mem)

structure Slot (m : Mem) (sp : Word) (off : Nat) (x : Int) : Prop where
  value : value m (addr sp off) = x
  formed : VecWellFormed (vec m (addr sp off))

theorem Slot.move {m m' : Mem} {sp : Word} {a b : Nat} {x : Int} (h : Slot m sp b x)
    (hf : FrameOk sp) (ha : InSlot a) (hb : InSlot b) (hab : Separate a b)
    (hmem : WritesOnly m m' (addr sp a) vectorBytes) : Slot m' sp b x :=
  ⟨(value_disjoint hf ha hb hab hmem).trans h.value, formed_disjoint hf ha hb hab hmem h.formed⟩

theorem Slot.of_low {m : Mem} {sp : Word} {off : Nat} {x : Int} (hv : FoldRefine.value m (addr sp off) = x)
    (hl : Vectors.LowLimbs m (addr sp off)) (hlo : -2 * foldRadix ≤ x) (hhi : x < 3 * foldRadix) :
    Slot m sp off x := by
  refine ⟨hv, Vectors.well_formed_of_range _ _ hl ?_ ?_⟩ <;> rwa [hv]

structure VectorsAt (s : State) (b : Banks) (x : BatchState) : Prop where
  f : Slot s.mem s.sp b.f x.scalar.f
  g : Slot s.mem s.sp bankG x.scalar.g
  d : Slot s.mem s.sp b.d x.d
  e : Slot s.mem s.sp bankE x.e

structure Image (s : State) (b : Banks) (x : BatchState) : Prop extends VectorsAt s b x where
  delta : stackWord s deltaAt = BitVec.ofInt 32 x.scalar.delta

structure Range (x : BatchState) : Prop where
  odd : x.scalar.f % 2 = 1
  magnitudeF : magnitude (x.scalar.f) ≤ p
  magnitudeG : magnitude (x.scalar.g) ≤ p
  d : ResidueBounds x.d
  e : ResidueBounds x.e

theorem Range.next {x : BatchState} (hx : Range x) : Range x.next := by
  obtain ⟨hodd, _, ⟨hFn, hGn⟩, _, _⟩ := one_matrix x.scalar hx.odd
  obtain ⟨hF, hG⟩ := accumulate_scalar_bound x.scalar p hx.magnitudeF hx.magnitudeG batchSteps
  obtain ⟨hfl, hfh⟩ := rowQuotient_range hFn hx.d hx.e
  obtain ⟨hgl, hgh⟩ := rowQuotient_range hGn hx.d hx.e
  exact ⟨hodd, hF, hG, fold_range hfl hfh, fold_range hgl hgh⟩

theorem iterate_range {z : Int} (hz : 0 ≤ z) (hp : z < p) (n : Nat) : Range (iterate z n) := by
  induction n with
  | zero =>
    have hi := iterate_valid z 0
    refine ⟨hi.1, ?_, ?_, hi.2.1, hi.2.2.1⟩
    · change magnitude (p) ≤ p
      rw [magnitude_of_nonneg (Int.le_of_lt p_pos)]; exact Int.le_refl _
    · change magnitude (z) ≤ p
      rw [magnitude_of_nonneg hz]
      exact Int.le_of_lt hp
  | succ n ih => exact ih.next

theorem iterate_delta (z : Int) (n : Nat) (hn : n ≤ batchCount) :
    magnitude ((iterate z n).scalar.delta) ≤ (1205 : Int) := by
  rw [iterate_scalar]
  have hb := MatrixRefine.accumulate_delta_bound (initial z).scalar (n * batchSteps)
  have hc : magnitude ((initial z).scalar.delta) = 1 := by
    change magnitude ((1 : Int)) = 1
    decide
  simp only [hc, batchSteps, Int.natCast_mul, show ((14 : Nat) : Int) = 14 from rfl] at hb
  unfold batchCount at hn
  simp only [batchSteps]
  omega

end SafegcdTermination.BatchMachine
