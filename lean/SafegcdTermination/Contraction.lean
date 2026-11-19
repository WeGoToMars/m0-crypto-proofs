module

public import SafegcdTermination.Certificate

@[expose] public section

namespace SafegcdTermination

private theorem seed_one (i : Fin 16) :
    1000 * magnitude (b i) ≤ w i ∧ 1000 * magnitude (a i + b i) ≤ w i :=
  of_decide_eq_true (List.all_eq_true.mp initialWeights i (List.mem_finRange i))

theorem seed (g : Int) (hg : 0 ≤ g) (hgp : g ≤ p) : Bounded 0 p g := by
  intro i
  have hrest : 0 ≤ p - g := by omega
  obtain ⟨hb, hab⟩ := seed_one i
  have e : a i * g + b i * p = (a i + b i) * g + b i * (p - g) := by grind only
  unfold boundDenominator boundNumerator
  simp only [Int.pow_zero, Int.mul_one, e]
  calc
    _ ≤ (magnitude (a i + b i) * g + magnitude (b i) * (p - g)) * 1000 := by
      apply Int.mul_le_mul_of_nonneg_right _ (by decide)
      simpa only [magnitude_mul, magnitude_of_nonneg hg, magnitude_of_nonneg hrest] using
        magnitude_add_le ((a i + b i) * g) (b i * (p - g))
    _ = (1000 * magnitude (a i + b i)) * g + (1000 * magnitude (b i)) * (p - g) := by
      grind only
    _ ≤ w i * g + w i * (p - g) :=
      Int.add_le_add (Int.mul_le_mul_of_nonneg_right hab hg)
        (Int.mul_le_mul_of_nonneg_right hb hrest)
    _ = _ := by grind only

private def dot (v : Int × Int) (f g : Int) : Int := v.1 * g + v.2 * f

private theorem magnitude_upperHalf (v : Int × Int) (f g : Int) :
    magnitude (dot (upperHalf v) f g) = magnitude (dot v f g) := by
  unfold upperHalf
  split
  · have e : dot (-v.1, -v.2) f g = -dot v f g := by simp only [dot]; grind only
    rw [e, magnitude_neg]
  · rfl

private theorem magnitude_neighbor (k : Fin 16) (f g : Int) :
    magnitude (dot (signNext k * a (neighbor k), signNext k * b (neighbor k)) f g) =
      magnitude (a (neighbor k) * g + b (neighbor k) * f) := by
  unfold signNext
  split
  · simp only [dot, Int.neg_mul, Int.one_mul]
    rw [← Int.neg_add, magnitude_neg]
  · simp [dot]

private theorem advance {n t : Nat} {u d cost bound : Int}
    (hd : 0 < d) (h : d * u * boundDenominator n ≤ cost * boundNumerator n)
    (hc : cost * 125 ^ t ≤ d * bound * 93 ^ t) :
    u * boundDenominator (n + t) ≤ bound * boundNumerator (n + t) := by
  rw [boundDenominator_add, boundNumerator_add, ← Int.mul_le_mul_left hd]
  have h₁ := Int.mul_le_mul_of_nonneg_right h (Int.pow_nonneg (n := 125) (m := t) (by decide))
  have h₂ := Int.mul_le_mul_of_nonneg_right hc (boundNumerator_nonneg n)
  simpa only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using Int.le_trans h₁
    (show cost * boundNumerator n * 125 ^ t ≤ d * (bound * (boundNumerator n * 93 ^ t)) by
      simpa only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h₂)

private theorem endpoint_short (n j : Nat) (hj : j < shortLimit) (i : Fin 16)
    (e : Bool) {f g : Int} (h : Bounded n f g) :
    magnitude (dot (endpoint j e i) f g) * boundDenominator (n + (2*j+1)) ≤
      (2 ^ (2*j+1) * w i) * boundNumerator (n + (2*j+1)) := by
  have chk := List.all_eq_true.mp
    (List.all_eq_true.mp checkShort j (List.mem_range.mpr hj)) i (List.mem_finRange i)
  obtain ⟨chkLo, chkHi⟩ := Bool.and_eq_true_iff.mp chk
  have any : (List.finRange 16).any (checkLine j e i) = true := by
    cases e
    · exact chkLo
    · exact chkHi
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp any
  let v := upperHalf (endpoint j e i)
  let l := (bracket v k).1
  let r := (bracket v k).2.1
  let d := (bracket v k).2.2
  have hK : 0 ≤ l ∧ 0 ≤ r ∧ 0 < d ∧
      (l * w k + r * w (neighbor k)) * 125 ^ (2*j+1) ≤
      d * 2 ^ (2*j+1) * w i * 93 ^ (2*j+1) := of_decide_eq_true hk
  obtain ⟨hl, hr, hd, hc⟩ := hK
  have eq : d * dot v f g =
      l * (a k * g + b k * f) +
      r * dot (signNext k * a (neighbor k), signNext k * b (neighbor k)) f g := by
    dsimp only [d, l, r, bracket, dot, Prod.fst, Prod.snd]
    grind only
  rw [← magnitude_upperHalf (endpoint j e i) f g]
  change magnitude (dot v f g) * _ ≤ _
  apply advance hd _ (by simpa only [Int.mul_assoc] using hc)
  have ht := magnitude_add_le (l * (a k * g + b k * f))
    (r * dot (signNext k * a (neighbor k), signNext k * b (neighbor k)) f g)
  rw [magnitude_mul, magnitude_mul, magnitude_of_nonneg hl, magnitude_of_nonneg hr,
    magnitude_neighbor] at ht
  rw [← magnitude_of_nonneg (Int.le_of_lt hd), ← magnitude_mul, eq]
  calc
    _ ≤ (l * magnitude (a k * g + b k * f) +
        r * magnitude (a (neighbor k) * g + b (neighbor k) * f)) * boundDenominator n :=
      Int.mul_le_mul_of_nonneg_right ht (Int.le_of_lt (boundDenominator_pos n))
    _ = l * (magnitude (a k * g + b k * f) * boundDenominator n) +
        r * (magnitude (a (neighbor k) * g + b (neighbor k) * f) * boundDenominator n) := by
      grind only
    _ ≤ l * (w k * boundNumerator n) + r * (w (neighbor k) * boundNumerator n) :=
      Int.add_le_add (Int.mul_le_mul_of_nonneg_left (h k) hl)
        (Int.mul_le_mul_of_nonneg_left (h (neighbor k)) hr)
    _ = _ := by grind only

theorem g_bound {n : Nat} {f g : Int} (h : Bounded n f g) :
    magnitude g * boundDenominator n ≤ 1055 * boundNumerator n := by
  have h := h 0
  change magnitude (1 * g + 0 * f) * boundDenominator n ≤ 1055 * boundNumerator n at h
  simpa using h

theorem f_bound {n : Nat} {f g : Int} (h : Bounded n f g) :
    magnitude f * boundDenominator n ≤ 1420 * boundNumerator n := by
  have h := h 8
  change magnitude (0 * g + 1 * f) * boundDenominator n ≤ 1420 * boundNumerator n at h
  simpa using h

private theorem long_ineq (j : Nat) (hj : shortLimit ≤ j) (i : Fin 16) :
    longCost i * 125 ^ (2*j+1) ≤ 2^(j+1) * w i * 93 ^ (2*j+1) := by
  have hBase : longCost i * 125 ^ (2 * shortLimit + 1) ≤
      w i * 2 ^ (shortLimit + 1) * 93 ^ (2 * shortLimit + 1) :=
    of_decide_eq_true (List.all_eq_true.mp checkLong i (List.mem_finRange i))
  have hw := Int.le_trans (Int.mul_nonneg (by decide) (magnitude_nonneg (b i))) (seed_one i).1
  have hBaseNonneg : 0 ≤ w i * 2 ^ (shortLimit + 1) * 93 ^ (2 * shortLimit + 1) :=
    Int.mul_nonneg (Int.mul_nonneg hw (Int.pow_nonneg (by decide))) (Int.pow_nonneg (by decide))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show shortLimit + k + 1 = shortLimit + 1 + k by omega,
    show 2 * (shortLimit + k) + 1 = (2 * shortLimit + 1) + 2*k by omega,
    Int.pow_add (2 : Int), Int.pow_add (93 : Int), Int.pow_add (125 : Int)]
  simpa only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using
    Int.mul_le_mul hBase (decay k) (Int.pow_nonneg (by decide)) hBaseNonneg

private theorem linear_between {a b c lo hi : Int} (hlo : lo ≤ c) (hhi : c ≤ hi)
    (K : Int) (h₁ : magnitude (lo * a + b) ≤ K) (h₂ : magnitude (hi * a + b) ≤ K) :
    magnitude (c * a + b) ≤ K := by
  rw [magnitude_le_iff] at h₁ h₂ ⊢
  by_cases hs : 0 ≤ a
  · have e₁ := Int.mul_le_mul_of_nonneg_right hlo hs
    have e₂ := Int.mul_le_mul_of_nonneg_right hhi hs
    omega
  · have e₁ := Int.mul_le_mul_of_nonpos_right hlo (by omega : a ≤ 0)
    have e₂ := Int.mul_le_mul_of_nonpos_right hhi (by omega : a ≤ 0)
    omega

/-- One return to counter 1, after j even steps, one swap and j non-swaps. -/
theorem contract (n j : Nat) (c : Int) {f g F G : Int} (h : Bounded n f g)
    (hc : 1 ≤ c ∧ c ≤ 2 * 2 ^ j - 1)
    (hF : 2 ^ j * F = g)
    (hG : 2 ^ (2*j+1) * G = c * g - 2 ^ j * f) :
    Bounded (n + (2*j+1)) F G := by
  intro i
  have hm : (0 : Int) < 2 ^ j := Int.pow_pos (by decide)
  have hd : (0 : Int) < 2 ^ (2*j+1) := Int.pow_pos (by decide)
  have hp : (2 : Int) ^ (2*j+1) = 2 * 2 ^ j * 2 ^ j := by
    rw [show 2*j+1 = j+j+1 by omega, Int.pow_succ, Int.pow_add]
    grind only
  by_cases hj : j < shortLimit
  · let D := boundDenominator (n + (2*j+1))
    let K := 2 ^ (2*j+1) * (w i * boundNumerator (n + (2*j+1)))
    let A := a i * g * D
    let B := (2 * 2 ^ j * b i * g - 2 ^ j * a i * f) * D
    have hD : 0 ≤ D := Int.le_of_lt (boundDenominator_pos _)
    have hEnd (e : Bool) :
        magnitude ((if e then 2 * 2 ^ j - 1 else 1) * A + B) ≤ K := by
      have h := endpoint_short n j hj i e h
      change magnitude (dot (endpoint j e i) f g) * D ≤ _ at h
      rw [← magnitude_of_nonneg hD, ← magnitude_mul] at h
      have eq : dot (endpoint j e i) f g * D =
          (if e then 2 * 2 ^ j - 1 else 1) * A + B := by
        dsimp only [dot, endpoint, A, B, Prod.fst, Prod.snd]
        grind only
      simpa only [eq, K, Int.mul_assoc] using h
    have hMid := linear_between hc.1 hc.2 K (hEnd false) (hEnd true)
    have eq : (2 ^ (2*j+1) * (a i * G + b i * F)) * D = c * A + B := by
      have hdot : 2 ^ (2*j+1) * (a i * G + b i * F) =
          a i * (2 ^ (2*j+1) * G) + (2 * 2 ^ j * b i) * (2 ^ j * F) := by
        rw [hp]
        grind only
      rw [hdot, hF, hG]
      dsimp only [A, B]
      grind only
    apply Int.le_of_mul_le_mul_left _ hd
    change 2 ^ (2*j+1) * (magnitude (a i * G + b i * F) * D) ≤ K
    rw [← magnitude_of_nonneg hD, ← magnitude_mul,
      ← magnitude_of_nonneg (Int.le_of_lt hd), ← magnitude_mul, ← Int.mul_assoc, eq]
    exact hMid
  · have hc' := long_ineq j (by omega) i
    rw [Int.pow_succ' 2 j] at hc'
    have hGc : (2 * 2 ^ j) * magnitude G ≤ 2 * magnitude g + magnitude f := by
      apply Int.le_of_mul_le_mul_right _ hm
      calc
        _ = magnitude ((2 : Int)^(2*j+1) * G) := by
          rw [magnitude_mul, magnitude_of_nonneg (Int.le_of_lt hd), hp]
          grind only
        _ = _ := congrArg magnitude hG
        _ ≤ magnitude (c * g) + magnitude (2 ^ j * f) := by
          simpa only [Int.sub_eq_add_neg, magnitude_neg] using
            magnitude_add_le (c*g) (-(2^j*f))
        _ ≤ _ := by
          rw [magnitude_mul, magnitude_mul, magnitude_of_nonneg (by omega : 0 ≤ c),
            magnitude_of_nonneg (Int.le_of_lt hm)]
          have h := Int.mul_le_mul_of_nonneg_right
            (show c ≤ 2 * 2 ^ j by omega) (magnitude_nonneg g)
          have eq : (2 * 2 ^ j) * magnitude g + 2 ^ j * magnitude f =
              (2 * magnitude g + magnitude f) * 2 ^ j := by grind only
          exact Int.le_trans (Int.add_le_add_right h _) (Int.le_of_eq eq)
    have hFc : (2 ^ j : Int) * magnitude F = magnitude g := by
      simpa only [magnitude_mul, magnitude_of_nonneg (Int.le_of_lt hm)] using congrArg magnitude hF
    let d : Int := 2 * 2^j
    have hpos : 0 < d := Int.mul_pos (by decide) hm
    apply advance hpos _ hc'
    let a' := magnitude (a i)
    let b' := magnitude (b i)
    have ht := magnitude_add_le (a i * G) (b i * F)
    rw [magnitude_mul, magnitude_mul] at ht
    have htri := Int.mul_le_mul_of_nonneg_left ht (Int.le_of_lt hpos)
    change d * magnitude (a i * G + b i * F) ≤ d * (a' * magnitude G + b' * magnitude F) at htri
    calc
      _ ≤ (d * (a' * magnitude G + b' * magnitude F)) * boundDenominator n :=
        Int.mul_le_mul_of_nonneg_right htri (Int.le_of_lt (boundDenominator_pos n))
      _ = (a' * (d * magnitude G) + (2 * b') * (2^j * magnitude F)) * boundDenominator n := by
        dsimp only [d]
        grind only
      _ ≤ (a' * (2 * magnitude g + magnitude f) + (2 * b') * magnitude g) * boundDenominator n := by
        rw [hFc]
        exact Int.mul_le_mul_of_nonneg_right
          (Int.add_le_add_right (Int.mul_le_mul_of_nonneg_left hGc (magnitude_nonneg _)) _)
          (Int.le_of_lt (boundDenominator_pos n))
      _ = 2 * (a' + b') * (magnitude g * boundDenominator n) +
          a' * (magnitude f * boundDenominator n) := by grind only
      _ ≤ 2 * (a' + b') * (1055 * boundNumerator n) + a' * (1420 * boundNumerator n) :=
        Int.add_le_add
          (Int.mul_le_mul_of_nonneg_left (g_bound h) (Int.mul_nonneg (by decide)
            (Int.add_nonneg (magnitude_nonneg _) (magnitude_nonneg _))))
          (Int.mul_le_mul_of_nonneg_left (f_bound h) (magnitude_nonneg _))
      _ = _ := by
        change _ = (2 * (a' + b') * 1055 + a' * 1420) * boundNumerator n
        grind only

end SafegcdTermination
