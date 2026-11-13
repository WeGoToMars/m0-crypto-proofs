import M0Crypto.Release.X25519Congr
import M0Crypto.Release.X25519Chain
import M0Crypto.Spec.X25519

/-!
The ladder algebra of `m0c_x25519` against RFC 7748.

The entry works on frame slots, and each field operation leaves a value that is only
congruent modulo `p` to its exact result. These lemmas take one congruence per slot
operation, in the code's order (generator `emit_x25519`, `dbl`), and conclude congruence with
`Spec.X25519`:

* `ladderStep_congr`: one iteration for bits 254 to 3. The code applies the conditional swap to
  the sums and differences (`SA`, `SB`), the RFC to the four inputs; both give the same new
  state.
* `dbl_congr`: the doubling body of the tail loop, against `dbl`, the RFC step for a zero bit.
* `ladderStep_zero`: for a zero bit, the RFC step is the pending swap followed by `dbl`.
* `x25519_tail`: for a scalar with bits 0 to 2 clear (every clamped scalar), RFC 7748
  `X25519` is the ladder over bits 254 to 3, the pending swap, three doublings and `output`.
* `output_canon`: the canonical residue of `x * z^(p - 2)` encodes as `output x z`.

Polynomial identities are closed by `grind` in small named lemmas.
-/

namespace M0Crypto.Release.X25519Ladder

open M0Crypto.Release.X25519Congr
open M0Crypto.Spec.X25519 (LadderState ladderStep ladderInit cswap a24 output encodeUCoordinate)

theorem spec_p : Spec.X25519.p = p := rfl

theorem emod_congr (a : Int) : a % Spec.X25519.p ≡p a := ModP.emod_left a

/-! ## Identities -/

theorem sq_eq_mul (y : Int) : y ^ 2 = y * y := by grind

theorem sub_sq_comm (a b : Int) : (a - b) ^ 2 = (b - a) ^ 2 := by grind

theorem z2_identity (aa bb e : Int) (he : e ≡p aa - bb) :
    121666 * e + bb ≡p aa + a24 * e := by
  have h1 : 121666 * e + bb = 121665 * e + e + bb := by grind
  have h2 : aa + a24 * e = 121665 * e + (aa - bb) + bb := by unfold a24; grind
  rw [h1, h2]
  exact ModP.add (ModP.add (ModP.refl _) he) (ModP.refl _)

/-! ## One ladder step (bits 254 to 3) -/

/-- The slot values of one ladder iteration of the code, given as congruences. `sw` is the
swap bit the code computes (`r7 = -(swap ^ k_t)`); `SA`, `SB` are exact selections. -/
structure StepSlots (x1 x2 z2 x3 z3 : Int) (sw : Nat)
    (A B C D SA SB DA CB X3s X3' Z3d Z3s Z3' AA BB X2' E T Z2' : Int) : Prop where
  hA : A ≡p x2 + z2
  hB : B ≡p x2 - z2
  hC : C ≡p x3 + z3
  hD : D ≡p x3 - z3
  hSA : SA = if sw = 1 then C else A
  hSB : SB = if sw = 1 then D else B
  hDA : DA ≡p D * A
  hCB : CB ≡p C * B
  hX3s : X3s ≡p DA + CB
  hX3 : X3' ≡p X3s * X3s
  hZ3d : Z3d ≡p DA - CB
  hZ3s : Z3s ≡p Z3d * Z3d
  hZ3 : Z3' ≡p x1 * Z3s
  hAA : AA ≡p SA * SA
  hBB : BB ≡p SB * SB
  hX2 : X2' ≡p AA * BB
  hE : E ≡p AA - BB
  hT : T ≡p 121666 * E + BB
  hZ2 : Z2' ≡p E * T

/-- The code state matches the RFC state `s`. -/
structure Matches (s : LadderState) (x2 z2 x3 z3 : Int) : Prop where
  x2 : x2 ≡p s.x2
  z2 : z2 ≡p s.z2
  x3 : x3 ≡p s.x3
  z3 : z3 ≡p s.z3

/-! ### Congruence to the RFC's reduced form -/

local notation "P" => Spec.X25519.p

theorem addm {a b c d : Int} (h1 : a ≡p b) (h2 : c ≡p d) : a + c ≡p (b + d) % P :=
  (ModP.add h1 h2).trans (emod_congr _).symm

theorem subm {a b c d : Int} (h1 : a ≡p b) (h2 : c ≡p d) : a - c ≡p (b - d) % P :=
  (ModP.sub h1 h2).trans (emod_congr _).symm

theorem mulm {a b c d : Int} (h1 : a ≡p b) (h2 : c ≡p d) : a * c ≡p b * d % P :=
  (ModP.mul h1 h2).trans (emod_congr _).symm

theorem sqm {a b : Int} (h : a ≡p b) : a * a ≡p b ^ 2 % P := by
  rw [sq_eq_mul]; exact mulm h h

/-- The doubling half of a step: from `SA ≡ a` and `SB ≡ b`, the new `x2`, `z2` in the
RFC's reduced form. -/
theorem dbl_half {SA SB AA BB X2' E T Z2' a b : Int} (hAA : AA ≡p SA * SA) (hBB : BB ≡p SB * SB)
    (hX2 : X2' ≡p AA * BB) (hE : E ≡p AA - BB) (hT : T ≡p 121666 * E + BB) (hZ2 : Z2' ≡p E * T)
    (ha : SA ≡p a) (hb : SB ≡p b) :
    X2' ≡p (a ^ 2 % P) * (b ^ 2 % P) % P ∧
      Z2' ≡p ((a ^ 2 % P - b ^ 2 % P) % P) *
        ((a ^ 2 % P) + a24 * ((a ^ 2 % P - b ^ 2 % P) % P)) % P := by
  have hAA := hAA.trans (sqm ha)
  have hBB := hBB.trans (sqm hb)
  have hE := hE.trans (subm hAA hBB)
  refine ⟨hX2.trans (mulm hAA hBB), hZ2.trans (mulm hE ?_)⟩
  exact hT.trans ((ModP.add (ModP.mul_left 121666 hE) hBB).trans (z2_identity _ _ _ (emod_congr _)))

theorem ladderStep_congr (k : Nat) (u x1 : Int) (s : LadderState) (t : Nat)
    (hsw : s.swap ≤ 1) (hx1 : x1 ≡p u)
    {x2 z2 x3 z3 A B C D SA SB DA CB X3s X3' Z3d Z3s Z3' AA BB X2' E T Z2' : Int}
    (hm : Matches s x2 z2 x3 z3)
    (h : StepSlots x1 x2 z2 x3 z3 (s.swap ^^^ ((k >>> t) &&& 1))
      A B C D SA SB DA CB X3s X3' Z3d Z3s Z3' AA BB X2' E T Z2') :
    Matches (ladderStep k u s t) X2' Z2' X3' Z3' ∧
      (ladderStep k u s t).swap = (k >>> t) &&& 1 := by
  refine ⟨?_, rfl⟩
  have hA := h.hA.trans (ModP.add hm.x2 hm.z2)
  have hB := h.hB.trans (ModP.sub hm.x2 hm.z2)
  have hC := h.hC.trans (ModP.add hm.x3 hm.z3)
  have hD := h.hD.trans (ModP.sub hm.x3 hm.z3)
  have hX3 : X3' ≡p (D * A + C * B) * (D * A + C * B) :=
    h.hX3.trans (ModP.mul (h.hX3s.trans (ModP.add h.hDA h.hCB))
      (h.hX3s.trans (ModP.add h.hDA h.hCB)))
  have hZ3 : Z3' ≡p u * ((D * A - C * B) * (D * A - C * B)) :=
    h.hZ3.trans (ModP.mul hx1 (h.hZ3s.trans (ModP.mul
      (h.hZ3d.trans (ModP.sub h.hDA h.hCB)) (h.hZ3d.trans (ModP.sub h.hDA h.hCB)))))
  have hk : (k >>> t) &&& 1 ≤ 1 := Nat.and_le_right
  have hsw' : s.swap ^^^ ((k >>> t) &&& 1) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with h0 | h0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h1 | h1 <;> simp [h0, h1]
  have dblHalf := fun a b (ha : SA ≡p a) (hb : SB ≡p b) =>
    dbl_half h.hAA h.hBB h.hX2 h.hE h.hT h.hZ2 ha hb
  have hA' := hA.trans (emod_congr _).symm
  have hB' := hB.trans (emod_congr _).symm
  have hC' := hC.trans (emod_congr _).symm
  have hD' := hD.trans (emod_congr _).symm
  simp only [ladderStep, cswap]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw' with hs | hs
  · have hSA : SA = A := by rw [h.hSA, hs]; rfl
    have hSB : SB = B := by rw [h.hSB, hs]; rfl
    simp only [hs, Nat.zero_ne_one, ↓reduceIte]
    obtain ⟨d1, d2⟩ := dblHalf _ _ (hSA ▸ hA') (hSB ▸ hB')
    refine ⟨d1, d2, ?_, ?_⟩ <;> dsimp only
    · refine hX3.trans ?_
      rw [← sq_eq_mul]
      exact (ModP.pow (ModP.add (mulm hD' hA') (mulm hC' hB')) 2).trans (emod_congr _).symm
    · refine hZ3.trans ?_
      rw [← sq_eq_mul]
      exact (ModP.mul (ModP.refl u) (ModP.pow (ModP.sub (mulm hD' hA') (mulm hC' hB')) 2)).trans
        (emod_congr _).symm
  · have hSA : SA = C := by rw [h.hSA, hs]; rfl
    have hSB : SB = D := by rw [h.hSB, hs]; rfl
    simp only [hs, ↓reduceIte]
    obtain ⟨d1, d2⟩ := dblHalf _ _ (hSA ▸ hC') (hSB ▸ hD')
    refine ⟨d1, d2, ?_, ?_⟩ <;> dsimp only
    · refine hX3.trans ?_
      rw [show D * A + C * B = B * C + A * D by grind, ← sq_eq_mul]
      exact (ModP.pow (ModP.add (mulm hB' hC') (mulm hA' hD')) 2).trans (emod_congr _).symm
    · refine hZ3.trans ?_
      rw [show (D * A - C * B) * (D * A - C * B) = (B * C - A * D) ^ 2 by grind]
      exact (ModP.mul (ModP.refl u) (ModP.pow (ModP.sub (mulm hB' hC') (mulm hA' hD')) 2)).trans
        (emod_congr _).symm

/-! ## The tail: bits 2 to 0 -/

/-- The RFC step for a zero bit, as a function of the selected `x_2`, `z_2`. -/
def dbl (x z : Int) : Int × Int :=
  let A := (x + z) % P
  let AA := A ^ 2 % P
  let B := (x - z) % P
  let BB := B ^ 2 % P
  let E := (AA - BB) % P
  (AA * BB % P, E * (AA + a24 * E) % P)

/-- For a zero bit, the RFC step applies the pending swap and doubles. -/
theorem ladderStep_zero (k : Nat) (u : Int) (s : LadderState) (t : Nat)
    (hbit : (k >>> t) &&& 1 = 0) :
    (ladderStep k u s t).x2 = (dbl (cswap s.swap s.x2 s.x3).1 (cswap s.swap s.z2 s.z3).1).1 ∧
      (ladderStep k u s t).z2 = (dbl (cswap s.swap s.x2 s.x3).1 (cswap s.swap s.z2 s.z3).1).2 ∧
      (ladderStep k u s t).swap = 0 := by
  unfold ladderStep dbl cswap
  simp [hbit]

/-- The doubling body of the code's tail loop, slot by slot, against `dbl`. -/
theorem dbl_congr {x z xs zs A B AA BB X' E T Z' : Int} (hx : x ≡p xs) (hz : z ≡p zs)
    (hA : A ≡p x + z) (hB : B ≡p x - z) (hAA : AA ≡p A * A) (hBB : BB ≡p B * B)
    (hX : X' ≡p AA * BB) (hE : E ≡p AA - BB) (hT : T ≡p 121666 * E + BB) (hZ : Z' ≡p E * T) :
    X' ≡p (dbl xs zs).1 ∧ Z' ≡p (dbl xs zs).2 :=
  dbl_half hAA hBB hX hE hT hZ (hA.trans (addm hx hz)) (hB.trans (subm hx hz))

theorem bits_low (k : Nat) (hk : k % 8 = 0) (t : Nat) (ht : t < 3) : (k >>> t) &&& 1 = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have h : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases h with h | h | h <;> subst h
  · simp only [Nat.pow_zero, Nat.div_one]; omega
  · simp only [Nat.pow_one]; omega
  · show k / 4 % 2 = 0; omega

theorem range_split : (List.range 255).reverse = (List.range' 3 252).reverse ++ [2, 1, 0] := by
  rw [show 255 = 3 + 252 from rfl, List.range_add, List.reverse_append]
  rw [show List.map (fun x => 3 + x) (List.range 252) = List.range' 3 252 by
    rw [List.range_eq_range', List.map_add_range']]
  rfl

/-- The ladder over bits 254 to 3, before the pending swap. -/
def ladderTop (k : Nat) (u : Int) : LadderState :=
  ((List.range' 3 252).reverse).foldl (ladderStep k u) (ladderInit u)

/-- Three doublings from `(x, z)`. -/
def dbl3 (x z : Int) : Int × Int :=
  let d1 := dbl x z
  let d2 := dbl d1.1 d1.2
  dbl d2.1 d2.2

/-- The code's route to the output: the ladder over bits 254 to 3, the pending swap, three
doublings and `output`. -/
def tailOut (k : Nat) (u : Int) : List Spec.X25519.Byte :=
  let s := ladderTop k u
  let d := dbl3 (cswap s.swap s.x2 s.x3).1 (cswap s.swap s.z2 s.z3).1
  output d.1 d.2

/-- For a scalar with bits 0 to 2 clear, RFC 7748 `X25519` equals `tailOut`. -/
theorem x25519_tail (kb ub : List Spec.X25519.Byte)
    (hk : Spec.X25519.decodeScalar25519 kb % 8 = 0) :
    Spec.X25519.x25519 kb ub =
      tailOut (Spec.X25519.decodeScalar25519 kb) (Spec.X25519.decodeUCoordinate ub) := by
  unfold Spec.X25519.x25519 tailOut
  generalize Spec.X25519.decodeScalar25519 kb = k at hk ⊢
  generalize (Spec.X25519.decodeUCoordinate ub : Int) = u
  simp only [Spec.X25519.ladder, Spec.X25519.bits, range_split, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  rw [show (List.range' 3 252).reverse.foldl (ladderStep k u) (ladderInit u) = ladderTop k u
    from rfl]
  generalize ladderTop k u = s
  obtain ⟨a2, b2, c2⟩ := ladderStep_zero k u s 2 (bits_low k hk 2 (by omega))
  obtain ⟨a1, b1, c1⟩ := ladderStep_zero k u (ladderStep k u s 2) 1 (bits_low k hk 1 (by omega))
  obtain ⟨a0, b0, c0⟩ := ladderStep_zero k u (ladderStep k u (ladderStep k u s 2) 1) 0
    (bits_low k hk 0 (by omega))
  simp only [cswap, c0, c1, c2, Nat.zero_ne_one, ↓reduceIte] at a0 b0 a1 b1 ⊢
  rw [a0, b0, a1, b1, a2, b2]
  rfl

/-! ## Output -/

theorem exp_toNat : (Spec.X25519.p - 2).toNat = 2 ^ 255 - 21 := by
  unfold Spec.X25519.p; omega

/-- The canonical residue `c` of `x * z^(p - 2)` encodes as the RFC's `output x z`. -/
theorem output_canon (x z : Int) (c : Nat) (hc : (c : Int) < p)
    (h : (c : Int) ≡p x * z ^ (2 ^ 255 - 21)) :
    output x z = (List.range 32).map fun i => BitVec.ofNat 8 (c / 2 ^ (8 * i)) := by
  unfold output encodeUCoordinate
  rw [exp_toNat, spec_p]
  have e : x * z ^ (2 ^ 255 - 21) % p = (c : Int) := by
    unfold ModP at h; rw [← h]; exact Int.emod_eq_of_lt (by omega) hc
  rw [e]; simp

end M0Crypto.Release.X25519Ladder
