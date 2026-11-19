import M0Crypto.Release.Ed25519Bridge

/-!
Encoding (`m0c_ge_compress`) against RFC 8032 section 5.1.2 (`Spec.Ed25519.encodePoint`).

The routine inverts `Z` by the Fermat chain (`Z^(p − 2)`, the inverse of `F_p`), forms
`x = X Z⁻¹` and `y = Y Z⁻¹`, reduces both to their canonical values and sets bit 255 of `y` to
the parity of `x`. `compressCode E` is that integer; the routine stores it as 32 little-endian
bytes, `encodeInt`.

* `encodePoint_eq`: the specification's encoding of a point is `encodeInt` of `compressCode` of
  its image in `F_p`.
* `compressCode_eq`: `compressCode` depends only on the represented point (`encodeAff`), so the
  code's point and the specification's point encode alike when they represent the same point.
-/

namespace M0Crypto.Release.Ed25519Encode

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519PrimeCert (p)

/-- The integer `m0c_ge_compress` stores: canonical `y = Y Z^(p−2)` with bit 255 the parity of
canonical `x = X Z^(p−2)`. -/
def compressCode (E : Ext Fp) : Nat :=
  (E.Y * E.Z ^ (p - 2)).val + 2 ^ 255 * ((E.X * E.Z ^ (p - 2)).val % 2)

/-- The encoding integer of an affine point. -/
def encodeAff (A : EdPt) : Nat := A.pt.y.val + 2 ^ 255 * (A.pt.x.val % 2)

/-- Canonical `y` leaves bit 255 clear, so setting it is an addition below `2^256`. -/
theorem val_lt (x : Fp) : x.val < 2 ^ 255 := Nat.lt_of_lt_of_le x.val_lt (by decide)

theorem compressCode_lt (E : Ext Fp) : compressCode E < 2 ^ 256 := by
  have := val_lt (E.Y * E.Z ^ (p - 2))
  have : (E.X * E.Z ^ (p - 2)).val % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold compressCode; omega

theorem compressCode_eq {E : Ext Fp} {A : EdPt} (h : Rep2 E A) : compressCode E = encodeAff A := by
  have hx : A.pt.x = E.X * E.Z ^ (p - 2) := by rw [← h.2]; rfl
  have hy : A.pt.y = E.Y * E.Z ^ (p - 2) := by rw [← h.2]; rfl
  rw [compressCode, encodeAff, hx, hy]

theorem encodePoint_eq (P : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint P = Spec.Ed25519.encodeInt (compressCode (ofSpec P)) := by
  have hx : (ofSpec P).X * (ofSpec P).Z ^ (p - 2) = toF (P.X * Spec.Ed25519.inv P.Z) := by
    rw [toF_mul, toF_inv]; rfl
  have hy : (ofSpec P).Y * (ofSpec P).Z ^ (p - 2) = toF (P.Y * Spec.Ed25519.inv P.Z) := by
    rw [toF_mul, toF_inv]; rfl
  rw [compressCode, hx, hy, val_toF, val_toF]
  rfl

/-- The specification's encoding of a point that represents `A`. -/
theorem encodePoint_rep {P : Spec.Ed25519.Point} {A : EdPt} (h : SpecRep P A) :
    Spec.Ed25519.encodePoint P = Spec.Ed25519.encodeInt (encodeAff A) := by
  rw [encodePoint_eq, compressCode_eq h.rep2]

end M0Crypto.Release.Ed25519Encode
