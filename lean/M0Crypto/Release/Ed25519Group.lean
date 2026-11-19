import M0Crypto.Release.Ed25519Curve

/-!
The points of the Ed25519 curve as an abelian group (`EdPt`), with the `Lean.Grind.IntModule`
structure, so that `grind` rearranges sums of points and core's `IntModule` lemmas
(`add_zsmul`, `mul_zsmul`, `neg_zsmul`, `zsmul_add`, …) apply to scalar multiplication.

`n • P` for `n : Nat` is `P + … + P` (`n` times, `nsmul_succ`); for `n : Int` a negative `n`
negates. The group law is `edAdd` of `Ed25519Curve` (RFC 8032 section 5.1.4), complete on the
curve, so every law here holds without side conditions.
-/

namespace M0Crypto.Release.Ed25519Group

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519Edwards (Point zero neg onCurve_zero onCurve_neg)

/-- A point of the Ed25519 curve. -/
@[ext] structure EdPt where
  /-- The affine point `(x, y)`. -/
  pt : Point Fp
  on : OnEd25519 pt

namespace EdPt

instance : Zero EdPt := ⟨⟨zero, onCurve_zero _ _⟩⟩
instance : Add EdPt := ⟨fun P Q => ⟨edAdd P.pt Q.pt, onEd25519_add P.on Q.on⟩⟩
instance : Neg EdPt := ⟨fun P => ⟨neg P.pt, onCurve_neg P.on⟩⟩
instance : Sub EdPt := ⟨fun P Q => P + -Q⟩

theorem pt_zero : (0 : EdPt).pt = zero := rfl
theorem pt_add (P Q : EdPt) : (P + Q).pt = edAdd P.pt Q.pt := rfl
theorem pt_neg (P : EdPt) : (-P).pt = neg P.pt := rfl

instance : AddCommGroup EdPt where
  add_zero P := EdPt.ext (edAdd_zero P.pt)
  add_comm P Q := EdPt.ext (edAdd_comm P.pt Q.pt)
  add_assoc P Q R := EdPt.ext (edAdd_assoc P.on Q.on R.on)
  neg_add_cancel P := EdPt.ext (by
    show edAdd (neg P.pt) P.pt = zero
    rw [edAdd_comm]
    exact edAdd_neg P.on)
  sub_eq_add_neg _ _ := rfl

/-- `n • P = P + … + P`. -/
def nsmulRec : Nat → EdPt → EdPt
  | 0, _ => 0
  | n + 1, P => nsmulRec n P + P

/-- `n • P` for an integer `n`. -/
def zsmulRec : Int → EdPt → EdPt
  | .ofNat n, P => nsmulRec n P
  | .negSucc n, P => -nsmulRec (n + 1) P

instance : SMul Nat EdPt := ⟨nsmulRec⟩
instance : SMul Int EdPt := ⟨zsmulRec⟩

open AddCommMonoid AddCommGroup

theorem zsmul_succ (n : Int) (P : EdPt) : zsmulRec (n + 1) P = zsmulRec n P + P := by
  rcases n with n | (_ | n)
  · rfl
  · show (0 : EdPt) = -(0 + P) + P
    rw [zero_add, neg_add_cancel]
  · show -nsmulRec (n + 1) P = -(nsmulRec (n + 1) P + P) + P
    rw [neg_add, add_assoc, neg_add_cancel, add_zero]

theorem zsmul_pred (n : Int) (P : EdPt) : zsmulRec (n - 1) P = zsmulRec n P + -P := by
  have h := zsmul_succ (n - 1) P
  rw [Int.sub_add_cancel] at h
  rw [h, add_assoc, add_neg_cancel, add_zero]

theorem zsmul_add (n m : Int) (P : EdPt) :
    zsmulRec (n + m) P = zsmulRec n P + zsmulRec m P := by
  rcases m with m | m
  · induction m with
    | zero => show zsmulRec (n + 0) P = zsmulRec n P + 0; rw [Int.add_zero, add_zero]
    | succ m ih =>
      have e : n + Int.ofNat (m + 1) = (n + Int.ofNat m) + 1 := by
        simp only [Int.ofNat_eq_natCast]; omega
      rw [e, zsmul_succ, ih, add_assoc]
      rfl
  · induction m with
    | zero =>
      have e : n + Int.negSucc 0 = n - 1 := by simp only [Int.negSucc_eq]; omega
      rw [e, zsmul_pred]
      show _ = zsmulRec n P + -(0 + P)
      rw [zero_add]
    | succ m ih =>
      have e : n + Int.negSucc (m + 1) = (n + Int.negSucc m) - 1 := by
        simp only [Int.negSucc_eq]; omega
      have e' : Int.negSucc (m + 1) = Int.negSucc m - 1 := by simp only [Int.negSucc_eq]; omega
      rw [e, zsmul_pred, ih, e', zsmul_pred, add_assoc]

instance : IntModule EdPt where
  zero_zsmul _ := rfl
  one_zsmul P := show 0 + P = P from zero_add P
  add_zsmul n m P := zsmul_add n m P
  zsmul_natCast_eq_nsmul _ _ := rfl

theorem nsmul_succ (n : Nat) (P : EdPt) : (n + 1) • P = n • P + P := rfl

theorem two_nsmul (P : EdPt) : (2 : Nat) • P = P + P := by
  show (0 + P) + P = P + P
  rw [zero_add]

/-- Doubling as an integer multiple. -/
theorem two_zsmul (n : Int) (P : EdPt) : (2 * n) • P = n • P + n • P := by
  rw [show 2 * n = n + n by omega, IntModule.add_zsmul]

end EdPt

end M0Crypto.Release.Ed25519Group
