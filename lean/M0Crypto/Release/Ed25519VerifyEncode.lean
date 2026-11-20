import M0Crypto.Release.Ed25519Verify
import M0Crypto.Release.Ed25519Encode
import M0Crypto.Release.Ed25519CallProgBytes

namespace M0Crypto.Release.Ed25519VerifyEncode

open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge M0Crypto.Release.Ed25519Decode
open M0Crypto.Release.Ed25519Encode M0Crypto.Release.Ed25519Verify
open M0Crypto.Release.Ed25519CallProg (encodeInt_decodeInt decodeInt_encodeInt)
open M0Crypto.Release.Ed25519PrimeCert (p)
open M0Crypto.Spec.Ed25519 (Byte decodeInt encodeInt decodePoint)

private theorem decode_canonical {l : List Byte} {R : M0Crypto.Spec.Ed25519.Point}
    (h : decodePoint l = some R) : decodeInt l % 2^255 < p := by
  have e := decodePoint_eq l
  rw [h, Option.map_some] at e
  apply Nat.lt_of_not_le
  intro hBad
  unfold decodeCode at e
  rw [ite_eq_left hBad] at e
  exact absurd e (by simp)

/-- The encoding checks performed before hashing. The remaining encodings are
    checked by comparing against the canonical encoding of the computed point. -/
def earlyReject (l : List Byte) : Prop :=
  let y := decodeInt l % 2^255
  let sign := decodeInt l / 2^255 % 2
  p ≤ y ∨ sign = 1 ∧ (y = 1 ∨ y = p - 1)

private theorem signed_identity_reject : decodeCode 1 1 = none := by decide +kernel
private theorem signed_order_two_reject : decodeCode (p - 1) 1 = none := by decide +kernel

theorem decode_of_earlyReject {l : List Byte} (h : earlyReject l) : decodePoint l = none := by
  have hd := decodePoint_eq l
  have hCode : decodeCode (decodeInt l % 2^255) (decodeInt l / 2^255 % 2) = none := by
    rcases h with hy | ⟨hs, hy | hy⟩
    · simp only [decodeCode, hy, ↓reduceIte]
    · rw [hs, hy, signed_identity_reject]
    · rw [hs, hy, signed_order_two_reject]
  rw [hCode] at hd
  cases h : decodePoint l with
  | none => rfl
  | some r => simp [h] at hd

theorem verify_of_earlyReject {sig msg pk : List Byte} (h : earlyReject (sig.take 32)) :
    M0Crypto.Spec.Ed25519.verify sig msg pk = false :=
  verify_of_decode_R_none (decode_of_earlyReject h)

/-- The forbidden encodings have all-zero or all-ones middle bytes. This form
    matches the endpoint tests and the middle-byte scan in the Thumb routine. -/
theorem earlyReject_of_byte_pattern (lo hi : Byte) (mid : List Byte)
    (h : (hi = 128 ∧ lo = 1 ∧ mid = List.replicate 30 0) ∨
      ((hi = 127 ∨ hi = 255) ∧ 237 ≤ lo.toNat ∨ hi = 255 ∧ lo = 236) ∧
        mid = List.replicate 30 255) :
    earlyReject (lo :: (mid ++ [hi])) := by
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨⟨hHi,hLo⟩ | ⟨rfl,rfl⟩,rfl⟩
  · unfold earlyReject
    decide +kernel

  · have hN : decodeInt (lo :: (List.replicate 30 255 ++ [hi])) =
        lo.toNat + 256 * (256^30 - 1 + 256^30 * hi.toNat) := by
      rw [Ed25519Bytes.decodeInt_cons,Ed25519CallProg.decodeInt_append,List.length_replicate]
      have hRep : decodeInt (List.replicate 30 (255 : Byte)) = 256^30 - 1 := by decide +kernel
      rw [hRep]
      have hSingle : decodeInt [hi] = hi.toNat := by simp [decodeInt]
      rw [hSingle]
      exact Nat.add_comm _ _
    have hLoMax := lo.isLt
    unfold earlyReject
    simp only [hN]
    left
    rcases hHi with rfl | rfl <;> unfold p <;>
      simp only [show (127 : Byte).toNat = 127 from rfl, show (255 : Byte).toNat = 255 from rfl] <;> omega
  · unfold earlyReject
    decide +kernel

/-- Select the byte expected at every middle position of a forbidden encoding. -/
def earlyMask (lo hi : Byte) : Option Byte :=
  if hi = 255 ∨ hi = 127 then
    if 237 ≤ lo.toNat ∨ hi = 255 ∧ lo = 236 then some 255 else none
  else if hi = 128 ∧ lo = 1 then some 0 else none

theorem earlyMask_sound {lo hi byte : Byte} (h : earlyMask lo hi = some byte) :
    earlyReject (lo :: (List.replicate 30 byte ++ [hi])) := by
  unfold earlyMask at h
  split at h
  · rename_i hHigh
    split at h
    · rename_i hLow
      obtain rfl := Option.some.inj h
      apply earlyReject_of_byte_pattern
      right
      refine ⟨?_, rfl⟩
      rcases hLow with hLo | hLo
      · exact .inl ⟨hHigh.elim Or.inr Or.inl,hLo⟩
      · exact .inr hLo
    · cases h

  · split at h
    · rename_i hIdentity
      obtain rfl := Option.some.inj h
      exact earlyReject_of_byte_pattern _ _ _ (.inl ⟨hIdentity.1,hIdentity.2,rfl⟩)
    · cases h

/-- A loop that observes the selected byte at each of the 30 middle positions
    establishes that the original encoding will be rejected by decoding. -/
theorem scan_earlyReject {lo hi byte : Byte} {mid : List Byte}
    (hm : earlyMask lo hi = some byte) (hlen : mid.length = 30)
    (hscan : ∀ i (hi : i < mid.length), mid[i] = byte) :
    earlyReject (lo :: (mid ++ [hi])) := by
  have hRep : mid = List.replicate 30 byte := by
    apply List.ext_getElem
    · simpa using hlen
    · intro i hi _
      rw [hscan i hi,List.getElem_replicate]
  rw [hRep]
  exact earlyMask_sound hm

/-- The implementation scans positions 30 through 1, excluding the endpoints. -/
def earlyScan (read : Nat → Byte) (byte : Byte) : Nat → Bool
  | 0 => true
  | n + 1 => (read (n + 1) == byte) && earlyScan read byte n

theorem earlyScan_iff (read : Nat → Byte) (byte : Byte) (n : Nat) :
    earlyScan read byte n = true ↔ ∀ i, 1 ≤ i → i ≤ n → read i = byte := by
  induction n with
  | zero =>
    simp only [earlyScan,true_iff]
    intro i h₁ h₂
    omega
  | succ n ih =>
    rw [earlyScan,Bool.and_eq_true,beq_iff_eq,ih]
    constructor
    · rintro ⟨hn, h⟩ i h₁ h₂
      by_cases hi : i = n + 1
      · simpa only [hi] using hn
      · exact h i h₁ (by omega)
    · intro h
      exact ⟨h (n+1) (by omega) (by omega), fun i hi hn => h i hi (by omega)⟩

private theorem encoding_lt (A : EdPt) : encodeAff A < 2^256 := by
  have hy := Ed25519Encode.val_lt A.pt.y
  have hx := Nat.mod_lt A.pt.x.val (by decide : 0 < 2)
  unfold encodeAff
  omega

private theorem tags (A : EdPt) :
    encodeAff A % 2^255 = A.pt.y.val ∧ encodeAff A / 2^255 % 2 = A.pt.x.val % 2 := by
  have hy := Ed25519Encode.val_lt A.pt.y
  have hx := Nat.mod_lt A.pt.x.val (by decide : 0 < 2)
  unfold encodeAff
  omega

/-- Canonical Ed25519 decoding represents `A` exactly on the 32-byte encoding of `A`.
    Equality is on the original bytes, including the sign bit. -/
theorem decode_iff_encoding (l : List Byte) (hLen : l.length = 32) (A : EdPt) :
    (∃ R, decodePoint l = some R ∧ SpecRep R A) ↔ l = encodeInt (encodeAff A) := by
  constructor
  · rintro ⟨R,hR,hA⟩
    have hY := decode_canonical hR
    have hS : decodeInt l / 2^255 % 2 < 2 := Nat.mod_lt _ (by decide)
    have hD := decodePoint_eq l
    rw [hR,Option.map_some] at hD
    obtain ⟨X,hCurve,hSign,hCoord⟩ := (decodeCode_eq_some_iff hY hS).1 hD.symm
    let P : EdPt := ⟨_,hCurve⟩
    have hRep : Rep (ofSpec R) P := by rw [hCoord]; exact rep_ofPoint P
    have hEq : A = P := EdPt.ext (hA.2.symm.trans hRep.2)
    have hy : P.pt.y.val = decodeInt l % 2^255 := val_toF_of_lt hY
    have hx : P.pt.x.val % 2 = decodeInt l / 2^255 % 2 := hSign
    have hN := Ed25519Bytes.decodeInt_lt l
    rw [hLen] at hN
    have hInt : decodeInt l = encodeAff A := by
      rw [hEq,encodeAff,hy,hx]
      omega
    rw [← hInt,encodeInt_decodeInt hLen]
  · intro hL
    have hInt : decodeInt l = encodeAff A := by
      rw [hL,decodeInt_encodeInt,Nat.mod_eq_of_lt (encoding_lt A)]
    have hD := decodePoint_eq l
    rw [hInt,(tags A).1,(tags A).2] at hD
    have hCode : decodeCode A.pt.y.val (A.pt.x.val % 2) = some (Ext.ofPoint A.pt) := by
      refine (decodeCode_eq_some_iff A.pt.y.val_lt (Nat.mod_lt _ (by decide))).2 ⟨A.pt.x,?_,rfl,?_⟩
      · rw [toF_val]; exact A.on
      · rw [toF_val]; rfl
    rw [hCode] at hD
    cases hR : decodePoint l with
    | none => rw [hR] at hD; cases hD
    | some R =>
      rw [hR, Option.map_some] at hD
      refine ⟨R,rfl,?_⟩
      unfold SpecRep
      rw [Option.some.inj hD]
      exact rep_ofPoint A

private theorem comp_iff {l : List Byte} {R : M0Crypto.Spec.Ed25519.Point} {SB : Ext Fp} {A : EdPt}
    (hLen : l.length = 32) (hR : decodePoint l = some R) (hSB : Rep2 SB A) :
    l = encodeInt (compressCode SB) ↔ eqCode SB (ofSpec R) = true := by
  obtain ⟨Rpt,hRp,hZ⟩ := specRep_of_decode hR
  have hCompare := Rep2.eq_iff hSB hRp.rep2
  simp only [hZ,Lean.Grind.Semiring.mul_one] at hCompare
  rw [eqCode,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq,← hCompare,
    compressCode_eq hSB,← decode_iff_encoding l hLen A]
  constructor
  · rintro ⟨R',hR',hR'A⟩
    rw [hR,Option.some.injEq] at hR'
    subst R'
    exact EdPt.ext (hR'A.2.symm.trans hRp.2)
  · intro hPoint
    rw [hPoint]
    exact ⟨R,hR,hRp⟩

/-- Once `A` has decoded and `SB` is the double-scalar result, comparing the
    canonical encoding of `SB` to the original `R` bytes gives the same verdict.
    The check on `S` guards the double-scalar result and the comparison. -/
theorem verify_encode_compare {sig msg key : List Byte} {P : M0Crypto.Spec.Ed25519.Point}
    (hLen : (sig.take 32).length = 32) (hA : decodePoint key = some P)
    {A : EdPt} (hAr : SpecRep P A) {SB : Ext Fp}
    (hSB : decodeInt (sig.drop 32) < M0Crypto.Spec.Ed25519.L →
      Rep2 SB ((decodeInt (sig.drop 32) : Int) • Bpt -
        ((decodeInt (M0Crypto.Spec.Sha512.sha512 (sig.take 32 ++ key ++ msg))
          % M0Crypto.Spec.Ed25519.L : Nat) : Int) • A)) :
    M0Crypto.Spec.Ed25519.verify sig msg key =
      (decide (decodeInt (sig.drop 32) < M0Crypto.Spec.Ed25519.L) &&
        decide (sig.take 32 = encodeInt (compressCode SB))) := by
  by_cases hS : decodeInt (sig.drop 32) < M0Crypto.Spec.Ed25519.L
  · have hr := hSB hS
    cases hR : decodePoint (sig.take 32) with
    | none =>
      rw [verify_of_decode_R_none hR]
      have hComparison : sig.take 32 ≠ encodeInt (compressCode SB) := by
        intro e
        rw [compressCode_eq hr] at e
        obtain ⟨R,hGood,_⟩ := (decode_iff_encoding _ hLen _).2 e
        rw [hR] at hGood
        cases hGood
      simp [hComparison]
    | some R =>
      rw [verify_eq hR hA hAr hSB]
      simp only [hS, decide_true, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact (comp_iff hLen hR hr).symm
  · cases hR : decodePoint (sig.take 32) with
    | none => rw [verify_of_decode_R_none hR]; simp [hS]
    | some R => rw [verify_eq hR hA hAr hSB]; simp [hS]

end M0Crypto.Release.Ed25519VerifyEncode
