import M0Crypto.Release.Ed25519FragC
import M0Crypto.Release.Ed25519Decode
import M0Crypto.Release.Ed25519ScReduceProg

/-!
# `m0c_ge_decompress`'s values in `F_p`

`Ed25519Decode.decodeCode` is the routine's computation in the generator's order, and
`decodePoint_eq` equates it with RFC 8032's decoding. This module links the program's values to
it: field values `.f z` are `fI z` in `F_p`; `fe_pow` of kind `1` is the `(p − 5)/8` power
(`pow_val`); `fe_eq`'s status is `0` exactly when the field values agree (`eq_iff`); `fe_canon`'s
bytes are the value's canonical form (`canon_val`), whose words decide `x = 0` (`zero_iff`) and
the parity (`par_eq`); the code constants `m0c_ed_zero`, `_one`, `_d` and `_sqrtm1`, contiguous
from `m0c_ed_zero`, are `0`, `1`, `d` and `sqrt(−1)` in both builds (`consts`, `const_fe`).
-/

namespace M0Crypto.Release.Ed25519DecompressVal

open M0Crypto.Armv6M (Word Mem read32 slot)
open M0Crypto.Thumb (CodeAt)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg (fI fI_mul fI_nat fI_modP fI_emod)
open M0Crypto.Release.Ed25519FePow (powE)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519PrimeCert (p)
open M0Crypto.Spec.Ed25519 (decodeInt encodeInt)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ed_zero)
open Lean.Grind (Ring)

/-! ## Field operations -/

theorem fI_pow (x : Int) (n : Nat) : fI (x ^ n) = fI x ^ n := Ring.intCast_pow x n

theorem p58 : powE 1 = (p - 5) / 8 := by decide

/-- **`fe_pow` of kind `1`** is the `(p − 5)/8` power. -/
theorem pow_val (x : Int) : fI (x ^ powE 1) = fI x ^ ((p - 5) / 8) := by rw [fI_pow, p58]

/-- A memory value read modulo `p` as its field value. -/
theorem fI_of {a : Nat} {x : Int} (h : ModP a x) : fI x = toF a := by rw [← fI_modP h, fI_nat]

/-- **`fe_eq`'s status** is `0` exactly when the field values agree. -/
theorem eq_iff {a b : Nat} {x y : Int} (ha : ModP a x) (hb : ModP b y) : a % pN = b % pN ↔ fI x = fI y := by
  rw [fI_of ha, fI_of hb, toF_eq_iff]; rfl

/-! ## The canonical form -/

theorem pN_eq : (pN : Int) = Field25519Congr.p := by decide

/-- The canonical representative is the field value's. -/
theorem canon_nat (x : Int) : (x % (pN : Int)).toNat = (fI x).val := by
  have h0 : 0 ≤ x % (pN : Int) := Int.emod_nonneg _ (by decide)
  have hl : x % (pN : Int) < (pN : Int) := Int.emod_lt_of_pos _ (by decide)
  have e : fI x = toF (x % (pN : Int)).toNat := by
    rw [← fI_nat, Int.toNat_of_nonneg h0, pN_eq, fI_emod]
  rw [e, Ed25519Decode.val_toF_of_lt (by have : (pN : Int) = (p : Int) := rfl; omega)]

/-- **`fe_canon`'s bytes** hold the field value. -/
theorem canon_val (x : Int) : decodeInt (encodeInt (x % (pN : Int)).toNat) = (fI x).val := by
  rw [decodeInt_encodeInt, canon_nat, Nat.mod_eq_of_lt (Nat.lt_trans (fI x).val_lt (by decide))]

/-- A value is `0` exactly when its 8 words are. -/
theorem zero_iff (m : Mem) (a : Word) : feVal m a = 0 ↔ ∀ i < 8, (read32 m (slot a i)).toNat = 0 := by
  rw [Field25519Facts.feVal_psum]
  simp only [Field25519Facts.psum]
  constructor
  · intro h i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro h
    have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
    have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
    omega

/-- The parity of a value is that of its first word. -/
theorem par_eq (m : Mem) (a : Word) : feVal m a % 2 = (read32 m (slot a 0)).toNat % 2 := by
  rw [Field25519Facts.feVal_psum]
  simp only [Field25519Facts.psum]
  omega

/-! ## The code constants -/

/-- `m0c_ed_zero`, `_one`, `_d` and `_sqrtm1` from `m0c_ed_zero`, with their values. -/
def cZero : Nat := 0
def cOne : Nat := 32
def cD : Nat := 64
def cSqrt : Nat := 128

/-- The constants' 32 bytes from `m0c_ed_zero + e`. -/
def cBytes (b : Build) (e : Nat) : List (BitVec 8) := (b.bytes.drop (ed_zero + e)).take 32

/-- **The constants** in both builds; the four lie in the 160 bytes from `m0c_ed_zero`. -/
theorem consts (b : Build) :
    decodeInt (cBytes b cZero) = 0 ∧ decodeInt (cBytes b cOne) = 1 ∧
    decodeInt (cBytes b cD) = Spec.Ed25519.d ∧
    decodeInt (cBytes b cSqrt) = 19681161376707505956807079304988542015446066515923890162744021073123829784752 ∧
    ed_zero + 160 ≤ b.bytes.length := by
  cases b <;> decide +kernel

theorem toF_sqrt : toF 19681161376707505956807079304988542015446066515923890162744021073123829784752 = sqrtM1 := by
  rw [sqrtM1_eq]; rfl

/-- A constant's value read from memory holding the code at `base`. -/
theorem const_fe {m : Mem} {base : Word} (b : Build) (h : CodeAt m base b.bytes) {e : Nat} (he : e + 32 ≤ 160) :
    feVal m (base + BitVec.ofNat 32 ed_zero + BitVec.ofNat 32 e) = decodeInt (cBytes b e) := by
  rw [← Ed25519GeCompressProg.dec_fe, Thumb.ofNat_add_assoc,
    Ed25519ScReduceProg.code_bytes h (by have := (consts b).2.2.2.2; omega)]
  rfl

/-- **The constants as field values.** -/
theorem const_vals {m : Mem} {base : Word} (b : Build) (h : CodeAt m base b.bytes) :
    toF (feVal m (base + BitVec.ofNat 32 ed_zero + BitVec.ofNat 32 cZero)) = 0 ∧
    toF (feVal m (base + BitVec.ofNat 32 ed_zero + BitVec.ofNat 32 cOne)) = 1 ∧
    toF (feVal m (base + BitVec.ofNat 32 ed_zero + BitVec.ofNat 32 cD)) = d ∧
    toF (feVal m (base + BitVec.ofNat 32 ed_zero + BitVec.ofNat 32 cSqrt)) = sqrtM1 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := consts b
  rw [const_fe b h (e := cZero) (by decide), const_fe b h (e := cOne) (by decide),
    const_fe b h (e := cD) (by decide), const_fe b h (e := cSqrt) (by decide), h0, h1, h2, h3, toF_d, toF_sqrt]
  exact ⟨rfl, rfl, rfl, rfl⟩

end M0Crypto.Release.Ed25519DecompressVal
