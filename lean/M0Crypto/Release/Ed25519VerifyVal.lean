import M0Crypto.Release.Ed25519VerifyBlocks
import M0Crypto.Release.Ed25519DsmBlocks
import M0Crypto.Release.Ed25519ScalarMul

/-!
# The values of `sc_wnaf` and `ge_dsm` in `m0c_ed25519_verify`

* `wnaf_bytes`, `wnafV`: `m0c_sc_wnaf`'s post (`Ed25519ScWnaf.wnR`) leaves the 256 bytes
  `wnafBytes w k`, the signed bytes of the windowed NAF `wnaf w k` of its scalar;
* `digOf_wnaf`: the digits `m0c_ge_dsm` reads from those bytes (`Ed25519DsmBlocks.digOf`) are
  `wnaf w k`;
* `verify_digits`: those digits at verify's call are of width `5` (of `s`) and `3` (of `h`);
* `dsm_digits`: the double-scalar loop over the digits read from the bytes of `wnaf 5 s` and
  `wnaf 3 h`, from the top-digit scan, is `[s]B − [h]A` for `s, h < L` (`dsmTop_congr`,
  `dsmRun_congr`: the loop reads only the 256 digits);
* `sb_rep`, `sb_hyp`: `p2` values of that loop's point are the `SB` that `verify_tests` and
  `verdict_r0` take, with `A` decoded from `pk` and `h = k mod L`.
-/

namespace M0Crypto.Release.Ed25519VerifyVal

open M0Crypto.Armv6M (Word Mem)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519WnafDigits (wnaf wnaf_spec Digit)
open M0Crypto.Release.Ed25519Wnaf (dsmRun dsmStep)
open M0Crypto.Release.Ed25519ScalarMul (dsmTop dsmRun_wnaf)
open M0Crypto.Release.Ed25519DsmBlocks (digOf)
open M0Crypto.Release.Ed25519Group M0Crypto.Release.Ed25519Bridge M0Crypto.Release.Ed25519Formulas
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519EdwardsExtended (Ext)
open M0Crypto.Release.Ed25519GeProg (Rep2V fI)
open M0Crypto.Spec.Ed25519 (decodeInt L)

/-! ## The digits -/

/-- The 256 signed bytes of the width-`w` digits of `k`. -/
def wnafBytes (w k : Nat) : List (BitVec 8) := (List.range 256).map fun i => BitVec.ofInt 8 (wnaf w k i)

/-- **`sc_wnaf`'s post as bytes.** -/
theorem wnaf_bytes {m : Mem} {a : Word} {w k : Nat}
    (h : ∀ i < 256, m (a + BitVec.ofNat 32 i) = BitVec.ofInt 8 (wnaf w k i)) : bytesAt m a 256 = wnafBytes w k :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `sc_wnaf`'s semantics on its view: the digit bytes of the scalar's value. -/
def wnafV (w : Nat) : List Ed25519CallProg.V → List Ed25519CallProg.V
  | [.b l] => [.b (wnafBytes w (decodeInt l))]
  | _ => [.none]

theorem toInt_ofInt {d : Int} (h1 : -128 ≤ d) (h2 : d < 128) : (BitVec.ofInt 8 d).toInt = d := by
  rw [BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> omega

/-- **The digits `ge_dsm` reads** from the bytes of `wnaf w k` are `wnaf w k`. -/
theorem digOf_wnaf {m : Mem} {p : Word} {w k : Nat} (hw : 2 ≤ w) (hw8 : w ≤ 8) (hk : k < 2 ^ 255)
    (h : bytesAt m p 256 = wnafBytes w k) : ∀ i < 256, digOf m p i = wnaf w k i := by
  intro i hi
  have hb := congrArg (fun l => l[i]?) h
  simp only [bytesAt, wnafBytes, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at hb
  obtain ⟨h1, h2⟩ := Digit.byte hw8 ((wnaf_spec w k hw hk).2.1 i)
  rw [digOf, hb, toInt_ofInt h1 h2]

/-- **The digit bounds at `m0c_ed25519_verify`'s `ge_dsm` call**: the digits read from the bytes
of `wnaf 5 s` and `wnaf 3 h` (`sc_wnaf`'s outputs, `wnaf_bytes`), `s, h < L`, are of width `5` and `3`. -/
theorem verify_digits {m : Mem} {p1 p2 : Word} {s h : Nat} (hs : s < L) (hh : h < L)
    (b1 : bytesAt m p1 256 = wnafBytes 5 s) (b2 : bytesAt m p2 256 = wnafBytes 3 h) :
    ∀ i < 256, Digit 5 (digOf m p1 i) ∧ Digit 3 (digOf m p2 i) := fun i hi => by
  have L5 := Nat.lt_trans hs Ed25519ScalarMul.L_lt
  have L3 := Nat.lt_trans hh Ed25519ScalarMul.L_lt
  rw [digOf_wnaf (by decide) (by decide) L5 b1 i hi, digOf_wnaf (by decide) (by decide) L3 b2 i hi]
  exact ⟨(wnaf_spec 5 s (by decide) L5).2.1 i, (wnaf_spec 3 h (by decide) L3).2.1 i⟩

/-! ## The loop reads only the 256 digits -/

theorem dsmTop_congr {sd hd sd' hd' : Nat → Int} :
    ∀ k, (∀ i < k, sd i = sd' i ∧ hd i = hd' i) → dsmTop sd hd k = dsmTop sd' hd' k
  | 0, _ => rfl
  | k + 1, h => by
    unfold dsmTop
    rw [(h k (by omega)).1, (h k (by omega)).2, dsmTop_congr k fun i hi => h i (by omega)]

theorem dsmRun_congr {sd hd sd' hd' : Nat → Int} (A : EdPt) :
    ∀ k R, (∀ i < k, sd i = sd' i ∧ hd i = hd' i) → dsmRun sd hd A k R = dsmRun sd' hd' A k R
  | 0, _, _ => rfl
  | k + 1, R, h => by
    simp only [dsmRun, dsmStep, (h k (by omega)).1, (h k (by omega)).2]
    exact dsmRun_congr A k _ fun i hi => h i (by omega)

/-- **`ge_dsm` over the digits of `s` and `h`**: the loop over the digits read from the bytes of
`wnaf 5 s` and `wnaf 3 h`, from the top-digit scan, is `[s]B − [h]A`. -/
theorem dsm_digits {m : Mem} {p1 p2 : Word} {s h : Nat} (A : EdPt) (hs : s < L) (hh : h < L)
    (b1 : bytesAt m p1 256 = wnafBytes 5 s) (b2 : bytesAt m p2 256 = wnafBytes 3 h) :
    dsmRun (digOf m p1) (digOf m p2) A (dsmTop (digOf m p1) (digOf m p2) 256) 0 = (s : Int) • Bpt - (h : Int) • A := by
  have L5 := Nat.lt_trans hs Ed25519ScalarMul.L_lt
  have L3 := Nat.lt_trans hh Ed25519ScalarMul.L_lt
  have e : ∀ i < 256, digOf m p1 i = wnaf 5 s i ∧ digOf m p2 i = wnaf 3 h i := fun i hi =>
    ⟨digOf_wnaf (by decide) (by decide) L5 b1 i hi, digOf_wnaf (by decide) (by decide) L3 b2 i hi⟩
  have ht := dsmTop_congr 256 e
  rw [ht, dsmRun_congr A _ 0 fun i hi => e i (by
    have := (Ed25519ScalarMul.dsmTop_spec (wnaf 5 s) (wnaf 3 h) 256).1; omega)]
  exact dsmRun_wnaf A hs hh

/-! ## `SB` for the verdict -/

/-- **The loop's `p2` values represent `[s]B − [h]A`.** -/
theorem sb_rep {m : Mem} {p1 p2 : Word} {s h : Nat} {A : EdPt} (hs : s < L) (hh : h < L)
    (b1 : bytesAt m p1 256 = wnafBytes 5 s) (b2 : bytesAt m p2 256 = wnafBytes 3 h) {vs : List Ed25519CallProg.V}
    (hv : Rep2V vs (dsmRun (digOf m p1) (digOf m p2) A (dsmTop (digOf m p1) (digOf m p2) 256) 0)) :
    Rep2V vs ((s : Int) • Bpt - (h : Int) • A) := by
  rwa [dsm_digits A hs hh b1 b2] at hv

/-- **`verify_tests`' hypothesis on `SB`**: when, for the decoded `R` and `A'`, some `A`
represented by `A'` has `p2` values `x, y, z` of `[s]B − [k mod L]A` whenever `s < L`, the
point `(x : y : z)` is the `SB` that `verify_tests` and `verdict_r0` take. -/
theorem sb_hyp {sig M Apk : List Spec.Ed25519.Byte} {x y z : Int}
    (h : ∀ R A', Spec.Ed25519.decodePoint (sig.take 32) = some R → Spec.Ed25519.decodePoint Apk = some A' →
      ∃ A : EdPt, SpecRep A' A ∧ (decodeInt (sig.drop 32) < L →
        Rep2V [.f x, .f y, .f z] ((decodeInt (sig.drop 32) : Int) • Bpt -
          ((decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M)) % L : Nat) : Int) • A))) :
    ∀ R A', Spec.Ed25519.decodePoint (sig.take 32) = some R → Spec.Ed25519.decodePoint Apk = some A' →
      ∃ A : EdPt, SpecRep A' A ∧ (decodeInt (sig.drop 32) < L →
        Rep2 (⟨fI x, fI y, fI z, 0⟩ : Ext Fp) ((decodeInt (sig.drop 32) : Int) • Bpt -
          ((decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M)) % L : Nat) : Int) • A)) := by
  intro R A' hR hA
  obtain ⟨A, hr, hs⟩ := h R A' hR hA
  refine ⟨A, hr, fun hl => ?_⟩
  obtain ⟨x', y', z', he, hrep⟩ := hs hl
  simp only [List.cons.injEq, Ed25519CallProg.V.f.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact hrep

end M0Crypto.Release.Ed25519VerifyVal
