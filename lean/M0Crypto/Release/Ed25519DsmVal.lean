import M0Crypto.Release.Ed25519DsmProg
import M0Crypto.Release.Ed25519MulBaseVal
import M0Crypto.Release.Ed25519VerifyVal
import M0Crypto.Release.Ed25519MulBaseTab
import M0Crypto.Release.Ed25519DecompressOut

/-!
# `m0c_ge_dsm`'s values in its loop

A pass of the loop at position `i` (`emit_dsm`) with the digits `hd` of `h` and `sd` of `s`:
`ge_dbl` of `R` into `T`, back to `p3` (some digit nonzero) or `p2`; for `hd ≠ 0`, `signed_add`
of `AI[|hd| / 2]` with `hd`'s sign, back to `p3` (`sd ≠ 0`) or `p2`; for `sd ≠ 0`, `signed_add`
of `m0c_ed_odd_b[|sd| / 2]` with `sd`'s sign, back to `p2`. `passR` lists its updates; the
segments' static runs (`Prog.lin`) are these lists (`dbl_lin`, `cv_lin`, `sa_lin`, `sb_lin`). Over them:

* `pass_val`: from `p2` values of `A` at `R`, `p2` values of `dsmStep` at `R`, with `AI[k]` the
  cached `[2k + 1](−A₀)` and `odd_b[k]` the Niels `[2k + 1]B`; the table `AI` stays;
* `runs_val`: the passes of the positions `k − 1, …, 0` follow `dsmRun`;
* `loop_val`: over the digits read from the bytes of `wnaf 5 s` and `wnaf 3 h`, from the
  top-digit scan and `p2` values of the identity, `p2` values of `[s]B − [h]A₀`;
* `pre_val`, `id_val`, `end_val`: under the callees' values `dsV`, the prologue (`pre_lin`)
  fills `AI` with the cached `−A₀` and `[3](−A₀)` from `A₀`'s values, `set_identity` gives `p2`
  values of `0` at `R`, the epilogue copies `R`'s `X, Y, Z` to `out`;
* `k_ok`, `ob_ok`: the zero, `2 d` and `m0c_ed_odd_b` that these read are the code's.
-/

namespace M0Crypto.Release.Ed25519DsmVal

open M0Crypto.Armv6M (Word Reg Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519FragC (fresC)
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519MulBaseVal (frR flOf runR_frag)
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Release.Ed25519Bridge (Bpt)
open M0Crypto.Release.Ed25519Wnaf (dsmStep dsmRun)
open M0Crypto.Release.Ed25519WnafDigits (Digit)
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519DsmBlocks (digOf)
open M0Crypto.Release.Ed25519VerifyVal (wnafBytes sb_rep)
open M0Crypto.Spec.Ed25519 (L decodeInt)
open M0Crypto.Release.Ed25519ScalarMul (dsmTop)
open M0Crypto.Release.Ed25519Formulas (d2)
open M0Crypto.Release.Ed25519DecompressOut (keeps run_keep)

/-! ## The updates -/

/-- The fragments' updates. -/
def dblR : List (ROp DS DB) := frR DS.f (flOf dblF)
def cvR (withT : Bool) : List (ROp DS DB) := frR DS.f (flOf (p3F withT))

/-- `signed_add`'s resolved fragments: over `AI[k]`, over `odd_b[k]`, with sign `s`. -/
def saL (k s : Nat) : FL := ((fresC dsGeo (saSt k s) saF).map Prod.fst).getD []
def sbL (k s : Nat) : FL := ((fresC dsGeo (sbSt k s) sbF).map Prod.fst).getD []

/-- A digit's sign bit. -/
def sgn (d : Int) : Nat := if d < 0 then 1 else 0

/-- **The updates of a pass** with the digits `hd` of `h` and `sd` of `s`. -/
def passR (hd sd : Int) : List (ROp DS DB) :=
  dblR ++ cvR (hd != 0 || sd != 0) ++
    (if hd = 0 then [] else frR DS.f (saL (hd.natAbs / 2) (sgn hd)) ++ cvR (sd != 0)) ++
    (if sd = 0 then [] else frR DS.f (sbL (sd.natAbs / 2) (sgn sd)) ++ cvR false)

/-- The passes of the positions `k − 1, …, 0`. -/
def runsR (hd sd : Nat → Int) : Nat → List (ROp DS DB)
  | 0 => []
  | k + 1 => passR (hd k) (sd k) ++ runsR hd sd k

/-- **The segments' static runs are these updates**, at the states of their first pass. -/
theorem dbl_lin : (segDbl.lin dsS dbS dsGeo (rs s1)).map Prod.fst = some dblR := by decide +kernel

theorem cv_lin : (segP3.lin dsS dbS dsGeo (rs sD)).map Prod.fst = some (cvR true) ∧
    (segP2.lin dsS dbS dsGeo (rs sD)).map Prod.fst = some (cvR false) := ⟨by decide +kernel, by decide +kernel⟩

theorem sa_lin : ∀ k < 2, ∀ s < 2, (segSA.lin dsS dbS dsGeo (saSt k s)).map Prod.fst = some (frR DS.f (saL k s)) := by
  decide +kernel

theorem sb_lin : ∀ k < 8, ∀ s < 2, (segSB.lin dsS dbS dsGeo (sbSt k s)).map Prod.fst = some (frR DS.f (sbL k s)) := by
  decide +kernel

/-! ## The fragments' terms -/

def R3 : List Loc := rLocs.take 3

/-- The table `AI`'s eight field elements. -/
def aiLocs : List Loc := (List.range 8).map fun j => .fr (oAI + 32 * j)

/-- Entry `k` of `AI`. -/
def aiE (k : Nat) : List Loc := [.fr (oAI + 128 * k), .fr (oAI + 128 * k + 32), .fr (oAI + 128 * k + 64), .fr (oAI + 128 * k + 96)]

theorem dbl_terms : tLocs.map (symL tm0 (flOf dblF)) = dblT (frL oR) (frL (oR + 32)) (frL (oR + 64)) := by
  decide

theorem p3_terms : rLocs.map (symL tm0 (flOf (p3F true))) = p3T true (frL oT) (frL (oT + 32)) (frL (oT + 64)) (frL (oT + 96)) := by
  decide

theorem p2_terms : R3.map (symL tm0 (flOf (p3F false))) = p3T false (frL oT) (frL (oT + 32)) (frL (oT + 64)) (frL (oT + 96)) := by
  decide

/-- **The fragments keep `AI`.** -/
theorem keepAI : (∀ L ∈ [flOf dblF, flOf (p3F true), flOf (p3F false)], ∀ l ∈ aiLocs, symL tm0 L l = tm0 l) ∧
    (∀ k < 2, ∀ s < 2, ∀ l ∈ aiLocs, symL tm0 (saL k s) l = tm0 l) ∧
    (∀ k < 8, ∀ s < 2, ∀ l ∈ aiLocs, symL tm0 (sbL k s) l = tm0 l) := by
  decide +kernel

theorem ai_sub : ∀ k < 2, ∀ l ∈ aiE k, l ∈ aiLocs := by decide

/-! ## The segments' values -/

section
variable {c : Ctx} {m0 : Mem}

/-- `odd_b[k]`'s three field elements. -/
def obV (c : Ctx) (m0 : Mem) (k : Nat) : List V :=
  [lfV dsGeo c m0 (fun _ => .none) (.xf ⟨.ex 5 (96 * k), .k 32⟩),
    lfV dsGeo c m0 (fun _ => .none) (.xf ⟨.ex 5 (96 * k + 32), .k 32⟩),
    lfV dsGeo c m0 (fun _ => .none) (.xf ⟨.ex 5 (96 * k + 64), .k 32⟩)]

/-- `AI[k]` holds the cached `[2k + 1](−A₀)`. -/
def AIok (ε : Loc → V) (A0 : EdPt) : Prop := ∀ k < 2, CachedV ((aiE k).map ε) (((2 * k + 1 : Nat) : Int) • (-A0))

/-- `odd_b[k]` holds the Niels `[2k + 1]B`. -/
def OBok (c : Ctx) (m0 : Mem) : Prop := ∀ k < 8, NielsV (obV c m0 k) (((2 * k + 1 : Nat) : Int) • Bpt)

theorem AIok.of {ε ε' : Loc → V} {A0 : EdPt} (h : AIok ε A0) (he : ∀ l ∈ aiLocs, ε' l = ε l) : AIok ε' A0 :=
  fun k hk => by
    rw [List.map_congr_left fun l hl => he l (ai_sub k hk l hl)]
    exact h k hk

theorem keep_frag {L : FL} (h : ∀ l ∈ aiLocs, symL tm0 L l = tm0 l) (ε : Loc → V) :
    ∀ l ∈ aiLocs, fragE dsGeo c m0 ε L l = ε l :=
  fun l hl => by simp only [fragE, h l hl, tm0, Tm.ev, lfV]

theorem dbl_v {ε : Loc → V} {A : EdPt} (h : Rep2V (R3.map ε) A) :
    RepCV (tLocs.map (fragE dsGeo c m0 ε (flOf dblF))) (A + A) :=
  dbl_val (val := lfV dsGeo c m0 ε) dbl_terms h

theorem p3_v {ε : Loc → V} {A : EdPt} (h : RepCV (tLocs.map ε) A) :
    RepV (rLocs.map (fragE dsGeo c m0 ε (flOf (p3F true)))) A :=
  p3_val (val := lfV dsGeo c m0 ε) p3_terms h

theorem p2_v {ε : Loc → V} {A : EdPt} (h : RepCV (tLocs.map ε) A) :
    Rep2V (R3.map (fragE dsGeo c m0 ε (flOf (p3F false)))) A :=
  p2_val (val := lfV dsGeo c m0 ε) p2_terms h

theorem sa_v {k s : Nat} (hk : k < 2) (hs : s < 2) {ε : Loc → V} {A Q : EdPt} (hA : RepV (rLocs.map ε) A)
    (hQ : CachedV ((aiE k).map ε) Q) :
    RepCV (tLocs.map (fragE dsGeo c m0 ε (saL k s))) (if s == 1 then A - Q else A + Q) := by
  obtain ⟨L, st', hf, hv⟩ := add_rep (e := fun o => .view (.fr (oAI + 128 * k + o))) (sa_terms k hk s hs)
  have e : saL k s = L := by simp only [saL, hf, Option.map_some, Option.getD_some]
  rw [e]
  exact hv (lfV dsGeo c m0 ε) A Q hA hQ

theorem sb_v {k s : Nat} (hk : k < 8) (hs : s < 2) {ε : Loc → V} {A Q : EdPt} (hA : RepV (rLocs.map ε) A)
    (hQ : NielsV (obV c m0 k) Q) :
    RepCV (tLocs.map (fragE dsGeo c m0 ε (sbL k s))) (if s == 1 then A - Q else A + Q) := by
  obtain ⟨L, st', hf, hv⟩ := add_rep (e := fun o => .xf ⟨.ex 5 (96 * k + o), .k 32⟩) (sb_terms k hk s hs)
  have e : sbL k s = L := by simp only [sbL, hf, Option.map_some, Option.getD_some]
  rw [e]
  exact hv (lfV dsGeo c m0 ε) A Q hA hQ

theorem sgn_lt (d : Int) : sgn d < 2 := by unfold sgn; split <;> decide

theorem dig_odd {w : Nat} {d : Int} (h : Digit w d) (h0 : d ≠ 0) :
    d % 2 = 1 ∧ -2 ^ (w - 1) < d ∧ d < 2 ^ (w - 1) := by
  rcases h with h | h
  · exact absurd h h0
  · exact h

theorem dig3 {d : Int} (h : Digit 3 d) (h0 : d ≠ 0) : d % 2 = 1 ∧ d.natAbs / 2 < 2 := by
  obtain ⟨h1, h2, h3⟩ := dig_odd h h0
  have e : (2 : Int) ^ (3 - 1) = 4 := rfl
  rw [e] at h2 h3
  refine ⟨h1, ?_⟩
  rcases Int.natAbs_eq d with e | e <;> omega

theorem dig5 {d : Int} (h : Digit 5 d) (h0 : d ≠ 0) : d % 2 = 1 ∧ d.natAbs / 2 < 8 := by
  obtain ⟨h1, h2, h3⟩ := dig_odd h h0
  have e : (2 : Int) ^ (5 - 1) = 16 := rfl
  rw [e] at h2 h3
  refine ⟨h1, ?_⟩
  rcases Int.natAbs_eq d with e | e <;> omega

end

/-! ## The passes -/

section
variable {bE : DB → BlockS} {semA : DS → List V → List V} {semB : DB → List V → List V} {c : Ctx} {m0 : Mem}

/-- **A pass**: from `p2` values of `R` at `R`, with `AI` and `odd_b` holding their multiples,
`p2` values of `dsmStep` at `R`; `AI` stays. -/
theorem pass_val (hS : ∀ a vs, semA (DS.f a) vs = [faV a vs]) {hd sd : Nat → Int} {i : Nat} {A0 R : EdPt}
    {ε : Loc → V} (hh : Digit 3 (hd i)) (hs : Digit 5 (sd i)) (hAI : AIok ε A0) (hOB : OBok c m0)
    (hR : Rep2V (R3.map ε) R) :
    (∀ l ∈ aiLocs, runR bE dsGeo semA semB c m0 (passR (hd i) (sd i)) ε l = ε l) ∧
      Rep2V (R3.map (runR bE dsGeo semA semB c m0 (passR (hd i) (sd i)) ε)) (dsmStep sd hd A0 R i) := by
  unfold dsmStep passR
  generalize hd i = a at hh ⊢
  generalize sd i = b at hs ⊢
  have rf : ∀ (L : FL) (E : Loc → V), runR bE dsGeo semA semB c m0 (frR DS.f L) E = fragE dsGeo c m0 E L :=
    fun L E => runR_frag hS L E
  obtain ⟨kf, kab, kbb⟩ := keepAI
  have kd := keep_frag (c := c) (m0 := m0) (kf (flOf dblF) (by simp))
  have kp3 := keep_frag (c := c) (m0 := m0) (kf (flOf (p3F true)) (by simp))
  have kp2 := keep_frag (c := c) (m0 := m0) (kf (flOf (p3F false)) (by simp))
  have hT1 := dbl_v (c := c) (m0 := m0) hR
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha hb
    simp only [bne_self_eq_false, Bool.or_self, ↓reduceIte, List.append_nil, runR_append, dblR, cvR, rf]
    exact ⟨fun l hl => by rw [kp2 _ l hl, kd _ l hl], p2_v hT1⟩
  · subst ha
    have hb' : (b != 0) = true := bne_iff_ne.mpr hb
    obtain ⟨o5, l5⟩ := dig5 hs hb
    simp only [bne_self_eq_false, hb', Bool.or_true, hb, ↓reduceIte, List.nil_append, List.append_assoc,
      runR_append, dblR, cvR, rf]
    have hR2 := p3_v (c := c) (m0 := m0) hT1
    have hT3 := sb_v l5 (sgn_lt b) hR2 (hOB _ l5)
    unfold sgn at hT3
    rw [signed_eq o5] at hT3
    exact ⟨fun l hl => by rw [kp2 _ l hl, keep_frag (kbb _ l5 _ (sgn_lt b)) _ l hl, kp3 _ l hl, kd _ l hl], p2_v hT3⟩
  · subst hb
    have ha' : (a != 0) = true := bne_iff_ne.mpr ha
    obtain ⟨o3, l3⟩ := dig3 hh ha
    simp only [bne_self_eq_false, ha', Bool.true_or, ha, ↓reduceIte, List.append_nil, List.append_assoc,
      runR_append, dblR, cvR, rf]
    have hR2 := p3_v (c := c) (m0 := m0) hT1
    have hAI2 : AIok (fragE dsGeo c m0 (fragE dsGeo c m0 ε (flOf dblF)) (flOf (p3F true))) A0 := hAI.of fun l hl => by rw [kp3 _ l hl, kd _ l hl]
    have hT3 := sa_v (c := c) (m0 := m0) l3 (sgn_lt a) hR2 (hAI2 _ l3)
    unfold sgn at hT3
    rw [signed_eq o3] at hT3
    exact ⟨fun l hl => by rw [kp2 _ l hl, keep_frag (kab _ l3 _ (sgn_lt a)) _ l hl, kp3 _ l hl, kd _ l hl], p2_v hT3⟩
  · have ha' : (a != 0) = true := bne_iff_ne.mpr ha
    have hb' : (b != 0) = true := bne_iff_ne.mpr hb
    obtain ⟨o3, l3⟩ := dig3 hh ha
    obtain ⟨o5, l5⟩ := dig5 hs hb
    simp only [ha', hb', Bool.or_self, ha, hb, ↓reduceIte, List.append_assoc, runR_append, dblR, cvR, rf]
    have hR2 := p3_v (c := c) (m0 := m0) hT1
    have hAI2 : AIok (fragE dsGeo c m0 (fragE dsGeo c m0 ε (flOf dblF)) (flOf (p3F true))) A0 := hAI.of fun l hl => by rw [kp3 _ l hl, kd _ l hl]
    have hT3 := sa_v (c := c) (m0 := m0) l3 (sgn_lt a) hR2 (hAI2 _ l3)
    unfold sgn at hT3
    rw [signed_eq o3] at hT3
    have hR4 := p3_v (c := c) (m0 := m0) hT3
    have hT5 := sb_v l5 (sgn_lt b) hR4 (hOB _ l5)
    unfold sgn at hT5
    rw [signed_eq o5] at hT5
    exact ⟨fun l hl => by
      rw [kp2 _ l hl, keep_frag (kbb _ l5 _ (sgn_lt b)) _ l hl, kp3 _ l hl, keep_frag (kab _ l3 _ (sgn_lt a)) _ l hl,
        kp3 _ l hl, kd _ l hl], p2_v hT5⟩

/-- **The passes** of the positions `k − 1, …, 0` follow `dsmRun`; `AI` stays. -/
theorem runs_val (hS : ∀ a vs, semA (DS.f a) vs = [faV a vs]) {hd sd : Nat → Int} {A0 : EdPt} (hOB : OBok c m0) :
    ∀ k, (∀ i < k, Digit 3 (hd i) ∧ Digit 5 (sd i)) → ∀ (ε : Loc → V) (R : EdPt), AIok ε A0 → Rep2V (R3.map ε) R →
      (∀ l ∈ aiLocs, runR bE dsGeo semA semB c m0 (runsR hd sd k) ε l = ε l) ∧
        Rep2V (R3.map (runR bE dsGeo semA semB c m0 (runsR hd sd k) ε)) (dsmRun sd hd A0 k R)
  | 0, _, _, _, _, hr => ⟨fun _ _ => rfl, hr⟩
  | k + 1, hd', ε, R, ha, hr => by
    obtain ⟨k1, r1⟩ := pass_val (bE := bE) (semB := semB) hS (hd' k (by omega)).1 (hd' k (by omega)).2 ha hOB hr
    rw [runsR, runR_append]
    obtain ⟨k2, r2⟩ := runs_val hS hOB k (fun i hi => hd' i (by omega)) _ _ (ha.of k1) r1
    exact ⟨fun l hl => by rw [k2 l hl, k1 l hl], r2⟩


/-- **The loop over the digits of `s` and `h`**: from `p2` values of the identity at `R`, with `AI`
and `odd_b` holding their multiples, the passes over the digits read from the bytes of `wnaf 5 s`
(at `p1`) and `wnaf 3 h` (at `p2`), from the top-digit scan, leave `p2` values of `[s]B − [h]A₀`;
`AI` stays. -/
theorem loop_val (hS : ∀ a vs, semA (DS.f a) vs = [faV a vs]) {m : Mem} {p1 p2 : Word} {s h : Nat} {A0 : EdPt}
    (hs : s < L) (hh : h < L) (b1 : bytesAt m p1 256 = wnafBytes 5 s) (b2 : bytesAt m p2 256 = wnafBytes 3 h)
    (hOB : OBok c m0) {ε : Loc → V} (hAI : AIok ε A0) (hR : Rep2V (R3.map ε) 0) :
    (∀ l ∈ aiLocs, runR bE dsGeo semA semB c m0
        (runsR (digOf m p2) (digOf m p1) (dsmTop (digOf m p1) (digOf m p2) 256)) ε l = ε l) ∧
      Rep2V (R3.map (runR bE dsGeo semA semB c m0
        (runsR (digOf m p2) (digOf m p1) (dsmTop (digOf m p1) (digOf m p2) 256)) ε)) ((s : Int) • Bpt - (h : Int) • A0) := by
  have hk := (Ed25519ScalarMul.dsmTop_spec (digOf m p1) (digOf m p2) 256).1
  obtain ⟨k1, r1⟩ := runs_val (bE := bE) (semB := semB) (hd := digOf m p2) (sd := digOf m p1) (A0 := A0) hS hOB
    (dsmTop (digOf m p1) (digOf m p2) 256) (fun i hi =>
      (Ed25519VerifyVal.verify_digits hs hh b1 b2 i (by omega)).symm) ε 0 hAI hR
  exact ⟨k1, sb_rep hs hh b1 b2 r1⟩

end

/-! ## The prologue, the identity and the epilogue -/

section
variable {c : Ctx} {m0 : Mem}

/-- The callees' values: the field callees, `m0c_copy` of one, two and three elements, `zero`;
the block `ident`. -/
def dsV : DS → List V → List V
  | .f a => fun vs => [faV a vs]
  | .copy => fun vs => [Ed25519FePow.paV .copyOut vs]
  | .copy2 => id
  | .copy3 => id
  | .zero => Ed25519WordAd.zeroV 4

def dsBV : DB → List V → List V
  | .ident => Ed25519MulBaseVal.identV

abbrev runD (c : Ctx) (m0 : Mem) : List (ROp DS DB) → (Loc → V) → Loc → V := runR dbS dsGeo dsV dsBV c m0

theorem hSD : ∀ a vs, dsV (DS.f a) vs = [faV a vs] := fun _ _ => rfl

theorem runD_app (L L' : List (ROp DS DB)) (E : Loc → V) : runD c m0 (L ++ L') E = runD c m0 L' (runD c m0 L E) :=
  runR_append _ _ _ _ _ _ _ _ _

/-- A buffer's field element. -/
def xS (r o : Nat) : Src := .extF ⟨.ex r o, .k 32⟩
def vS (o : Nat) : Src := .view (.fr o)
def call1 (a : FA) (o : Nat) (s : List Src) : ROp DS DB := .call (.f a) [(.fr o, .fe)] s

/-- `neg_a` and `to_cached(R, AI[j])`'s updates. -/
def negR : List (ROp DS DB) :=
  [call1 .sub oR [xS 4 0, xS 3 0], .call .copy2 [(.fr (oR + 32), .fe), (.fr (oR + 64), .fe)] [xS 3 32, xS 3 64],
    call1 .sub (oR + 96) [xS 4 0, xS 3 96]]

def cachR (j : Nat) : List (ROp DS DB) :=
  [call1 .add (oAI + 128 * j) [vS (oR + 32), vS oR], call1 .sub (oAI + 128 * j + 32) [vS (oR + 32), vS oR],
    .call .copy [(.fr (oAI + 128 * j + 64), .fe)] [vS (oR + 64)], call1 .mul (oAI + 128 * j + 96) [vS (oR + 96), xS 4 96]]

def preR : List (ROp DS DB) :=
  negR ++ cachR 0 ++ dblR ++ cvR true ++ cachR 1 ++ negR ++ frR DS.f (flOf addF) ++ cvR true ++ cachR 1

theorem pre_lin : (segPre.lin dsS dbS dsGeo stE).map Prod.fst = some preR := by decide +kernel

/-- A buffer's field element as a number. -/
def xF (c : Ctx) (m0 : Mem) (r o : Nat) : Int := Field25519Routines.feVal m0 ((Loc.ex r o).addr c (dsGeo.fsp c))

theorem xS_val (E : Loc → V) (r o : Nat) : Src.val dsGeo c m0 E (xS r o) = .f (xF c m0 r o) := rfl

/-- `negR`'s values at `R`. -/
theorem neg_v (E : Loc → V) : rLocs.map (runD c m0 negR E) =
    [.f (xF c m0 4 0 - xF c m0 3 0), .f (xF c m0 3 32), .f (xF c m0 3 64), .f (xF c m0 4 0 - xF c m0 3 96)] := rfl

theorem cach_v (j : Nat) (hj : j < 2) (E : Loc → V) : (aiE j).map (runD c m0 (cachR j) E) =
    [faV .add [E (.fr (oR + 32)), E (.fr oR)], faV .sub [E (.fr (oR + 32)), E (.fr oR)],
      Ed25519FePow.paV .copyOut [E (.fr (oR + 64))], faV .mul [E (.fr (oR + 96)), .f (xF c m0 4 96)]] := by
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl


/-- After `neg_a`'s and the conversions' fragments, the rest of the prologue. -/
def tailR : List (ROp DS DB) := dblR ++ cvR true ++ cachR 1 ++ negR ++ frR DS.f (flOf addF) ++ cvR true ++ cachR 1

theorem pre_eq : preR = negR ++ cachR 0 ++ tailR := by simp only [preR, tailR, List.append_assoc]

theorem pre_keeps : (∀ l ∈ aiE 0, ∀ r ∈ tailR, keeps l r = true) ∧ (∀ j < 2, ∀ l ∈ rLocs, ∀ r ∈ cachR j, keeps l r = true) ∧
    (∀ l ∈ aiE 1, ∀ r ∈ negR, keeps l r = true) := by
  decide +kernel

theorem add_terms : tLocs.map (symL tm0 (flOf addF)) = addT true false (frL oR) (frL (oR + 32)) (frL (oR + 64)) (frL (oR + 96))
    (frL (oAI + 128 * 1)) (frL (oAI + 128 * 1 + 32)) (frL (oAI + 128 * 1 + 64)) (frL (oAI + 128 * 1 + 96)) := by
  decide

/-- `m0c_ed_zero`'s zero and `2d`. -/
def KOk (c : Ctx) (m0 : Mem) : Prop := fI (xF c m0 4 0) = 0 ∧ fI (xF c m0 4 96) = d2

/-- `A`'s four field elements. -/
def aV (c : Ctx) (m0 : Mem) : List V := [.f (xF c m0 3 0), .f (xF c m0 3 32), .f (xF c m0 3 64), .f (xF c m0 3 96)]

theorem cach_rep {j : Nat} (hj : j < 2) (hk : KOk c m0) {E : Loc → V} {P : EdPt} (h : RepV (rLocs.map E) P) :
    CachedV ((aiE j).map (runD c m0 (cachR j) E)) P ∧ rLocs.map (runD c m0 (cachR j) E) = rLocs.map E := by
  refine ⟨?_, List.map_congr_left fun l hl => run_keep _ _ (pre_keeps.2.1 j hj l hl)⟩
  obtain ⟨x, y, z, t, he, hr⟩ := h
  have hr' : RepV [.f x, .f y, .f z, .f t] P := ⟨x, y, z, t, rfl, hr⟩
  simp only [rLocs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  obtain ⟨e0, e1, e2, e3⟩ := he
  rw [cach_v j hj, e0, e1, e2, e3]
  exact cached_rep hk.2 hr'

/-- **The prologue**: from `A`'s values, `AI` holds the cached `−A` and `[3](−A)`. -/
theorem pre_val {A0 : EdPt} (hA : RepV (aV c m0) A0) (hk : KOk c m0) (ε : Loc → V) : AIok (runD c m0 preR ε) A0 := by
  have rf : ∀ (L : FL) (E : Loc → V), runD c m0 (frR DS.f L) E = fragE dsGeo c m0 E L := fun L E => runR_frag hSD L E
  have hN : ∀ E, RepV (rLocs.map (runD c m0 negR E)) (-A0) := fun E => by rw [neg_v]; exact negA_rep hk.1 hA
  rw [pre_eq, runD_app, runD_app]
  generalize hE2 : runD c m0 (cachR 0) (runD c m0 negR ε) = E2
  obtain ⟨c2, k2⟩ := cach_rep (j := 0) (by decide) hk (hN ε)
  rw [hE2] at c2 k2
  have r2 : RepV (rLocs.map E2) (-A0) := k2 ▸ hN ε
  have hk0 : (aiE 0).map (runD c m0 tailR E2) = (aiE 0).map E2 :=
    List.map_congr_left fun l hl => run_keep _ _ (pre_keeps.1 l hl)
  intro k hk2
  match k, hk2 with
  | 0, _ => rw [hk0, ← one_eq]; exact c2
  | 1, _ =>
    rw [← three_eq]
    simp only [tailR, List.append_assoc, runD_app, dblR, cvR, rf]
    have t3 := dbl_v (c := c) (m0 := m0) (RepV.rep2 r2)
    have r4 := p3_v (c := c) (m0 := m0) t3
    obtain ⟨c5, -⟩ := cach_rep (j := 1) (by decide) hk r4
    generalize runD c m0 (cachR 1) (fragE dsGeo c m0 (fragE dsGeo c m0 E2 (flOf dblF)) (flOf (p3F true))) = E5 at c5
    have r6 := hN E5
    have c6 : CachedV ((aiE 1).map (runD c m0 negR E5)) (-A0 + -A0) := by
      rw [List.map_congr_left fun l hl => run_keep _ _ (pre_keeps.2.2 l hl)]; exact c5
    have t7 := cadd_val (val := lfV dsGeo c m0 (runD c m0 negR E5)) (neg := false) add_terms r6 c6
    simp only [Bool.false_eq_true, ↓reduceIte] at t7
    have r8 := p3_v (c := c) (m0 := m0) t7
    exact (cach_rep (j := 1) (by decide) hk r8).1


/-- `set_identity(R)`'s and the epilogue's updates. -/
def idR : List (ROp DS DB) :=
  [.call .zero (Ed25519MulBaseVal.fes oR 4 (.bytes 32)) [], .blk .ident (Ed25519MulBaseVal.fes oR 4 .fe) (Ed25519MulBaseVal.vws oR 4)]

def endR : List (ROp DS DB) :=
  [.call .copy3 [(.ex 0 0, .fe), (.ex 0 32, .fe), (.ex 0 64, .fe)] [vS oR, vS (oR + 32), vS (oR + 64)]]

theorem id_lin : (segId.lin dsS dbS dsGeo (rs s0)).map Prod.fst = some idR ∧
    (segEnd.lin dsS dbS dsGeo (rs s1)).map Prod.fst = some endR ∧ ∀ l ∈ aiLocs, ∀ r ∈ idR, keeps l r = true := by
  decide +kernel

/-- **The identity**: `p2` values of `0` at `R`; `AI` stays. -/
theorem id_val (E : Loc → V) :
    Rep2V (R3.map (runD c m0 idR E)) 0 ∧ ∀ l ∈ aiLocs, runD c m0 idR E l = E l := by
  refine ⟨?_, fun l hl => run_keep _ _ (id_lin.2.2 l hl)⟩
  have : rLocs.map (runD c m0 idR E) = [.f 0, .f 1, .f 1, .f 0] := by
    show [_, _, _, _] = _
    simp only [runD, runR, ROp.ev, idR, Ed25519MulBaseVal.fes, Ed25519MulBaseVal.vws, dsBV, dbS, Ed25519MulBaseProg.mbS, Ed25519MulBaseProg.ioIdent, dsV,
      Ed25519WordAd.zeroV, Ed25519MulBaseVal.r4, List.map_cons, List.map_nil, Src.val, updOuts, Ed25519MulBaseVal.identV]
    simp [updOuts, setRg]
    exact ⟨Ed25519MulBaseVal.zero_dec.1, by decide, Ed25519MulBaseVal.zero_dec.1⟩
  exact RepV.rep2 (this ▸ Ed25519MulBaseVal.rep0)

/-- **The epilogue**: `out` gets `R`'s `X, Y, Z`. -/
theorem end_val (E : Loc → V) :
    [runD c m0 endR E (.ex 0 0), runD c m0 endR E (.ex 0 32), runD c m0 endR E (.ex 0 64)] = R3.map E := rfl

end

/-! ## The code's tables -/

section
variable {c : Ctx} {m0 : Mem}
open M0Crypto.Thumb (CodeAt ofNat_add_assoc)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519Tables (TablesOk leVals)
open M0Crypto.Release.Ed25519Bridge (toF toF_mod toF_mul toF_two toF_d)
open M0Crypto.Release.Ed25519DecompressVal (cBytes consts const_fe)
open M0Crypto.Artifacts.Ed25519Compact (ed_zero ed_odd_b)

/-- `m0c_ed_d2`'s bytes, `96` from `m0c_ed_zero`, hold `2 d`. -/
theorem d2_bytes (b : Build) : decodeInt (cBytes b 96) = 2 * Spec.Ed25519.d % Spec.Ed25519.p := by
  cases b <;> decide +kernel

/-- **The zero and `2 d`** from the code. -/
theorem k_ok {base : Word} (b : Build) (hc : CodeAt m0 base b.bytes) (h4 : c.ptr 4 = base + BitVec.ofNat 32 ed_zero) :
    KOk c m0 := by
  have v : ∀ e, e + 32 ≤ 160 → xF c m0 4 e = (decodeInt (cBytes b e) : Int) := fun e he => by
    show ((Field25519Routines.feVal m0 (c.ptr 4 + BitVec.ofNat 32 e) : Nat) : Int) = _
    rw [h4, const_fe b hc he]
  refine ⟨?_, ?_⟩
  · rw [v 0 (by decide), fI_nat, show cBytes b 0 = cBytes b Ed25519DecompressVal.cZero from rfl, (consts b).1]; rfl
  · rw [v 96 (by decide), fI_nat, d2_bytes, toF_mod, toF_mul, toF_two, toF_d]; rfl

/-- **`m0c_ed_odd_b`** from the code: entry `k` is the Niels `[2k + 1]B`. -/
theorem ob_ok {base : Word} (b : Build) (hc : CodeAt m0 base b.bytes) (ht : TablesOk b)
    (h5 : c.ptr 5 = base + BitVec.ofNat 32 ed_odd_b) : OBok c m0 := by
  have hl : ed_odd_b + 32 * 24 ≤ b.bytes.length := by
    rw [Ed25519.Build.bytes_length, ← ht.comb_end]; cases b <;> decide
  intro k hk
  have hv : ∀ j < 3, xF c m0 5 (96 * k + 32 * j) = ((leVals 32 24 (b.bytes.drop ed_odd_b)).getD (3 * k + j) 0 : Int) := by
    intro j hj
    show ((Field25519Routines.feVal m0 (c.ptr 5 + BitVec.ofNat 32 (96 * k + 32 * j)) : Nat) : Int) = _
    rw [h5, ofNat_add_assoc, show ed_odd_b + (96 * k + 32 * j) = ed_odd_b + 32 * (3 * k + j) by omega,
      Ed25519MulBaseTab.fe_tab hc (by omega) hl]
  have e0 := hv 0 (by decide)
  have e1 := hv 1 (by decide)
  have e2 := hv 2 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2
  have ho := Ed25519TableLink.odd_b ht k hk
  rw [Ed25519MulBaseTab.tab_three (by rw [Ed25519MulBaseTab.leVals_length]; omega)] at ho
  refine ⟨_, _, _, rfl, ?_⟩
  show (⟨fI (xF c m0 5 (96 * k)), fI (xF c m0 5 (96 * k + 32)), fI (xF c m0 5 (96 * k + 64))⟩ : Ed25519Formulas.Niels Ed25519Field.Fp) = _
  rw [e0, e1, e2, fI_nat, fI_nat, fI_nat, ho, show ((2 * k + 1 : Nat) : Int) = 2 * (k : Int) + 1 by omega]

end

end M0Crypto.Release.Ed25519DsmVal
