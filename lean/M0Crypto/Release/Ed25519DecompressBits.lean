import M0Crypto.Release.Ed25519DecompressRun

/-!
# `m0c_ge_decompress`'s tests are `decodeCode`'s

With the code's constants (`DcK`), the machine's tests are those of `decodeCode` on the input's
`y` and sign bit: `k1` the first candidate (`!bOf`), `k2` the second, `kz` `x = 0`, `kn` the
negation (`nOf` on the path `bOf`). `okD_eq`: the status is `decTests`; `dc_ok`: `r0` is `0`
exactly when the input bytes decode. `E7_eq`: the values along the body are `dcR`'s, so on
success `out` holds `decodeCode`'s point (`dc_out`) and the representation of the decoded point
(`dc_rep`).
-/

namespace M0Crypto.Release.Ed25519DecompressStitch

open M0Crypto.Armv6M (Word Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519DecompressOut (seg0R seg1R seg2R seg3R seg4R seg5R seg6R powR L3 inB yN sgN eqR dcR
  DcK FV uF vvF x0F x1F bOf nOf runC runC_app runC_frag runC_keep run_keep keeps Sems seg1_eq seg1_keep src_x xv
  xL frag1 stA stB dc_val dec_rep)
open M0Crypto.Release.Ed25519DecompressVal (cZero cOne cD cSqrt)
open M0Crypto.Release.Ed25519MulBaseVal (frR)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519Curve (d sqrtM1)
open M0Crypto.Release.Ed25519PrimeCert (p)
open M0Crypto.Release.Ed25519Bridge (toF)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519FeEq (okE)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-! ## `T` through the first test -/

section
variable {semA : DA → List V → List V} {semB : DB → List V → List V} {c : Ctx} {m0 : Mem}

theorem t_keep : keeps (.fr T) (eqR U : ROp DA DB) = true ∧ ∀ r ∈ (frR DA.f L3 : List (ROp DA DB)), keeps (.fr T) r = true := by
  decide +kernel

/-- **`v x²` at `T`** through the first `fe_eq` (`stA`'s run). -/
theorem stT (hs : Sems semA semB) (hk : DcK c m0) (E0 : Loc → V) :
    FV (runC semA semB c m0 (seg0R ++ seg1R) E0 (.fr T))
      (x0F (toF (yN c m0)) * x0F (toF (yN c m0)) * vvF (toF (yN c m0))) := by
  rw [runC_app]
  generalize hE1 : runC semA semB c m0 seg0R E0 = E1
  have hY : E1 (.fr Y) = .f (yN c m0 : Int) := by
    rw [← hE1]
    simp only [runC, runR, ROp.ev, seg0R, hs.load, List.map_cons, List.map_nil, Src.val]
    rfl
  have m1 : [fragE dcGeo c m0 E1 L1 (.fr U), fragE dcGeo c m0 E1 L1 (.fr V), fragE dcGeo c m0 E1 L1 (.fr V3),
      fragE dcGeo c m0 E1 L1 (.fr T)] = f1T.map (Tm.ev (lfV dcGeo c m0 E1)) := map_ev f1_terms.2
  simp only [f1T, fr, cv, List.map_cons, List.map_nil, Tm.ev, lfV, hY, src_x, vop, List.cons.injEq, and_true] at m1
  obtain ⟨eU, eV, eV3, eT⟩ := m1
  rw [seg1_eq, runC_app, runC_frag hs]
  generalize fragE dcGeo c m0 E1 L1 = E2 at eU eV eV3 eT
  rw [runC_app, runC_app]
  generalize hE3 : runC semA semB c m0 [powR] E2 = E3
  have k3 : ∀ l ∈ [Loc.fr U, .fr V, .fr V3], E3 l = E2 l := fun l hl => by
    rw [← hE3]; exact run_keep _ E2 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact seg1_keep.2.2.2 l hl
  have pT : [E3 (.fr T)] = Ed25519FePow.powSem 1 [E2 (.fr T)] := by
    rw [← hE3]
    show [updOuts E2 [(.fr T, .fe)] (semA .pow [E2 (.fr T)]) (.fr T)] = _
    rw [hs.pow, eT]
    rfl
  rw [eT] at pT
  simp only [Ed25519FePow.powSem, List.cons.injEq, and_true] at pT
  have hT : runC semA semB c m0 [eqR U] (runC semA semB c m0 (frR DA.f L2) E3) (.fr T) =
      runC semA semB c m0 (frR DA.f L2) E3 (.fr T) :=
    run_keep [eqR U] _ fun r hr => by rw [List.mem_singleton.mp hr]; exact t_keep.1
  rw [hT, runC_frag hs]
  have m2 : [fragE dcGeo c m0 E3 L2 (.fr X), fragE dcGeo c m0 E3 L2 (.fr T)] = f2T.map (Tm.ev (lfV dcGeo c m0 E3)) :=
    map_ev f2_terms.2.2
  simp only [f2T, fr, List.map_cons, List.map_nil, Tm.ev, lfV, pT, k3 (.fr V3) (by simp), k3 (.fr U) (by simp),
    k3 (.fr Ed25519DecompressProg.V) (by simp), eU, eV, eV3, vop, List.cons.injEq,
    and_true] at m2
  refine ⟨_, m2.2, ?_⟩
  simp only [fI_sub, fI_mul, fI_add, fI_nat, Ed25519DecompressVal.pow_val, hk.2.1, hk.2.2.1, x0F, uF, vvF]

end

/-! ## The values are `dcR`'s -/

noncomputable section
variable (Rs : Rels) (b : Build) (c : Ctx) (m0 : Mem)

/-- `fe_eq` changes no value. -/
theorem eqR_nop (o : Nat) (E : Loc → V) : runC (sA Rs b) (sB Rs) c m0 [eqR o] E = E := by
  simp only [runC, runR, ROp.ev, eqR]
  exact updOuts_none E _

theorem E2_eq : E2 Rs b c m0 = runC (sA Rs b) (sB Rs) c m0 (seg0R ++ seg1R) fun _ => .none := by
  rw [runC_app, show seg1R = q1R ++ [eqR U] by simp only [seg1_eq, q1R, List.append_assoc], runC_app, eqR_nop]
  rfl

theorem E5_eq (bb : Bool) :
    E5 Rs b c m0 bb = runC (sA Rs b) (sB Rs) c m0 ((if bb then seg2R ++ seg3R else []) ++ seg4R) (E2 Rs b c m0) := by
  rw [runC_app]
  cases bb
  · rfl
  · simp only [E5, EJ, E4, E3, ↓reduceIte]
    rw [runC_app, show seg2R = frR DA.f L3 ++ [eqR X2] from rfl, runC_app, eqR_nop]

/-- **The values along the path `bb`, `n`** are those of `dcR`. -/
theorem E7_eq (bb n : Bool) : E7 Rs b c m0 bb n = runC (sA Rs b) (sB Rs) c m0 (dcR bb n) fun _ => .none := by
  rw [dcR, runC_app, runC_app, runC_app, ← E2_eq, ← E5_eq, E7, E6]
  cases n <;> rfl

/-! ## The tests are `decodeCode`'s -/

variable {Rs b c m0}

/-- `decodeCode`'s `y`. -/
abbrev yF (c : Ctx) (m0 : Mem) : Fp := toF (yN c m0)

theorem iE1_eq : iE1 Rs b c m0 = [E2 Rs b c m0 (.fr T), E2 Rs b c m0 (.fr U)] := by
  rw [iE1, ioVs_of sites_io.2.1]; rfl

theorem iE2_eq : iE2 Rs b c m0 = [E3 Rs b c m0 (.fr T), E3 Rs b c m0 (.fr X2)] := by
  rw [iE2, ioVs_of sites_io.2.2]; rfl

theorem okE_fv {a b' : V} {x y : Fp} (ha : FV a x) (hb : FV b' y) : okE [a, b'] = decide (x = y) := by
  obtain ⟨_, rfl, rfl⟩ := ha
  obtain ⟨_, rfl, rfl⟩ := hb
  rfl

theorem isZ_fv {v : V} {x : Fp} (h : FV v x) : isZ v = decide (x = 0) := by
  obtain ⟨_, rfl, rfl⟩ := h; rfl

theorem pOf_fv {v : V} {x : Fp} (s : Nat) (h : FV v x) : pOf s v = decide (x.val % 2 = s) := by
  obtain ⟨_, rfl, rfl⟩ := h; rfl

/-! The tests on the input bytes `l`, as `decodeCode` makes them. -/

def yL (l : List (BitVec 8)) : Nat := decodeInt l % 2 ^ 255
def sL (l : List (BitVec 8)) : Nat := decodeInt l / 2 ^ 255
abbrev YL (l : List (BitVec 8)) : Fp := toF (yL l)

def b0 (l : List (BitVec 8)) : Bool := decide (yL l < p)
def b1 (l : List (BitVec 8)) : Bool := !bOf (YL l)
def b2 (l : List (BitVec 8)) : Bool := decide (x0F (YL l) * x0F (YL l) * vvF (YL l) = 0 - uF (YL l))
def bz (l : List (BitVec 8)) : Bool := decide (x1F (YL l) (bOf (YL l)) = 0)
def bs (l : List (BitVec 8)) : Bool := decide (sL l = 0)
def bn (l : List (BitVec 8)) : Bool := nOf (YL l) (sL l)

/-- The status of the tests `k0` … `s`. -/
def okB (k0 k1 k2 z s : Bool) : Bool := k0 && (k1 || k2) && (!z || s)

/-- **The tests' status is `decTests`'s.** -/
theorem okB_spec (l : List (BitVec 8)) : okB (b0 l) (b1 l) (b2 l) (bz l) (bs l) = decTests (yL l) (sL l) := by
  have e : decTests (yL l) (sL l) = (decide (yL l < p) && rootTests (x0F (YL l))
      (x0F (YL l) * x0F (YL l) * vvF (YL l)) (uF (YL l)) (sL l)) := rfl
  rw [okB, b0, b1, b2, bz, bs, e, rootTests, bOf]
  simp only [x1F, Bool.not_not]
  generalize toF (yL l) = Y
  generalize x0F Y = x
  generalize x * x * vvF Y = w
  generalize uF Y = u
  simp [Bool.and_assoc]

variable (hk : DcK c m0)
include hk

theorem e2_fv : FV (E2 Rs b c m0 (.fr Y)) (yF c m0) ∧ FV (E2 Rs b c m0 (.fr U)) (uF (yF c m0)) ∧
    FV (E2 Rs b c m0 (.fr X)) (x0F (yF c m0)) ∧ FV (E2 Rs b c m0 (.fr T)) (x0F (yF c m0) * x0F (yF c m0) * vvF (yF c m0)) := by
  rw [E2_eq]
  exact ⟨(stA (daAd_sems Rs b) hk _).1, (stA (daAd_sems Rs b) hk _).2.1, (stA (daAd_sems Rs b) hk _).2.2,
    stT (daAd_sems Rs b) hk _⟩

/-- The first test: `v x² = u`. -/
theorem k1_eq : k1 Rs b c m0 = !bOf (yF c m0) := by
  rw [k1, iE1_eq, okE_fv (e2_fv hk).2.2.2 (e2_fv hk).2.1, bOf, Bool.not_not]

/-- The second test: `v x² = −u`. -/
theorem k2_eq : k2 Rs b c m0 = decide (x0F (yF c m0) * x0F (yF c m0) * vvF (yF c m0) = 0 - uF (yF c m0)) := by
  obtain ⟨-, ⟨zU, eU, fU⟩, -, hT⟩ := e2_fv (Rs := Rs) (b := b) hk
  have h3 : E3 Rs b c m0 = fragE dcGeo c m0 (E2 Rs b c m0) L3 := runC_frag (daAd_sems Rs b) _ _
  have hX2 : FV (E3 Rs b c m0 (.fr X2)) (0 - uF (yF c m0)) := by
    refine ⟨xv c m0 cZero - zU, ?_, by rw [fI_sub, hk.1, fU]⟩
    rw [h3, L3, frag1]
    simp only [opT, List.map_cons, List.map_nil, lfT, tm0, Tm.ev, lfV, eU, xL, src_x, vop]
  have hT3 : E3 Rs b c m0 (.fr T) = E2 Rs b c m0 (.fr T) := runC_keep _ _ t_keep.2
  rw [k2, iE2_eq, hT3, okE_fv hT hX2]

/-- The root on the path `bb`, at `X` after its canonical form. -/
theorem e5_x (bb : Bool) : FV (E5 Rs b c m0 bb (.fr X)) (x1F (yF c m0) bb) := by
  obtain ⟨hY, -, hX, -⟩ := e2_fv (Rs := Rs) (b := b) hk
  rw [E5_eq]
  exact (stB (daAd_sems Rs b) hk bb hY hX).2

/-- `x = 0` on the path `bb`. -/
theorem kz_eq (bb : Bool) : kz Rs b c m0 bb = decide (x1F (yF c m0) bb = 0) := by
  rw [kz, isZ_fv (e5_x hk bb)]

/-- **The path is `decodeCode`'s**: the second candidate exactly when `bOf`, the negation exactly
when `nOf`. -/
theorem path_eq : (!k1 Rs b c m0) = bOf (yF c m0) ∧ kn Rs b c m0 (bOf (yF c m0)) = nOf (yF c m0) (sgN c m0) := by
  refine ⟨by rw [k1_eq hk, Bool.not_not], ?_⟩
  rw [kn, pOf_fv _ (e5_x hk _), nOf]

/-- **The machine's tests are `decodeCode`'s** on the input bytes. -/
theorem bits_eq : k0 c m0 = b0 (inB c m0) ∧ k1 Rs b c m0 = b1 (inB c m0) ∧ k2 Rs b c m0 = b2 (inB c m0) ∧
    kz Rs b c m0 (!k1 Rs b c m0) = bz (inB c m0) ∧ ks c m0 = bs (inB c m0) ∧
    kn Rs b c m0 (!k1 Rs b c m0) = bn (inB c m0) := by
  refine ⟨rfl, k1_eq hk, k2_eq hk, ?_, rfl, ?_⟩
  · rw [(path_eq hk).1]; exact kz_eq hk _
  · rw [(path_eq hk).1]; exact (path_eq hk).2

/-- **The status is `decTests`'s.** -/
theorem okD_eq : okD Rs b c m0 = decTests (yN c m0) (sgN c m0) := by
  obtain ⟨e0, e1, e2, ez, es, -⟩ := bits_eq (Rs := Rs) (b := b) hk
  rw [show okD Rs b c m0 = okB (k0 c m0) (k1 Rs b c m0) (k2 Rs b c m0) (kz Rs b c m0 (!k1 Rs b c m0)) (ks c m0) from rfl,
    ez, e0, e1, e2, es]
  exact okB_spec _

/-- **The status**: `r0 = 0` exactly when the input bytes decode. -/
theorem dc_ok {r : Word} (hr : r = if okD Rs b c m0 then 0#32 else 1#32) :
    r = 0#32 ↔ (Spec.Ed25519.decodePoint (inB c m0)).isSome = true :=
  dec_status (Footprint.bytesAt_length _ _ _) (by rw [hr, okD_eq hk]; rfl)

/-- The values at the end of the path the tests take. -/
abbrev Eo (Rs : Rels) (b : Build) (c : Ctx) (m0 : Mem) : Loc → V :=
  E7 Rs b c m0 (!k1 Rs b c m0) (kn Rs b c m0 (!k1 Rs b c m0))

/-- **The outputs on success**: `out` holds `decodeCode`'s point. -/
theorem dc_out {P : Ed25519EdwardsExtended.Ext Fp} (h : Ed25519Decode.decodeCode (yN c m0) (sgN c m0) = some P) :
    FV (Eo Rs b c m0 (.ex 0 0)) P.X ∧ FV (Eo Rs b c m0 (.ex 0 32)) P.Y ∧ FV (Eo Rs b c m0 (.ex 0 64)) P.Z ∧
      FV (Eo Rs b c m0 (.ex 0 96)) P.T := by
  rw [Eo, (path_eq hk).1, (path_eq hk).2, E7_eq]
  exact dc_val (daAd_sems Rs b) hk _ h

/-- **The representation on success**: `out` holds the `p3` values of a point the decoded `Q`
represents. -/
theorem dc_rep {Q : Spec.Ed25519.Point} (h : Spec.Ed25519.decodePoint (inB c m0) = some Q) :
    ∃ A : Ed25519Group.EdPt, Ed25519Bridge.SpecRep Q A ∧
      RepV [Eo Rs b c m0 (.ex 0 0), Eo Rs b c m0 (.ex 0 32), Eo Rs b c m0 (.ex 0 64), Eo Rs b c m0 (.ex 0 96)] A := by
  rw [Eo, (path_eq hk).1, (path_eq hk).2, E7_eq]
  exact dec_rep (daAd_sems Rs b) hk _ h

end

end M0Crypto.Release.Ed25519DecompressStitch
