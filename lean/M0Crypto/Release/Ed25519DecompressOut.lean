import M0Crypto.Release.Ed25519DecompressBlocks
import M0Crypto.Release.Ed25519MulBaseVal

/-!
# `m0c_ge_decompress`'s outputs

The routine's lines between its tests (`Ed25519DecompressProg`) run, along the path the tests
take, the updates `dcR b n`: the load, `F1`, the power, `F2` and the first `fe_eq`; for `b` the
second candidate test and the `sqrt(−1)` fix-up; the canonical form of `x`; for `n` the negation;
the output. `seg0_lin` … `seg5_lin` decide the lines' static runs; the output's updates `seg6R`
are written here (its constant copy has no static run yet).

* `stA` … `stD`: the values at `Y`, `U` and `X` through the first test, the root and its
  canonical form, the negation, and the output;
* `code_some`, `dc_val`: when `decodeCode` succeeds, the four field values at `out` are its point,
  along the path (`bOf`, `nOf`) that its tests select;
* `dec_rep`: when the input bytes decode to `Q`, they are the `p3` values of an `A` that `Q`
  represents; `dk_ok`: the constants these read are the code's.
-/

namespace M0Crypto.Release.Ed25519DecompressOut

open M0Crypto.Armv6M (Word Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519MulBaseVal (frR flOf runR_frag)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519DecompressVal (cZero cOne cD cSqrt)

/-! ## The updates -/

def vS (o : Nat) : Src := .view (.fr o)
def xS (o : Nat) : Src := .extF ⟨.ex 2 o, .k 32⟩
def xL (o : Nat) : Lf := .xf ⟨.ex 2 o, .k 32⟩

def eqR (b : Nat) : ROp DA DB := .call .eq [] [vS T, vS b]
def canonR : ROp DA DB := .call .canon [(.fr X, .fc)] [vS X]

def L3 : FL := [(.fr X2, .sub, [xL cZero, .view (.fr U)])]
def L4 : FL := [(.fr X, .mul, [.view (.fr X), xL cSqrt])]
def L5 : FL := [(.fr X, .sub, [xL cZero, .view (.fr X)])]

def seg0R : List (ROp DA DB) := [.blk .load [(.fr Y, .fe), (.fr SIGN, .bytes 4)] [.ext ⟨.ex 1 0, .k 32⟩]]
def seg1R : List (ROp DA DB) :=
  frR DA.f L1 ++ [.call .pow [(.fr T, .fe)] [vS T]] ++ frR DA.f L2 ++ [eqR U]
def seg2R : List (ROp DA DB) := frR DA.f L3 ++ [eqR X2]
def seg3R : List (ROp DA DB) := frR DA.f L4
def seg4R : List (ROp DA DB) := [canonR]
def seg5R : List (ROp DA DB) := frR DA.f L5 ++ [canonR]

/-- The output: `x`, `y`, the constant `1`, `x y`. -/
def cpR (o : Nat) (s : Src) : ROp DA DB := .call .copy [(.ex 0 o, .fe)] [s]
def mulR : ROp DA DB := .call (.f .mul) [(.ex 0 96, .fe)] [vS X, vS Y]
def seg6R : List (ROp DA DB) := [cpR 0 (vS X), cpR 32 (vS Y), cpR 64 (xS cOne), mulR]

theorem seg_lin : (seg0.lin daS dbS dcGeo stE).map Prod.fst = some seg0R ∧
    (seg1.lin daS dbS dcGeo (rs s0)).map Prod.fst = some seg1R ∧
    (seg2.lin daS dbS dcGeo (rs s1)).map Prod.fst = some seg2R ∧
    (seg3.lin daS dbS dcGeo (rs s2)).map Prod.fst = some seg3R ∧
    (seg4.lin daS dbS dcGeo sJ).map Prod.fst = some seg4R ∧
    (seg5.lin daS dbS dcGeo (rs s4)).map Prod.fst = some seg5R := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Updates that leave a location -/

section
variable {A Bk : Type} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V}
  {c : Ctx} {m0 : Mem}

/-- An update leaves the location `l` (blocks and byte loads: a frame location). -/
def keeps (l : Loc) : ROp A Bk → Bool
  | .call _ o _ => decide (l ∉ o.map Prod.fst)
  | .blk _ o _ => (match l with | .fr _ => true | _ => false) && decide (l ∉ o.map Prod.fst)
  | .ldb _ _ => match l with | .fr _ => true | _ => false

theorem updOuts_nmem {E : Loc → V} {l : Loc} :
    ∀ (o : List (Loc × Kd)) (vs : List V), l ∉ o.map Prod.fst → updOuts E o vs l = E l
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | (l', _) :: o, _ :: vs, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [updOuts, h.1, ↓reduceIte]
    exact updOuts_nmem o vs h.2

/-- **Updates that leave `l`** keep its value. -/
theorem run_keep {l : Loc} : ∀ (L : List (ROp A Bk)) (E : Loc → V), (∀ r ∈ L, keeps l r = true) →
    runR bE G semA semB c m0 L E l = E l
  | [], _, _ => rfl
  | r :: L, E, h => by
    rw [show runR bE G semA semB c m0 (r :: L) E = runR bE G semA semB c m0 L (r.ev bE G semA semB c m0 E) from rfl,
      run_keep L _ fun r' hr => h r' (List.mem_cons_of_mem _ hr)]
    have hk := h r (List.mem_cons.mpr (.inl rfl))
    cases r with
    | call a o s => exact updOuts_nmem o _ (of_decide_eq_true hk)
    | blk b o s =>
      cases l with
      | fr o' =>
        simp only [keeps, Bool.true_and, decide_eq_true_eq] at hk
        exact updOuts_nmem o _ hk
      | ex => simp [keeps] at hk
      | rg => simp [keeps] at hk
    | ldb r s =>
      cases l with
      | fr o' => rfl
      | ex => simp [keeps] at hk
      | rg => simp [keeps] at hk

end

/-! ## The values along a path -/

section
variable {semA : DA → List V → List V} {semB : DB → List V → List V} {c : Ctx} {m0 : Mem}
open M0Crypto.Release.Ed25519Curve (d sqrtM1)
open M0Crypto.Release.Ed25519PrimeCert (p)
open M0Crypto.Release.Ed25519Bridge (toF)
open M0Crypto.Release.Ed25519Decode (decodeCode root finish)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-- The callees' and the load block's values: those of their adapters (`fe_eq`'s is free). -/
structure Sems (semA : DA → List V → List V) (semB : DB → List V → List V) : Prop where
  f : ∀ a vs, semA (.f a) vs = [faV a vs]
  pow : ∀ vs, semA .pow vs = Ed25519FePow.powSem 1 vs
  canon : ∀ vs, semA .canon vs = Ed25519GeCompressProg.canonV vs
  copy : ∀ vs, semA .copy vs = [Ed25519FePow.paV .copyOut vs]
  load : ∀ vs, semB .load vs = loadV vs

abbrev runC (semA : DA → List V → List V) (semB : DB → List V → List V) (c : Ctx) (m0 : Mem) :
    List (ROp DA DB) → (Loc → V) → Loc → V := runR dbS dcGeo semA semB c m0

theorem runC_app (L L' : List (ROp DA DB)) (E : Loc → V) :
    runC semA semB c m0 (L ++ L') E = runC semA semB c m0 L' (runC semA semB c m0 L E) :=
  runR_append _ _ _ _ _ _ _ _ _

theorem runC_frag (hs : Sems semA semB) (L : FL) (E : Loc → V) :
    runC semA semB c m0 (frR DA.f L) E = fragE dcGeo c m0 E L :=
  runR_frag hs.f L E

theorem runC_keep {l : Loc} (L : List (ROp DA DB)) (E : Loc → V) (h : ∀ r ∈ L, keeps l r = true) :
    runC semA semB c m0 L E l = E l :=
  run_keep L E h

/-- The constant at `o` from `m0c_ed_zero`. -/
def xv (c : Ctx) (m0 : Mem) (o : Nat) : Int := (Field25519Routines.feVal m0 ((Loc.ex 2 o).addr c (dcGeo.fsp c)) : Int)

theorem src_x (E : Loc → V) (o : Nat) : Src.val dcGeo c m0 E (.extF ⟨.ex 2 o, .k 32⟩) = .f (xv c m0 o) := rfl

/-- The input bytes, `y` (bit 255 off) and the sign bit. -/
def inB (c : Ctx) (m0 : Mem) : List (BitVec 8) := Footprint.bytesAt m0 ((Loc.ex 1 0).addr c (dcGeo.fsp c)) 32
def yN (c : Ctx) (m0 : Mem) : Nat := decodeInt (inB c m0) % 2 ^ 255
def sgN (c : Ctx) (m0 : Mem) : Nat := decodeInt (inB c m0) / 2 ^ 255

/-- The code's constants `0`, `1`, `d`, `sqrt(−1)`. -/
def DcK (c : Ctx) (m0 : Mem) : Prop :=
  fI (xv c m0 cZero) = 0 ∧ fI (xv c m0 cOne) = 1 ∧ fI (xv c m0 cD) = d ∧ fI (xv c m0 cSqrt) = sqrtM1

/-- A field value with its image in `F_p`. -/
def FV (v : V) (a : Fp) : Prop := ∃ z, v = .f z ∧ fI z = a

/-- `decodeCode`'s `u`, `v` and candidate `x` from `Y`. -/
def uF (Y : Fp) : Fp := Y * Y - 1
def vvF (Y : Fp) : Fp := Y * Y * d + 1
def x0F (Y : Fp) : Fp :=
  (vvF Y * vvF Y * vvF Y * (vvF Y * vvF Y * vvF Y) * vvF Y * uF Y) ^ ((p - 5) / 8) * (vvF Y * vvF Y * vvF Y) * uF Y

def powR : ROp DA DB := .call .pow [(.fr T, .fe)] [vS T]

theorem seg1_eq : seg1R = frR DA.f L1 ++ ([powR] ++ (frR DA.f L2 ++ [eqR U])) := by
  simp only [seg1R, powR, List.append_assoc]

theorem seg1_keep : (∀ r ∈ seg1R, keeps (.fr Y) r = true) ∧ (∀ r ∈ [powR] ++ (frR DA.f L2 ++ [eqR U]), keeps (.fr U) r = true) ∧
    keeps (.fr X) (eqR U : ROp DA DB) = true ∧ (∀ l ∈ [Loc.fr U, .fr V, .fr V3], keeps l powR = true) := by
  decide +kernel

/-- **Through the first `fe_eq`**: `Y`, `u` and the candidate `x`. -/
theorem stA (hs : Sems semA semB) (hk : DcK c m0) (E0 : Loc → V) :
    FV (runC semA semB c m0 (seg0R ++ seg1R) E0 (.fr Y)) (toF (yN c m0)) ∧
    FV (runC semA semB c m0 (seg0R ++ seg1R) E0 (.fr U)) (uF (toF (yN c m0))) ∧
    FV (runC semA semB c m0 (seg0R ++ seg1R) E0 (.fr X)) (x0F (toF (yN c m0))) := by
  rw [runC_app]
  generalize hE1 : runC semA semB c m0 seg0R E0 = E1
  have hY : E1 (.fr Y) = .f (yN c m0 : Int) := by
    rw [← hE1]
    simp only [runC, runR, ROp.ev, seg0R, hs.load, List.map_cons, List.map_nil, Src.val]
    rfl
  refine ⟨⟨_, (run_keep seg1R E1 seg1_keep.1).trans hY, fI_nat _⟩, ?_⟩
  have m1 : [fragE dcGeo c m0 E1 L1 (.fr U), fragE dcGeo c m0 E1 L1 (.fr V), fragE dcGeo c m0 E1 L1 (.fr V3),
      fragE dcGeo c m0 E1 L1 (.fr T)] = f1T.map (Tm.ev (lfV dcGeo c m0 E1)) := map_ev f1_terms.2
  simp only [f1T, fr, cv, List.map_cons, List.map_nil, Tm.ev, lfV, hY, src_x, vop, List.cons.injEq, and_true] at m1
  obtain ⟨eU, eV, eV3, eT⟩ := m1
  rw [seg1_eq, runC_app, runC_frag hs]
  generalize fragE dcGeo c m0 E1 L1 = E2 at eU eV eV3 eT
  refine ⟨⟨_, (run_keep _ E2 seg1_keep.2.1).trans eU, ?_⟩, ?_⟩
  · simp only [fI_sub, fI_mul, fI_nat, hk.2.1, uF]
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
  have hX : runC semA semB c m0 [eqR U] (runC semA semB c m0 (frR DA.f L2) E3) (.fr X) =
      runC semA semB c m0 (frR DA.f L2) E3 (.fr X) :=
    run_keep [eqR U] _ fun r hr => by rw [List.mem_singleton.mp hr]; exact seg1_keep.2.2.1
  rw [hX, runC_frag hs]
  have m2 : [fragE dcGeo c m0 E3 L2 (.fr X), fragE dcGeo c m0 E3 L2 (.fr T)] = f2T.map (Tm.ev (lfV dcGeo c m0 E3)) :=
    map_ev f2_terms.2.2
  simp only [f2T, fr, List.map_cons, List.map_nil, Tm.ev, lfV, pT, k3 (.fr V3) (by simp), k3 (.fr U) (by simp),
    k3 (.fr Ed25519DecompressProg.V) (by simp), eU, eV, eV3, vop, List.cons.injEq,
    and_true] at m2
  refine ⟨_, m2.1, ?_⟩
  simp only [fI_sub, fI_mul, fI_add, fI_nat, Ed25519DecompressVal.pow_val, hk.2.1, hk.2.2.1, x0F, uF, vvF]


/-- The root: the candidate, or its `sqrt(−1)` multiple on the second test's path `b`. -/
def x1F (Y : Fp) (b : Bool) : Fp := if b then x0F Y * sqrtM1 else x0F Y

/-- The last value of `x`: negated on the path `n`. -/
def x2F (Y : Fp) (b n : Bool) : Fp := if n then 0 - x1F Y b else x1F Y b

theorem frag1 {G : Geo} (E : Loc → V) (o : Loc) (a : FA) (ls : List Lf) :
    fragE G c m0 E [(o, a, ls)] o = (opT a (ls.map (lfT tm0))).ev (lfV G c m0 E) := by
  simp only [fragE, symL, stepT, ↓reduceIte]

theorem canon_x (hs : Sems semA semB) {E : Loc → V} {z : Int} (h : E (.fr X) = .f z) :
    runC semA semB c m0 [canonR] E (.fr X) = .f (z % Field25519Congr.p) := by
  show updOuts E [(.fr X, .fc)] (semA .canon [E (.fr X)]) (.fr X) = _
  rw [hs.canon, h]
  rfl

theorem path_keep : (∀ r ∈ seg2R ++ seg3R ++ seg4R, keeps (.fr Y) r = true) ∧ (∀ r ∈ seg2R, keeps (.fr X) r = true) ∧
    (∀ r ∈ seg4R, keeps (.fr Y) r = true) ∧ (∀ r ∈ seg5R, keeps (.fr Y) r = true) ∧
    (∀ r ∈ seg6R.drop 1, keeps (.ex 0 0) r = true) ∧ (∀ r ∈ seg6R.drop 2, keeps (.ex 0 32) r = true) ∧
    keeps (.ex 0 64) mulR = true ∧ (∀ l ∈ [Loc.fr X, .fr Y], ∀ r ∈ seg6R.take 3, keeps l r = true) ∧
    (∀ r ∈ seg6R.take 1, keeps (.fr Y) r = true) := by
  decide +kernel

/-- **The root and its canonical form**: `x` at `X`; `Y` stays. -/
theorem stB (hs : Sems semA semB) (hk : DcK c m0) {E : Loc → V} {Y0 : Fp} (b : Bool)
    (hY : FV (E (.fr Y)) Y0) (hX : FV (E (.fr X)) (x0F Y0)) :
    FV (runC semA semB c m0 ((if b then seg2R ++ seg3R else []) ++ seg4R) E (.fr Y)) Y0 ∧
      FV (runC semA semB c m0 ((if b then seg2R ++ seg3R else []) ++ seg4R) E (.fr X)) (x1F Y0 b) := by
  obtain ⟨zX, eX, fX⟩ := hX
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    refine ⟨by rw [runC_keep _ E path_keep.2.2.1]; exact hY, _, canon_x hs eX, ?_⟩
    rw [Ed25519GeProg.fI_emod, fX]; rfl
  · simp only [↓reduceIte]
    refine ⟨by rw [runC_keep _ E path_keep.1]; exact hY, ?_⟩
    rw [runC_app, runC_app, seg3R, runC_frag hs]
    have h2 : runC semA semB c m0 seg2R E (.fr X) = .f zX := (run_keep _ E path_keep.2.1).trans eX
    generalize runC semA semB c m0 seg2R E = E2 at h2
    have h3 : fragE dcGeo c m0 E2 L4 (.fr X) = .f (zX * xv c m0 cSqrt) := by
      rw [L4, frag1]
      simp only [opT, List.map_cons, List.map_nil, lfT, tm0, Tm.ev, lfV, h2, xL, src_x, vop]
    refine ⟨_, canon_x hs h3, ?_⟩
    rw [Ed25519GeProg.fI_emod, fI_mul, fX, hk.2.2.2]; rfl

/-- **The negation** on the path `n`, canonical; `Y` stays. -/
theorem stC (hs : Sems semA semB) (hk : DcK c m0) {E : Loc → V} {Y0 x : Fp} (n : Bool)
    (hY : FV (E (.fr Y)) Y0) (hX : FV (E (.fr X)) x) :
    FV (runC semA semB c m0 (if n then seg5R else []) E (.fr Y)) Y0 ∧
      FV (runC semA semB c m0 (if n then seg5R else []) E (.fr X)) (if n then 0 - x else x) := by
  cases n
  · exact ⟨hY, hX⟩
  · obtain ⟨zX, eX, fX⟩ := hX
    simp only [↓reduceIte]
    refine ⟨by rw [runC_keep _ E path_keep.2.2.2.1]; exact hY, ?_⟩
    rw [seg5R, runC_app, runC_frag hs]
    have h5 : fragE dcGeo c m0 E L5 (.fr X) = .f (xv c m0 cZero - zX) := by
      rw [L5, frag1]
      simp only [opT, List.map_cons, List.map_nil, lfT, tm0, Tm.ev, lfV, eX, xL, src_x, vop]
    refine ⟨_, canon_x hs h5, ?_⟩
    rw [Ed25519GeProg.fI_emod, fI_sub, fX, hk.1]

/-- **The output**: `x`, `y`, `1` and `x y` at `out`. -/
theorem stD (hs : Sems semA semB) (hk : DcK c m0) {E : Loc → V} {Y0 x : Fp}
    (hY : FV (E (.fr Y)) Y0) (hX : FV (E (.fr X)) x) :
    FV (runC semA semB c m0 seg6R E (.ex 0 0)) x ∧ FV (runC semA semB c m0 seg6R E (.ex 0 32)) Y0 ∧
      FV (runC semA semB c m0 seg6R E (.ex 0 64)) 1 ∧ FV (runC semA semB c m0 seg6R E (.ex 0 96)) (x * Y0) := by
  obtain ⟨zX, eX, fX⟩ := hX
  obtain ⟨zY, eY, fY⟩ := hY
  have cp : ∀ (o : Nat) (s : Src) (E' : Loc → V) (z : Int), Src.val dcGeo c m0 E' s = .f z →
      runC semA semB c m0 [cpR o s] E' (.ex 0 o) = .f z := fun o s E' z h => by
    show updOuts E' [(.ex 0 o, .fe)] (semA .copy [Src.val dcGeo c m0 E' s]) (.ex 0 o) = _
    rw [hs.copy, h]
    simp [updOuts, Ed25519FePow.paV]
  have k : ∀ l ∈ [Loc.fr X, .fr Y], runC semA semB c m0 (seg6R.take 3) E l = E l :=
    fun l hl => runC_keep _ E (path_keep.2.2.2.2.2.2.2.1 l hl)
  refine ⟨⟨zX, ?_, fX⟩, ⟨zY, ?_, fY⟩, ⟨_, ?_, hk.2.1⟩, ⟨zX * zY, ?_, by rw [fI_mul, fX, fY]⟩⟩
  · rw [show seg6R = [cpR 0 (vS X)] ++ seg6R.drop 1 from rfl, runC_app, runC_keep _ _ path_keep.2.2.2.2.1]
    exact cp 0 (vS X) E zX eX
  · rw [show seg6R = seg6R.take 1 ++ ([cpR 32 (vS Y)] ++ seg6R.drop 2) from rfl, runC_app, runC_app,
      runC_keep _ _ path_keep.2.2.2.2.2.1]
    have kY : runC semA semB c m0 (seg6R.take 1) E (.fr Y) = E (.fr Y) :=
      runC_keep _ E path_keep.2.2.2.2.2.2.2.2
    exact cp 32 (vS Y) _ zY (kY.trans eY)
  · rw [show seg6R = seg6R.take 2 ++ ([cpR 64 (xS cOne)] ++ seg6R.drop 3) from rfl, runC_app,
      runC_app, runC_keep _ _ fun r hr => by rw [List.mem_singleton.mp hr]; exact path_keep.2.2.2.2.2.2.1]
    exact cp 64 (xS cOne) _ _ rfl
  · rw [show seg6R = seg6R.take 3 ++ [mulR] from rfl, runC_app]
    show updOuts _ [(.ex 0 96, .fe)] (semA (.f .mul) [_, _]) (.ex 0 96) = _
    rw [hs.f]
    show updOuts _ [(.ex 0 96, .fe)] [faV .mul [runC semA semB c m0 (seg6R.take 3) E (.fr X),
      runC semA semB c m0 (seg6R.take 3) E (.fr Y)]] (.ex 0 96) = _
    rw [k _ (by simp), k _ (by simp), eX, eY]
    rfl


/-- The tests' path: the second candidate test (`v x² ≠ u`), the negation (parity not the sign). -/
def bOf (Y : Fp) : Bool := !decide (x0F Y * x0F Y * vvF Y = uF Y)
def nOf (Y : Fp) (sg : Nat) : Bool := !decide ((x1F Y (bOf Y)).val % 2 = sg)

/-- **`decodeCode`'s point**: `x2F` along the path, `y`, `1`, their product. -/
theorem code_some {y sg : Nat} {P : Ed25519EdwardsExtended.Ext Fp} (h : decodeCode y sg = some P) :
    P = ⟨x2F (toF y) (bOf (toF y)) (nOf (toF y) sg), toF y, 1, x2F (toF y) (bOf (toF y)) (nOf (toF y) sg) * toF y⟩ := by
  unfold decodeCode at h
  by_cases hp : p ≤ y
  · rw [ite_eq_left hp] at h; cases h
  rw [ite_eq_right hp] at h
  change (root (x0F (toF y)) (x0F (toF y) * x0F (toF y) * vvF (toF y)) (uF (toF y))).bind
    (fun x => finish x (toF y) sg) = some P at h
  generalize toF y = Y at h ⊢
  have fin : ∀ x, finish x Y sg = some P → P = ⟨if x.val % 2 = sg then x else 0 - x, Y, 1,
      (if x.val % 2 = sg then x else 0 - x) * Y⟩ := fun x hf => by
    unfold finish at hf
    by_cases h3 : x = 0 ∧ sg ≠ 0
    · rw [ite_eq_left h3] at hf; cases hf
    · rw [ite_eq_right h3] at hf; exact (Option.some.inj hf).symm
  unfold root at h
  by_cases h1 : x0F Y * x0F Y * vvF Y = uF Y
  · rw [ite_eq_left h1, Option.bind_some] at h
    have hb : bOf Y = false := by simp only [bOf, h1, decide_true, Bool.not_true]
    rw [fin _ h]
    by_cases h2 : (x0F Y).val % 2 = sg
    · have hn : nOf Y sg = false := by simp only [nOf, hb, x1F, Bool.false_eq_true, ↓reduceIte, h2, decide_true, Bool.not_true]
      simp only [x2F, x1F, hb, hn, h2, Bool.false_eq_true, ↓reduceIte]
    · have hn : nOf Y sg = true := by
        simp only [nOf, hb, x1F, Bool.false_eq_true, ↓reduceIte, h2, decide_false, Bool.not_false]
      simp only [x2F, x1F, hb, hn, h2, Bool.false_eq_true, ↓reduceIte]
  · rw [ite_eq_right h1] at h
    by_cases h1' : x0F Y * x0F Y * vvF Y = 0 - uF Y
    · rw [ite_eq_left h1', Option.bind_some] at h
      have hb : bOf Y = true := by simp only [bOf, h1, decide_false, Bool.not_false]
      rw [fin _ h]
      by_cases h2 : (x0F Y * sqrtM1).val % 2 = sg
      · have hn : nOf Y sg = false := by simp only [nOf, hb, x1F, ↓reduceIte, h2, decide_true, Bool.not_true]
        simp only [x2F, x1F, hb, hn, h2, Bool.false_eq_true, ↓reduceIte]
      · have hn : nOf Y sg = true := by simp only [nOf, hb, x1F, ↓reduceIte, h2, decide_false, Bool.not_false]
        simp only [x2F, x1F, hb, hn, h2, ↓reduceIte]
    · rw [ite_eq_right h1'] at h; cases h

/-- The updates along the path `b`, `n`. -/
def dcR (b n : Bool) : List (ROp DA DB) :=
  seg0R ++ seg1R ++ ((if b then seg2R ++ seg3R else []) ++ seg4R) ++ (if n then seg5R else []) ++ seg6R

/-- **`m0c_ge_decompress`'s outputs**: when `decodeCode` succeeds on the input's `y` and sign
bit, the updates along the path its tests select leave at `out` field values of its point. -/
theorem dc_val (hs : Sems semA semB) (hk : DcK c m0) (E0 : Loc → V) {P : Ed25519EdwardsExtended.Ext Fp}
    (h : decodeCode (yN c m0) (sgN c m0) = some P) :
    let E := runC semA semB c m0 (dcR (bOf (toF (yN c m0))) (nOf (toF (yN c m0)) (sgN c m0))) E0
    FV (E (.ex 0 0)) P.X ∧ FV (E (.ex 0 32)) P.Y ∧ FV (E (.ex 0 64)) P.Z ∧ FV (E (.ex 0 96)) P.T := by
  rw [code_some h]
  obtain ⟨aY, -, aX⟩ := stA hs hk E0
  show FV (runC semA semB c m0 (_ ++ seg6R) E0 _) _ ∧ FV (runC semA semB c m0 (_ ++ seg6R) E0 _) _ ∧
    FV (runC semA semB c m0 (_ ++ seg6R) E0 _) _ ∧ FV (runC semA semB c m0 (_ ++ seg6R) E0 _) _
  rw [runC_app, runC_app, runC_app]
  generalize runC semA semB c m0 (seg0R ++ seg1R) E0 = E1 at aY aX ⊢
  obtain ⟨bY, bX⟩ := stB hs hk (bOf (toF (yN c m0))) aY aX
  generalize runC semA semB c m0 ((if bOf (toF (yN c m0)) then seg2R ++ seg3R else []) ++ seg4R) E1 = E2 at bY bX ⊢
  obtain ⟨cY, cX⟩ := stC hs hk (nOf (toF (yN c m0)) (sgN c m0)) bY bX
  generalize runC semA semB c m0 (if nOf (toF (yN c m0)) (sgN c m0) then seg5R else []) E2 = E3 at cY cX ⊢
  have := stD hs hk cY cX
  simp only [x2F]
  exact this


/-- **`A`'s representation from `dec`'s success**: when the input bytes decode to `Q`, some `A`
that `Q` represents has the four field values at `out` as its `p3` values, along the path the
tests select. -/
theorem dec_rep (hs : Sems semA semB) (hk : DcK c m0) (E0 : Loc → V) {Q : Spec.Ed25519.Point}
    (h : Spec.Ed25519.decodePoint (inB c m0) = some Q) :
    let E := runC semA semB c m0 (dcR (bOf (toF (yN c m0))) (nOf (toF (yN c m0)) (sgN c m0))) E0
    ∃ A : Ed25519Group.EdPt, Ed25519Bridge.SpecRep Q A ∧ RepV [E (.ex 0 0), E (.ex 0 32), E (.ex 0 64), E (.ex 0 96)] A := by
  have hl : (inB c m0).length = 32 := Footprint.bytesAt_length _ _ _
  have hd := Ed25519Bytes.decodeInt_lt (inB c m0)
  rw [hl] at hd
  have e := Ed25519Decode.decodePoint_eq (inB c m0)
  rw [h, Option.map_some, Nat.mod_eq_of_lt (a := decodeInt (inB c m0) / 2 ^ 255) (by omega)] at e
  have hP : decodeCode (yN c m0) (sgN c m0) = some (Ed25519Bridge.ofSpec Q) := e.symm
  have hy : yN c m0 < p := by
    by_cases hp : p ≤ yN c m0
    · unfold decodeCode at hP; rw [ite_eq_left hp] at hP; cases hP
    · omega
  obtain ⟨A, hA, -, -⟩ := Ed25519Decode.rep_of_decode hy (by unfold sgN; omega) hP
  obtain ⟨⟨x, ex, fx⟩, ⟨y, ey, fy⟩, ⟨z, ez, fz⟩, ⟨t, et, ft⟩⟩ := dc_val hs hk E0 hP
  refine ⟨A, hA, x, y, z, t, by rw [ex, ey, ez, et], ?_⟩
  rw [fx, fy, fz, ft]
  exact hA


/-- **The constants from the code**: `m0c_ed_zero`'s `0`, `1`, `d` and `sqrt(−1)` at buffer `2`. -/
theorem dk_ok {base : Word} (b : Ed25519.Build) (hc : M0Crypto.Thumb.CodeAt m0 base b.bytes)
    (h2 : c.ptr 2 = base + BitVec.ofNat 32 M0Crypto.Artifacts.Ed25519Compact.ed_zero) : DcK c m0 := by
  obtain ⟨h0, h1, hd, hq⟩ := Ed25519DecompressVal.const_vals b hc
  have v : ∀ o, fI (xv c m0 o) =
      toF (Field25519Routines.feVal m0 (base + BitVec.ofNat 32 M0Crypto.Artifacts.Ed25519Compact.ed_zero + BitVec.ofNat 32 o)) :=
    fun o => by
      show fI ((Field25519Routines.feVal m0 (c.ptr 2 + BitVec.ofNat 32 o) : Nat) : Int) = _
      rw [h2, fI_nat]
  exact ⟨by rw [v]; exact h0, by rw [v]; exact h1, by rw [v]; exact hd, by rw [v]; exact hq⟩

end

end M0Crypto.Release.Ed25519DecompressOut
