import M0Crypto.Release.Ed25519GeCompressProg

/-!
# The point macros as call-program fragments

`ge_dbl`, `ge_add`, `signed_add` (its field part) and `ge_p1p1_to_p3` of `gen_ed25519.py` are
straight lines of `fop` calls to `m0c_fe_add`, `m0c_fe_sub`, `m0c_fe_mul` and `m0c_fe_sqr`. A
fragment is a list of `FOp`, each operand and destination an `Ld` loader; `fragP ι ops k` is its
`Prog` before `k` in any callee alphabet `A` that embeds the field callees by `ι`.

`fres G st ops` resolves a fragment at a static state `st`: per call, the typing of `Op.ty`, the
destination's location and the inputs' sources (views or a buffer's field elements). `frag_ev`:
where it resolves, the fragment's values are those of its symbolic run `symL` at every location.
Then a decided equation of the output locations' terms with a formula (`dblT`, `addT`, `p3T`) and
the representation of the inputs give the representation of the outputs, by the formulas of
`Ed25519Formulas` (`dbl_rep`, `madd_rep`, `cadd_rep`, `RepC.toExt`). Every hypothesis on `st` is
decidable, so one `decide` discharges a fragment's checks at each state a program types it at.
-/

namespace M0Crypto.Release.Ed25519GeProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519FePow (paS ioMul)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519EdwardsExtended (Ext Completed)
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Artifacts.Ed25519Compact (fe_add fe_sub)
open Lean.Grind (Ring)

/-! ## The field callees -/

inductive FA where
  | add | sub | mul | sqr
  deriving DecidableEq, Repr

/-- `m0c_fe_add` and `m0c_fe_sub` have `m0c_fe_mul`'s interface. -/
def faS : FA → CalleeS
  | .add => calleeAt fe_add ioMul [0, 1, 2]
  | .sub => calleeAt fe_sub ioMul [0, 1, 2]
  | .mul => paS .mul
  | .sqr => paS .sqr

/-- A binary operation on field values. -/
def vop (f : Int → Int → Int) : V → V → V
  | .f x, .f y => .f (f x y)
  | _, _ => .none

/-- The callees' values. -/
def faV : FA → List V → V
  | .add, [a, b] => vop (· + ·) a b
  | .sub, [a, b] => vop (· - ·) a b
  | .mul, [a, b] => vop (· * ·) a b
  | .sqr, [a] => vop (· * ·) a a
  | _, _ => .none

/-- `m0c_fe_pow`'s callees `mul` and `sqr` have these values. -/
theorem paV_mul (vs : List V) : Ed25519FePow.paV .mul vs = faV .mul vs := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> rfl

theorem paV_sqr (vs : List V) : Ed25519FePow.paV .sqr vs = faV .sqr vs := by
  rcases vs with _ | ⟨a, _ | ⟨b, vs⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> rfl

/-! ## Fragments -/

/-- `fop(g, a, d, s, t)`: `d` to `r0`, `s` to `r1`, `t` to `r2` (not for `sqr`), `bl`. -/
structure FOp where
  a : FA
  d : Ld
  s : Ld
  t : Ld := .K 0

def FOp.args (o : FOp) : List (LowReg × Ld) :=
  match o.a with
  | .sqr => [(0, o.d), (1, o.s)]
  | _ => [(0, o.d), (1, o.s), (2, o.t)]

section
variable {A Bk : Type}

/-- The fragment `ops` before `k`, with the field callees at `ι`. -/
def fragP (ι : FA → A) : List FOp → Prog A Bk → Prog A Bk
  | [], k => k
  | o :: os, k => .op (.call (ι o.a) o.args) (fragP ι os k)

end

/-! ## Symbolic runs -/

/-- A leaf: the value at a location before the fragment, or a buffer's field element. -/
inductive Lf where
  | view (l : Loc)
  | xf (r : SR)
  deriving DecidableEq, Repr

inductive Tm where
  | v (x : Lf)
  | add (a b : Tm)
  | sub (a b : Tm)
  | mul (a b : Tm)
  | bot
  deriving DecidableEq, Repr

def toLf : Src → Option Lf
  | .view l => some (.view l)
  | .extF r => some (.xf r)
  | _ => none

def opT : FA → List Tm → Tm
  | .add, [a, b] => .add a b
  | .sub, [a, b] => .sub a b
  | .mul, [a, b] => .mul a b
  | .sqr, [a] => .mul a a
  | _, _ => .bot

def Tm.ev (val : Lf → V) : Tm → V
  | .v x => val x
  | .add a b => vop (· + ·) (a.ev val) (b.ev val)
  | .sub a b => vop (· - ·) (a.ev val) (b.ev val)
  | .mul a b => vop (· * ·) (a.ev val) (b.ev val)
  | .bot => .none

theorem opT_ev (val : Lf → V) (a : FA) (ts : List Tm) : (opT a ts).ev val = faV a (ts.map (Tm.ev val)) := by
  cases a <;> rcases ts with _ | ⟨x, _ | ⟨y, _ | ⟨z, ts⟩⟩⟩ <;> rfl

/-- A resolved fragment: per call, the destination, the callee and the input leaves. -/
abbrev FL := List (Loc × FA × List Lf)

def lfT (cur : Loc → Tm) : Lf → Tm
  | .view l => cur l
  | .xf r => .v (.xf r)

def stepT (cur : Loc → Tm) (p : Loc × FA × List Lf) : Loc → Tm :=
  fun x => if x = p.1 then opT p.2.1 (p.2.2.map (lfT cur)) else cur x

/-- The terms at every location after the calls `L`, from `cur`. -/
def symL : (Loc → Tm) → FL → Loc → Tm
  | cur, [] => cur
  | cur, p :: L => symL (stepT cur p) L

/-- Every location holds its value before the fragment. -/
def tm0 : Loc → Tm := fun l => .v (.view l)

/-- **A fragment resolved at a static state**: per call, `Op.ty`'s checks, one field-element
output and inputs that are views or buffer field elements; and the state after it. -/
def fres (G : Geo) : St → List FOp → Option (FL × St)
  | st, [] => some ([], st)
  | st, o :: os =>
    if ldsRes st.Γ o.args && pubsOk st.Γ (regsOf st.Γ st.σ o.args) (faS o.a).pubs &&
        decide (G.top + (faS o.a).stack ≤ G.N) then
      match ioRes G st (regsOf st.Γ st.σ o.args) (faS o.a).io with
      | some r => match r.outs, r.srcs.mapM toLf with
        | [(l, .fe)], some ls => (fres G (r.after st σsp) os).map fun p => ((l, o.a, ls) :: p.1, p.2)
        | _, _ => none
      | none => none
    else none

/-- The leaves' values, from the values `E` before the fragment. -/
def lfV (G : Geo) (c : Ctx) (m0 : Mem) (E : Loc → V) : Lf → V
  | .view l => E l
  | .xf r => Src.val G c m0 E (.extF r)

/-- The values after a resolved fragment `L`. -/
def fragE (G : Geo) (c : Ctx) (m0 : Mem) (E : Loc → V) (L : FL) : Loc → V :=
  fun l => (symL tm0 L l).ev (lfV G c m0 E)

section
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V}
  {semB : Bk → List V → List V} {c : Ctx} {m0 : Mem} {ι : FA → A}

theorem srcs_val (E0 : Loc → V) {cur : Loc → Tm} {E : Loc → V}
    (hE : ∀ l, E l = (cur l).ev (lfV G c m0 E0)) :
    ∀ (srcs : List Src) (ls : List Lf), srcs.mapM toLf = some ls →
      srcs.map (Src.val G c m0 E) = ls.map fun x => (lfT cur x).ev (lfV G c m0 E0)
  | [], ls, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | s :: ss, ls, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    rw [List.map_cons, List.map_cons, srcs_val E0 hE ss xs hxs]
    congr 1
    cases s <;> simp only [toLf, reduceCtorEq, Option.some.injEq] at hx <;> subst hx
    · exact hE _
    · rfl

/-- **A resolved fragment's values**: those of its symbolic run, at every location. -/
theorem frag_ev (hE : ∀ a, cE (ι a) = faS a) (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) (E0 : Loc → V)
    (k : Prog A Bk) : ∀ (ops : List FOp) (st st' : St) (L : FL) (cur : Loc → Tm) (E : Loc → V),
      fres G st ops = some (L, st') → (∀ l, E l = (cur l).ev (lfV G c m0 E0)) →
      (fragP ι ops k).ev cE bE G semA semB c m0 st E =
        k.ev cE bE G semA semB c m0 st' (fun l => (symL cur L l).ev (lfV G c m0 E0))
  | [], st, st', L, cur, E, h, hE' => by
    simp only [fres, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [fragP, symL]; rw [show E = _ from funext hE']
  | o :: os, st, st', L, cur, E, h, hE' => by
    simp only [fres] at h
    split at h
    · rename_i hc
      split at h
      · rename_i r hr
        split at h
        · rename_i l ls ho hl
          obtain ⟨⟨L', st''⟩, hL', he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          have hty : (Op.call (ι o.a) o.args : Op A Bk).ty cE bE G st = some (r.after st σsp) := by
            simp only [Op.ty, hE, hc, ↓reduceIte, hr, Option.map_some]
          simp only [fragP]
          rw [Prog.ev_op hty]
          refine frag_ev hE hS E0 k os _ _ L' _ _ hL' fun x => ?_
          simp only [Op.ev, hE, hr, hS, ho, updOuts, stepT]
          split
          · rw [opT_ev, List.map_map, srcs_val E0 hE' r.srcs ls hl]; rfl
          · exact hE' x
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- `frag_ev` from the values before the fragment. -/
theorem frag_ev0 (hE : ∀ a, cE (ι a) = faS a) (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) {ops : List FOp}
    {st st' : St} {L : FL} (h : fres G st ops = some (L, st')) (k : Prog A Bk) (E : Loc → V) :
    (fragP ι ops k).ev cE bE G semA semB c m0 st E = k.ev cE bE G semA semB c m0 st' (fragE G c m0 E L) :=
  frag_ev hE hS E k ops st st' L tm0 E h fun _ => rfl

end

/-! ## Values in `F_p` -/

/-- `z mod p` in `F_p`. -/
def fI (z : Int) : Fp := @Int.cast Fp Ring.intCast z

theorem fI_add (a b : Int) : fI (a + b) = fI a + fI b := Ring.intCast_add a b
theorem fI_sub (a b : Int) : fI (a - b) = fI a - fI b := Ring.intCast_sub a b
theorem fI_mul (a b : Int) : fI (a * b) = fI a * fI b := Ring.intCast_mul a b

theorem fI_nat (n : Nat) : fI (n : Int) = toF n := by
  rw [fI, Ring.intCast_natCast]; rfl

theorem fI_p : fI Field25519Congr.p = 0 := by
  rw [show Field25519Congr.p = ((2 ^ 255 - 19 : Nat) : Int) by decide, fI_nat]; decide

theorem fI_emod (a : Int) : fI (a % Field25519Congr.p) = fI a := by
  rw [Int.emod_def, fI_sub, fI_mul, fI_p, Lean.Grind.Semiring.zero_mul]; grind

theorem fI_modP {a b : Int} (h : ModP a b) : fI a = fI b := by
  rw [← fI_emod a, ← fI_emod b]; exact congrArg fI h

/-- A field value in `F_p` (`0` for any other value). -/
def vF : V → Fp
  | .f z => fI z
  | _ => 0

def isF : V → Bool
  | .f _ => true
  | _ => false

def Tm.evF (w : Lf → Fp) : Tm → Fp
  | .v x => w x
  | .add a b => a.evF w + b.evF w
  | .sub a b => a.evF w - b.evF w
  | .mul a b => a.evF w * b.evF w
  | .bot => 0

def Tm.ok : Tm → Bool
  | .v _ => true
  | .add a b | .sub a b | .mul a b => a.ok && b.ok
  | .bot => false

def Tm.lvs : Tm → List Lf
  | .v x => [x]
  | .add a b | .sub a b | .mul a b => a.lvs ++ b.lvs
  | .bot => []

theorem isF_iff {v : V} : isF v = true ↔ ∃ z, v = .f z := by
  cases v <;> simp [isF]

/-- A term of field leaves is a field value, its leaves' arithmetic in `F_p`. -/
theorem Tm.ev_ok (val : Lf → V) : ∀ t : Tm, t.ok = true → (∀ x ∈ t.lvs, isF (val x) = true) →
    isF (t.ev val) = true ∧ vF (t.ev val) = t.evF (vF ∘ val)
  | .v x, _, h => ⟨h x (List.mem_singleton_self _), rfl⟩
  | .bot, h, _ => absurd h (by simp [Tm.ok])
  | .add a b, h, hl | .sub a b, h, hl | .mul a b, h, hl => by
    simp only [Tm.ok, Bool.and_eq_true] at h
    obtain ⟨ha, ea⟩ := Tm.ev_ok val a h.1 fun x hx => hl x (by simp [Tm.lvs, hx])
    obtain ⟨hb, eb⟩ := Tm.ev_ok val b h.2 fun x hx => hl x (by simp [Tm.lvs, hx])
    obtain ⟨za, hza⟩ := isF_iff.mp ha
    obtain ⟨zb, hzb⟩ := isF_iff.mp hb
    rw [hza] at ea; rw [hzb] at eb
    simp only [Tm.ev, Tm.evF, hza, hzb, vop, isF, vF, fI_add, fI_sub, fI_mul, true_and] at ea eb ⊢
    rw [ea, eb]

/-! ## The point forms of values -/

/-- Four field values representing `A` as `p3`. -/
def RepV (vs : List V) (A : EdPt) : Prop :=
  ∃ x y z t, vs = [.f x, .f y, .f z, .f t] ∧ Rep ⟨fI x, fI y, fI z, fI t⟩ A

/-- Three field values `X`, `Y`, `Z` representing `A` (`p2`: the `T` slot is not read). -/
def Rep2V (vs : List V) (A : EdPt) : Prop :=
  ∃ x y z, vs = [.f x, .f y, .f z] ∧ Rep2 ⟨fI x, fI y, fI z, 0⟩ A

/-- Four field values representing `A` as `p1p1`. -/
def RepCV (vs : List V) (A : EdPt) : Prop :=
  ∃ x y z t, vs = [.f x, .f y, .f z, .f t] ∧ RepC ⟨fI x, fI y, fI z, fI t⟩ A

/-- Three field values, the Niels form of `Q`. -/
def NielsV (vs : List V) (Q : EdPt) : Prop :=
  ∃ a b e, vs = [.f a, .f b, .f e] ∧ (⟨fI a, fI b, fI e⟩ : Niels Fp) = Niels.of d2 Q.pt

/-- Four field values, the cached form of a representative of `Q`. -/
def CachedV (vs : List V) (Q : EdPt) : Prop :=
  ∃ a b z t, vs = [.f a, .f b, .f z, .f t] ∧ ∃ G : Ext Fp, Rep G Q ∧ (⟨fI a, fI b, fI z, fI t⟩ : Cached Fp) = Cached.of d2 G

/-- `p3` to `p2`: drop `T`. -/
theorem RepV.rep2 {x y z t : V} {A : EdPt} (h : RepV [x, y, z, t] A) : Rep2V [x, y, z] A := by
  obtain ⟨x, y, z, t, he, hr⟩ := h
  simp only [List.cons.injEq, and_true] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  exact ⟨x, y, z, rfl, hr.1.1, hr.2⟩

/-- `p2` with a correct `T` to `p3`. -/
theorem Rep2V.rep {x y z t : Int} {A : EdPt} (h : Rep2V [.f x, .f y, .f z] A)
    (ht : fI x * fI y = fI z * fI t) : RepV [.f x, .f y, .f z, .f t] A := by
  obtain ⟨x', y', z', he, hr⟩ := h
  simp only [List.cons.injEq, V.f.injEq, and_true] at he; obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨_, _, _, t, rfl, ⟨hr.1, ht⟩, hr.2⟩

/-- The extended coordinates at `a` from field values that the memory holds modulo `p`. -/
theorem extAt_eq {m : Mem} {a : Word} {x y z t : Int}
    (hx : ModP (feVal m (a + BitVec.ofNat 32 0)) x) (hy : ModP (feVal m (a + BitVec.ofNat 32 32)) y)
    (hz : ModP (feVal m (a + BitVec.ofNat 32 64)) z) (ht : ModP (feVal m (a + BitVec.ofNat 32 96)) t) :
    Ed25519GeCompressProg.extAt m a = ⟨fI x, fI y, fI z, fI t⟩ := by
  simp only [Ed25519GeCompressProg.extAt, Ed25519GeCompressProg.CX, Ed25519GeCompressProg.CY,
    Ed25519GeCompressProg.CZ, Ed25519GeCompressProg.CT, ← fI_nat, fI_modP hx, fI_modP hy, fI_modP hz, fI_modP ht]

/-- **`PtR` from field values**: the memory at `a` holds `p3` values that represent `P`'s point. -/
theorem ptR_of {m : Mem} {a : Word} {x y z t : Int} {P : Spec.Ed25519.Point} {A : EdPt}
    (hx : ModP (feVal m (a + BitVec.ofNat 32 0)) x) (hy : ModP (feVal m (a + BitVec.ofNat 32 32)) y)
    (hz : ModP (feVal m (a + BitVec.ofNat 32 64)) z) (ht : ModP (feVal m (a + BitVec.ofNat 32 96)) t)
    (hP : SpecRep P A) (hA : RepV [.f x, .f y, .f z, .f t] A) : Ed25519GeCompressProg.PtR m a P := by
  obtain ⟨x', y', z', t', he, hr⟩ := hA
  simp only [List.cons.injEq, V.f.injEq, and_true] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  exact ⟨A, hP, by rw [extAt_eq hx hy hz ht]; exact hr⟩

/-- **The values at a memory point**: `PtR` gives `p3` values of the coordinates read modulo `p`. -/
theorem repV_of {m : Mem} {a : Word} {x y z t : Int} {P : Spec.Ed25519.Point}
    (hx : ModP (feVal m (a + BitVec.ofNat 32 0)) x) (hy : ModP (feVal m (a + BitVec.ofNat 32 32)) y)
    (hz : ModP (feVal m (a + BitVec.ofNat 32 64)) z) (ht : ModP (feVal m (a + BitVec.ofNat 32 96)) t)
    (h : Ed25519GeCompressProg.PtR m a P) : ∃ A, SpecRep P A ∧ RepV [.f x, .f y, .f z, .f t] A := by
  obtain ⟨A, hP, hr⟩ := h
  rw [extAt_eq hx hy hz ht] at hr
  exact ⟨A, hP, x, y, z, t, rfl, hr⟩

/-! ## The formulas as terms -/

/-- `ge_dbl`'s outputs `t0`–`t3` from `X`, `Y`, `Z`. -/
def dblT (X Y Z : Tm) : List Tm :=
  let a := Tm.mul X X
  let b := Tm.mul Y Y
  let c := Tm.mul Z Z
  let c := Tm.add c c
  let dd := Tm.add X Y
  let dd := Tm.mul dd dd
  let t1 := Tm.add b a
  let t2 := Tm.sub b a
  [.sub dd t1, t1, t2, .sub c t2]

/-- `ge_add`'s outputs `t0`–`t3` from `r = (X, Y, Z, T)` and the entry `e` (Niels: `e0`–`e2`;
cached: `e0`–`e3`). -/
def addT (cached neg : Bool) (X Y Z T e0 e1 e2 e3 : Tm) : List Tm :=
  let ypx := if neg then e1 else e0
  let ymx := if neg then e0 else e1
  let a := Tm.mul (.add Y X) ypx
  let b := Tm.mul (.sub Y X) ymx
  let cc := Tm.mul T (if cached then e3 else e2)
  let dd := if cached then Tm.add (.mul Z e2) (.mul Z e2) else Tm.add Z Z
  if neg then [.sub a b, .add a b, .sub dd cc, .add dd cc] else [.sub a b, .add a b, .add dd cc, .sub dd cc]

/-- `ge_p1p1_to_p3`'s outputs `r0`–`r3` (`r0`–`r2` without `T`) from `t`. -/
def p3T (withT : Bool) (X Y Z T : Tm) : List Tm :=
  [.mul X T, .mul Y Z, .mul Z T] ++ (if withT then [.mul X Y] else [])

/-! ## The generator's fragments -/

section
open Ld

/-- `ge_dbl(f, r, t)` with frame slots `A`–`D` at `a`–`d`. -/
def dblOps (a b c d : Nat) (r0 r1 r2 t0 t1 t2 t3 : Ld) : List FOp :=
  [⟨.sqr, S a, r0, .K 0⟩, ⟨.sqr, S b, r1, .K 0⟩, ⟨.sqr, S c, r2, .K 0⟩, ⟨.add, S c, S c, S c⟩,
   ⟨.add, S d, r0, r1⟩, ⟨.sqr, S d, S d, .K 0⟩, ⟨.add, t1, S b, S a⟩, ⟨.sub, t2, S b, S a⟩,
   ⟨.sub, t0, S d, t1⟩, ⟨.sub, t3, S c, t2⟩]

/-- `ge_add(f, r, e, t, cached, neg)` with frame slots `A`–`D` at `a`–`d` (`e3` unused for a Niels
entry). -/
def addOps (cached neg : Bool) (a b c d : Nat) (r0 r1 r2 r3 e0 e1 e2 e3 t0 t1 t2 t3 : Ld) : List FOp :=
  let ypx := if neg then e1 else e0
  let ymx := if neg then e0 else e1
  [⟨.add, S a, r1, r0⟩, ⟨.sub, S b, r1, r0⟩, ⟨.mul, S a, S a, ypx⟩, ⟨.mul, S b, S b, ymx⟩,
   ⟨.mul, S c, r3, if cached then e3 else e2⟩] ++
  (if cached then [⟨.mul, S d, r2, e2⟩, ⟨.add, S d, S d, S d⟩] else [⟨.add, S d, r2, r2⟩]) ++
  [⟨.sub, t0, S a, S b⟩, ⟨.add, t1, S a, S b⟩, ⟨if neg then .sub else .add, t2, S d, S c⟩,
   ⟨if neg then .add else .sub, t3, S d, S c⟩]

/-- `signed_add(f, r, t, digit_slot, cached)` after its pointer block: `ge_add` with the entry
through the frame words `EA`, `EB`, `EP` and the last two destinations through `TZ`, `TT`. -/
def saOps (cached : Bool) (a b c d ea eb ep tz tt : Nat) (r0 r1 r2 r3 t0 t1 : Ld) : List FOp :=
  addOps cached false a b c d r0 r1 r2 r3 (W ea 0) (W eb 0) (W ep 64) (W ep 96) t0 t1 (W tz 0) (W tt 0)

/-- `ge_p1p1_to_p3(t, r, with_t)`. -/
def p3Ops (withT : Bool) (t0 t1 t2 t3 r0 r1 r2 r3 : Ld) : List FOp :=
  [⟨.mul, r0, t0, t3⟩, ⟨.mul, r1, t1, t2⟩, ⟨.mul, r2, t2, t3⟩] ++ (if withT then [⟨.mul, r3, t0, t1⟩] else [])

end

/-! ## The values of the formulas -/

section
variable {val : Lf → V}

theorem map_ev {L : FL} {o : List Loc} {ts : List Tm} (h : o.map (symL tm0 L) = ts) :
    o.map (fun l => (symL tm0 L l).ev val) = ts.map (Tm.ev val) := by
  rw [← h, List.map_map]; rfl

/-- `Tm.ev_ok` at a term whose leaves are field values `x`. -/
theorem ev_f {t : Tm} (ho : t.ok = true) (hl : ∀ x ∈ t.lvs, isF (val x) = true) :
    ∃ z, t.ev val = .f z ∧ fI z = t.evF (vF ∘ val) := by
  obtain ⟨h1, h2⟩ := Tm.ev_ok val t ho hl
  obtain ⟨z, hz⟩ := isF_iff.mp h1
  exact ⟨z, hz, by rw [hz] at h2; exact h2⟩

theorem isF_f {v : V} {z : Int} (h : v = .f z) : isF v = true := by rw [h]; rfl

theorem vF_f {v : V} {z : Int} (h : v = .f z) : vF v = fI z := by rw [h]; rfl

end

section
variable {val : Lf → V}

/-- Terms of field leaves are field values, their arithmetic in `F_p`. -/
theorem evs_f : ∀ {ts : List Tm}, (∀ t ∈ ts, t.ok = true ∧ ∀ x ∈ t.lvs, isF (val x) = true) →
    ∃ zs : List Int, ts.map (Tm.ev val) = zs.map .f ∧ zs.map fI = ts.map (Tm.evF (vF ∘ val))
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: ts, h => by
    obtain ⟨z, e, f⟩ := ev_f (h t (.head _)).1 (h t (.head _)).2
    obtain ⟨zs, es, fs⟩ := evs_f fun u hu => h u (.tail _ hu)
    exact ⟨z :: zs, by simp only [List.map_cons, e, es], by simp only [List.map_cons, f, fs]⟩

/-- Four terms of field leaves, whose arithmetic in `F_p` represents `A` as `p1p1`. -/
theorem repCV_of {t0 t1 t2 t3 : Tm} {A : EdPt}
    (h : ∀ t ∈ [t0, t1, t2, t3], t.ok = true ∧ ∀ x ∈ t.lvs, isF (val x) = true)
    (hr : RepC ⟨t0.evF (vF ∘ val), t1.evF (vF ∘ val), t2.evF (vF ∘ val), t3.evF (vF ∘ val)⟩ A) :
    RepCV ([t0, t1, t2, t3].map (Tm.ev val)) A := by
  obtain ⟨zs, es, fs⟩ := evs_f h
  rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp only [List.map, List.cons.injEq,
    List.ne_cons_self, List.cons_ne_nil, and_false, reduceCtorEq] at fs
  obtain ⟨fa, fb, fc, fd, -⟩ := fs
  exact ⟨a, b, c, d, es, by rw [fa, fb, fc, fd]; exact hr⟩

theorem repV_of_terms {t0 t1 t2 t3 : Tm} {A : EdPt}
    (h : ∀ t ∈ [t0, t1, t2, t3], t.ok = true ∧ ∀ x ∈ t.lvs, isF (val x) = true)
    (hr : Rep ⟨t0.evF (vF ∘ val), t1.evF (vF ∘ val), t2.evF (vF ∘ val), t3.evF (vF ∘ val)⟩ A) :
    RepV ([t0, t1, t2, t3].map (Tm.ev val)) A := by
  obtain ⟨zs, es, fs⟩ := evs_f h
  rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp only [List.map, List.cons.injEq,
    List.ne_cons_self, List.cons_ne_nil, and_false, reduceCtorEq] at fs
  obtain ⟨fa, fb, fc, fd, -⟩ := fs
  exact ⟨a, b, c, d, es, by rw [fa, fb, fc, fd]; exact hr⟩

theorem rep2V_of_terms {t0 t1 t2 : Tm} {A : EdPt}
    (h : ∀ t ∈ [t0, t1, t2], t.ok = true ∧ ∀ x ∈ t.lvs, isF (val x) = true)
    (hr : Rep2 ⟨t0.evF (vF ∘ val), t1.evF (vF ∘ val), t2.evF (vF ∘ val), 0⟩ A) :
    Rep2V ([t0, t1, t2].map (Tm.ev val)) A := by
  obtain ⟨zs, es, fs⟩ := evs_f h
  rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp only [List.map, List.cons.injEq,
    List.ne_cons_self, List.cons_ne_nil, and_false, reduceCtorEq] at fs
  obtain ⟨fa, fb, fc, -⟩ := fs
  exact ⟨a, b, c, es, by rw [fa, fb, fc]; exact hr⟩

variable {L : FL} {o : List Loc} {A Q : EdPt}

/-- **`ge_dbl`**: from `p2` values of `A`, `p1p1` values of `2A`. -/
theorem dbl_val {X Y Z : Lf} (h : o.map (symL tm0 L) = dblT (.v X) (.v Y) (.v Z))
    (hA : Rep2V [val X, val Y, val Z] A) : RepCV (o.map fun l => (symL tm0 L l).ev val) (A + A) := by
  rw [map_ev h]
  obtain ⟨x, y, z, he, hr⟩ := hA
  simp only [List.cons.injEq, and_true] at he; obtain ⟨ex, ey, ez⟩ := he
  refine repCV_of (by simp [Tm.ok, Tm.lvs, isF_f ex, isF_f ey, isF_f ez]) ?_
  have := dbl_rep hr
  simp only [Tm.evF, Function.comp, vF_f ex, vF_f ey, vF_f ez]
  exact this

/-- **`ge_add` with a Niels entry**: from `p3` values of `A` and the Niels values of `Q`, `p1p1`
values of `A + Q` (`A − Q` for `neg`). -/
theorem madd_val {X Y Z T e0 e1 e2 : Lf} {neg : Bool}
    (h : o.map (symL tm0 L) = addT false neg (.v X) (.v Y) (.v Z) (.v T) (.v e0) (.v e1) (.v e2) .bot)
    (hA : RepV [val X, val Y, val Z, val T] A) (hQ : NielsV [val e0, val e1, val e2] Q) :
    RepCV (o.map fun l => (symL tm0 L l).ev val) (if neg then A - Q else A + Q) := by
  rw [map_ev h]
  obtain ⟨x, y, z, t, he, hr⟩ := hA
  obtain ⟨a, b, e, hf, hn⟩ := hQ
  simp only [List.cons.injEq, and_true] at he hf; obtain ⟨ex, ey, ez, et⟩ := he; obtain ⟨ea, eb, ee⟩ := hf
  have := madd_rep hr Q neg
  rw [← hn] at this
  cases neg <;> refine repCV_of (by simp [Tm.ok, Tm.lvs, isF_f ex, isF_f ey, isF_f ez, isF_f et,
    isF_f ea, isF_f eb, isF_f ee]) ?_ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Tm.evF, Function.comp, vF_f ex, vF_f ey, vF_f ez, vF_f et, vF_f ea, vF_f eb, vF_f ee] <;> exact this

/-- **`ge_add` with a cached entry**: from `p3` values of `A` and cached values of `Q`, `p1p1`
values of `A + Q` (`A − Q` for `neg`). -/
theorem cadd_val {X Y Z T e0 e1 e2 e3 : Lf} {neg : Bool}
    (h : o.map (symL tm0 L) = addT true neg (.v X) (.v Y) (.v Z) (.v T) (.v e0) (.v e1) (.v e2) (.v e3))
    (hA : RepV [val X, val Y, val Z, val T] A) (hQ : CachedV [val e0, val e1, val e2, val e3] Q) :
    RepCV (o.map fun l => (symL tm0 L l).ev val) (if neg then A - Q else A + Q) := by
  rw [map_ev h]
  obtain ⟨x, y, z, t, he, hr⟩ := hA
  obtain ⟨a, b, w, u, hf, G, hG, hc⟩ := hQ
  simp only [List.cons.injEq, and_true] at he hf; obtain ⟨ex, ey, ez, et⟩ := he
  obtain ⟨ea, eb, ew, eu⟩ := hf
  have := cadd_rep hr hG neg
  rw [← hc] at this
  cases neg <;> refine repCV_of (by simp [Tm.ok, Tm.lvs, isF_f ex, isF_f ey, isF_f ez, isF_f et,
    isF_f ea, isF_f eb, isF_f ew, isF_f eu]) ?_ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Tm.evF, Function.comp, vF_f ex, vF_f ey, vF_f ez, vF_f et, vF_f ea, vF_f eb, vF_f ew, vF_f eu] <;>
    exact this

/-- **`ge_p1p1_to_p3` with `T`**: `p3` values of the point the `p1p1` values represent. -/
theorem p3_val {X Y Z T : Lf} (h : o.map (symL tm0 L) = p3T true (.v X) (.v Y) (.v Z) (.v T))
    (hA : RepCV [val X, val Y, val Z, val T] A) : RepV (o.map fun l => (symL tm0 L l).ev val) A := by
  rw [map_ev h]
  obtain ⟨x, y, z, t, he, hr⟩ := hA
  simp only [List.cons.injEq, and_true] at he; obtain ⟨ex, ey, ez, et⟩ := he
  refine repV_of_terms (by simp [Tm.ok, Tm.lvs, isF_f ex, isF_f ey, isF_f ez, isF_f et]) ?_
  have := hr.toExt
  simp only [Tm.evF, Function.comp, vF_f ex, vF_f ey, vF_f ez, vF_f et]
  exact this

/-- **`ge_p1p1_to_p3` without `T`**: `p2` values of the point the `p1p1` values represent. -/
theorem p2_val {X Y Z T : Lf} (h : o.map (symL tm0 L) = p3T false (.v X) (.v Y) (.v Z) (.v T))
    (hA : RepCV [val X, val Y, val Z, val T] A) : Rep2V (o.map fun l => (symL tm0 L l).ev val) A := by
  rw [map_ev h]
  obtain ⟨x, y, z, t, he, hr⟩ := hA
  simp only [List.cons.injEq, and_true] at he; obtain ⟨ex, ey, ez, et⟩ := he
  refine rep2V_of_terms (by simp [Tm.ok, Tm.lvs, isF_f ex, isF_f ey, isF_f ez, isF_f et]) ?_
  have := hr.toExt2 0
  simp only [Tm.evF, Function.comp, vF_f ex, vF_f ey, vF_f ez, vF_f et]
  exact this

end

end M0Crypto.Release.Ed25519GeProg
