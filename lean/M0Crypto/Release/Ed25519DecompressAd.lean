import M0Crypto.Release.Ed25519DecompressStitch
import M0Crypto.Release.Ed25519FeEqZ
import M0Crypto.Release.Ed25519GeField
import M0Crypto.Release.Ed25519GeCompressProg

/-!
# The adapters of `m0c_ge_decompress`'s body

* `ldTD`, `ldTZ`: the load block with the `y ≥ p` test, `Z` clear (`bne`) exactly when the
  input's `y` is not below `p`;
* `eqAdE`: `m0c_fe_eq` with its effect, for the straight lines (which do not call it);
* `daAd`: the straight lines' callees, whose values are those of `Ed25519DecompressOut.Sems`.
-/

namespace M0Crypto.Release.Ed25519DecompressStitch

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb (execAll execAll_append ofNat_add_assoc)
open M0Crypto.Release.Routine (sregions)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.BlockEffect (Eff effOk eff_run)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519PrimeCert (p)
open M0Crypto.Artifacts.Ed25519Compact (fe_eq)

/-! ## The load block with its test -/

/-- The load keeps `sp`. -/
def eL : Eff := { clob := [0, 1, 2, 3, 4, 5, 6, 7], mem := none }
theorem eL_ok : effOk loadG eL = true := by decide +kernel

theorem load_sp (t : State) : (execAll loadG t).regs 13 = t.regs 13 :=
  (eff_run eL_ok t).reg 13 (by decide) (by decide)

/-- The input apart from `Y`, by `apt`. -/
theorem load_sep {c : Ctx} {sp : Word} {t : State} (hpv : PreV ioLoad c sp t.regs) :
    ∀ o < 32, ∀ q < 32, t.regs 13 + BitVec.ofNat 32 (Y + o) ≠ t.regs 1 + BitVec.ofNat 32 q := by
  have hs := hpv.2.2 _ (List.mem_singleton_self _)
  simp only [rgnsC, SRgn.rgnC, ALen.val, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    show (32 = 0) = False from by decide, ite_false] at hs
  intro o ho q hq he
  refine hs.not_has (y := t.regs 13 + BitVec.ofNat 32 (Y + o)) ⟨_, List.mem_singleton_self _, o, ho, ?_⟩
    ⟨_, List.mem_singleton_self _, q, hq, ?_⟩
  · exact (ofNat_add_assoc _ _ _).symm
  · rw [he, BitVec.add_zero]

/-- After the load, `Y` holds the input's `y`, below `2^255`; the test keeps memory and sets `Z`
exactly when `y < p`. -/
theorem ldT_run {c : Ctx} {sp : Word} {t : State} (hpv : PreV ioLoad c sp t.regs) :
    (execAll (loadG ++ ypG) t).mem = (execAll loadG t).mem ∧
    (execAll (loadG ++ ypG) t).z = decide (decodeInt (bytesAt t.mem (t.regs 1) 32) % 2 ^ 255 < p) := by
  have hY := (load_run t (load_sep hpv)).1
  rw [← load_sp t] at hY
  have hy := yp_run (execAll loadG t) (by rw [hY]; exact Nat.mod_lt _ (by decide))
  rw [hY] at hy
  rw [execAll_append]
  refine ⟨hy.2, ?_⟩
  cases hz : (execAll ypG (execAll loadG t)).z
  · exact (decide_eq_false (Nat.not_lt.mpr (hy.1.mp hz))).symm
  · exact (decide_eq_true (Nat.lt_of_not_le fun h => by have := hy.1.mpr h; rw [hz] at this; cases this)).symm

theorem ldT_in {Rs : Rels} {c : Ctx} {sp : Word} {t : State} {vs : List V} (hin : InsRel Rs c sp ioLoad t vs) :
    vs = [.b (bytesAt t.mem (t.regs 1) 32)] := by
  rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, ioLoad, and_true, and_false, In.kd, ALen.val] at hin
  obtain ⟨l, rfl, hl⟩ := rel_bytes Rs hin
  rw [BitVec.add_zero] at hl
  rw [hl]

variable (Rs : Rels)

/-- **The load block with the test**: the load's values. -/
def ldTD : Bd Rs (dxS .loadT) :=
  ⟨loadV, fun c sp t vs _ _ hpv hin => by
      show OutsRel Rs c sp ioLoad t (execAll (loadG ++ ypG) t).mem _
      rw [(ldT_run hpv).1]
      exact load_post Rs c sp t vs hpv hin,
    fun _ _ _ _ _ _ _ _ _ h => by simp [dxS, ioLoad] at h⟩

/-- The test: the input's `y` below `p`. -/
def ldOk : List V → Bool
  | [.b l] => decide (decodeInt l % 2 ^ 255 < p)
  | _ => false

/-- **The `y ≥ p` test**: `Z` clear exactly when the input's `y` is not below `p`. -/
def ldTZ : ZB Rs (ldTD Rs) where
  cc := NE
  ok := ldOk
  okf := fun _ _ t vs _ _ hpv hin => by
    rw [ldT_in hin]
    show (!(execAll (loadG ++ ypG) t).z) = _
    rw [(ldT_run hpv).2]
    rfl
  co := []
  csem := fun _ => []
  vpre := fun _ => True
  cpost := fun _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel, All2]

/-! ## The callees -/

/-- **`m0c_fe_eq` with its effect** in build `b`: no values. -/
noncomputable def eqAdE (b : Build) : AdE Rs (cb := b.codeBytes) Ed25519FeEq.eqS :=
  letI := b.codeBytes
  Ad.ofTSpec { Ed25519FeEq.eqR with code := footprint fe_eq } rfl rfl (by decide +kernel)
    ((Ed25519FeEq.eq_te b).code (footprint fe_eq) (by decide +kernel)) (fun base p tr h => Ed25519FeEq.eq_eff base p tr h)
    (fun _ => [])
    (fun _ _ _ _ _ hg _ _ => ⟨hg.1 0 (by simp [Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq]),
      hg.1 1 (by simp [Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq]),
      hg.1 2 (by simp [Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq])⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq, Ed25519FeEq.eqR,
      Ed25519Leaf.leafR, sregions, Ed25519FeCanon.rg0, Sym.SExpr.denote])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq, Ed25519FeEq.eqR,
      Ed25519Leaf.leafR, sregions, Ed25519FeEq.ab, Ed25519FeCanon.rg0, Sym.SExpr.denote])
    (fun _ _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, Ed25519FeEq.eqS, calleeAt, Ed25519FeEq.ioEq])

/-- **The straight lines' callees** in build `b`. -/
noncomputable def daAd (b : Build) : ∀ a, AdE Rs (cb := b.codeBytes) (daS a)
  | .f .add => Ed25519GeField.addAd b Rs
  | .f .sub => Ed25519GeField.subAd b Rs
  | .f .mul => Ed25519FePow.mulAd b Rs
  | .f .sqr => Ed25519FePow.sqrAd b Rs
  | .pow => Ed25519FePow.powAd b Rs
  | .eq => eqAdE Rs b
  | .canon => Ed25519GeCompressProg.canonAd b Rs
  | .copy => Ed25519FePow.paAd b Rs .copyOut

/-- The block adapters: the load. -/
def dbAd : ∀ x, Bd Rs (dbS x)
  | .load => dbD Rs .load

/-- **Their values** are those `Ed25519DecompressOut` reads. -/
theorem daAd_sems (b : Build) :
    Ed25519DecompressOut.Sems (fun a => @Ad.sem Rs b.bytes b.size b.codeBytes _ (daAd Rs b a).ad)
      (fun x => (dbAd Rs x).sem) where
  f := fun
    | .add, _ | .sub, _ => rfl
    | .mul, vs => congrArg (· :: []) (Ed25519GeProg.paV_mul vs)
    | .sqr, vs => congrArg (· :: []) (Ed25519GeProg.paV_sqr vs)
  pow := fun _ => rfl
  canon := fun _ => rfl
  copy := fun _ => rfl
  load := fun _ => rfl

end M0Crypto.Release.Ed25519DecompressStitch
