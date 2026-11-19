import M0Crypto.Release.Ed25519VerifyRun
import M0Crypto.Release.Ed25519VerifyAd
import M0Crypto.Release.Ed25519VerifyVal
import M0Crypto.Release.Ed25519Callees
import M0Crypto.Release.Ed25519DecompressAd
import M0Crypto.Release.Ed25519DecompressPack
import M0Crypto.Release.Ed25519DsmPack
import M0Crypto.Release.Ed25519FeEqZ

/-!
# `m0c_ed25519_verify`'s tests are `Spec.Ed25519.verify`'s

`vAd b`: the body's adapters in build `b`, at sign's relations. The inputs of its calls are the
entry bytes of `sig`, `m` and `pk` and the values of earlier calls (`i0_eq` … `i11_eq`, by
evaluation; `ge_decompress`'s and `ge_dsm`'s outputs stay unevaluated). Each test is the matching
conjunct of `verify_tests`: `A` decodes (`d0`), `R` decodes (`d1`), `s < L` (`d2`, with `L` read
from the code), and the two projective comparisons of `SB` with the decoded `R` (`d3`, `d4`), so
the verdict is `Spec.Ed25519.verify` (`ok_eq`). The callees' premises along the passing tests
hold (`body_pre`).
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Mem LowReg)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519EdwardsExtended (Ext)
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Release.Ed25519Bridge (ofSpec SpecRep toF toF_val Bpt)
open M0Crypto.Release.Ed25519GeProg (fI fI_nat fI_mul RepV Rep2V)
open M0Crypto.Release.Ed25519DecompressW (csemX okX okX_b ptV)
open M0Crypto.Release.Ed25519VerifyVal (wnafBytes)
open M0Crypto.Release.Ed25519DsmSem (dsmSem dsmPre dsm_sem)
open M0Crypto.Release.Ed25519FePow (paV)
open M0Crypto.Release.Ed25519FeEq (okE)
open M0Crypto.Release.Ed25519DecompressOut (updOuts_nmem)
open M0Crypto.Spec.Ed25519 (encodeInt decodeInt decodePoint L)
open M0Crypto.Spec.Sha512 (sha512)

/-! ## The adapters -/

/-- The relations of verify's callees: sign's. -/
abbrev vRels : Rels := calleeRels

/-- The straight lines' callees: sign's SHA-512 and reduction, and the field ones. -/
noncomputable def vAp (b : Build) : ∀ a, @Ad vRels b.bytes b.size b.codeBytes (vpS a)
  | .e a => (callees b).ad a
  | .f a => (Ed25519DecompressStitch.daAd vRels b (.f a)).ad

theorem vAp_E (b : Build) : ∀ a base p, @CalleeS.Eff (vpS a) p b.bytes b.size b.codeBytes base
    (@Ad.T vRels b.bytes b.size b.codeBytes _ (vAp b a) base p)
  | .e a => (callees b).ef a
  | .f a => (Ed25519DecompressStitch.daAd vRels b (.f a)).ef

/-- **The body's adapters** in build `b`. -/
noncomputable def vAd (b : Build) : @VAd vRels b.bytes b.size b.codeBytes :=
  letI := b.codeBytes
  { ap := vAp b
    apE := vAp_E b
    lt := ltD vRels
    zl := ltZ vRels
    zl_cc := rfl
    zl_co := rfl
    dc := Ed25519DecompressPack.decAd b vRels
    zd := Ed25519DecompressPack.decZ b vRels
    zd_co := rfl
    w5 := Ed25519WnafAd.wnafAd b vRels 5 (by decide) (by decide)
    w3 := Ed25519WnafAd.wnafAd b vRels 3 (by decide) (by decide)
    dm := Ed25519DsmPack.dsmAd b vRels
    eq := Ed25519FeEq.eqAd vRels b
    ze := Ed25519FeEq.eqZ vRels b
    ze_co := rfl }

/-- A stitched call's inputs from its sources. -/
theorem ioVs_of {G : Geo} {c : Ctx} {m0 : Mem} {st : St} {σ : List (M0Crypto.Armv6M.Reg × SV)} {io : Iface}
    {E : Loc → V} {l : List Src} (h : (ioRes G st σ io).map (·.srcs) = some l) :
    ioVs G c m0 st σ io E = l.map (Src.val G c m0 E) := by
  unfold ioVs; cases e : ioRes G st σ io <;> rw [e] at h <;> simp at h; subst h; rfl

theorem src11 : (ioRes verifyGeo v11 (regsOf v11.Γ v11.σ aE4) (vxS .eq).io).map (·.srcs) =
    some [.view (.fr 48), .view (.fr 624)] := by decide +kernel

/-- A stitched call with no outputs leaves the values. -/
theorem xcallEv_nil {G : Geo} {c : Ctx} {m0 : Mem} {st : St} {σ : List (M0Crypto.Armv6M.Reg × SV)} {io : Iface}
    {sem : List V → List V} {E : Loc → V} (h : (ioRes G st σ io).map (·.outs) = some []) :
    xcallEv G c m0 st σ io sem E = E := by
  unfold xcallEv; cases e : ioRes G st σ io with
  | none => rfl
  | some r =>
    rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h
    simp only [h]; exact Ed25519DecompressStitch.updOuts_none E _

/-- A one-call program's values. -/
theorem ev_call1 {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V}
    {semB : Bk → List V → List V} {c : Ctx} {m0 : Mem} {st : St} {E : Loc → V} {a : A} {as : List (LowReg × Ld)}
    {srcs : List Src} {outs : List (Loc × Kd)} (ht : ((Op.call a as : Op A Bk).ty cE bE G st).isSome = true)
    (hs : (ioRes G st (regsOf st.Γ st.σ as) (cE a).io).map (·.srcs) = some srcs)
    (ho : (ioRes G st (regsOf st.Γ st.σ as) (cE a).io).map (·.outs) = some outs) :
    (Prog.ofList [(Op.call a as : Op A Bk)]).ev cE bE G semA semB c m0 st E =
      updOuts E outs (semA a (srcs.map (Src.val G c m0 E))) := by
  obtain ⟨st', h'⟩ := Option.isSome_iff_exists.mp ht
  simp only [Prog.ofList, Prog.ev, h', Op.ev]
  cases e : ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
  | none => rw [e] at hs; cases hs
  | some r =>
    rw [e] at hs ho; simp only [Option.map_some, Option.some.injEq] at hs ho
    subst hs ho; rfl

theorem io9 : (ioRes verifyGeo v9 (regsOf v9.Γ v9.σ aE3) (vxS .eq).io).map (·.outs) = some [] := by decide +kernel

theorem m4_facts : ((Op.call (.f .mul) [(0, Ld.S T2), (1, Ld.S (PR + 32)), (2, Ld.S (SB + 64))] : Op VP VB).ty vpS vbS
      verifyGeo (addViews v10 [])).isSome = true ∧
    (ioRes verifyGeo (addViews v10 []) (regsOf (addViews v10 []).Γ (addViews v10 []).σ
      [(0, Ld.S T2), (1, Ld.S (PR + 32)), (2, Ld.S (SB + 64))]) (vpS (.f .mul)).io).map (·.srcs) =
        some [.view (.fr 272), .view (.fr 80)] ∧
    (ioRes verifyGeo (addViews v10 []) (regsOf (addViews v10 []).Γ (addViews v10 []).σ
      [(0, Ld.S T2), (1, Ld.S (PR + 32)), (2, Ld.S (SB + 64))]) (vpS (.f .mul)).io).map (·.outs) =
        some [(.fr 624, .fe)] := by decide +kernel

theorem m3_facts : ((Op.call (.f .mul) [(0, Ld.S T2), (1, Ld.S PR), (2, Ld.S (SB + 64))] : Op VP VB).ty vpS vbS
      verifyGeo v8).isSome = true ∧
    (ioRes verifyGeo v8 (regsOf v8.Γ v8.σ [(0, Ld.S T2), (1, Ld.S PR), (2, Ld.S (SB + 64))]) (vpS (.f .mul)).io).map
      (·.srcs) = some [.view (.fr 240), .view (.fr 80)] ∧
    (ioRes verifyGeo v8 (regsOf v8.Γ v8.σ [(0, Ld.S T2), (1, Ld.S PR), (2, Ld.S (SB + 64))]) (vpS (.f .mul)).io).map
      (·.outs) = some [(.fr 624, .fe)] := by decide +kernel

/-! ## The values along the body -/

section
variable (b : Build) (c : Ctx) (m0 : Mem)

/-- The entry bytes: `R` and `s` of `sig`, `pk`, the message and the code's `L`. -/
abbrev rv : List (BitVec 8) := bytesAt m0 (c.ptr 0 + 0#32) 32
abbrev sv : List (BitVec 8) := bytesAt m0 (c.ptr 0 + 32#32) 32
abbrev pv : List (BitVec 8) := bytesAt m0 (c.ptr 2 + 0#32) 32
abbrev mv : List (BitVec 8) := bytesAt m0 (c.ptr 1 + 0#32) (c.prm 0).toNat
abbrev lv : List (BitVec 8) := bytesAt m0 (c.ptr 3 + 0#32) 32

/-- `h`: the reduced hash of `R`, `pk` and the message. -/
abbrev hv : List (BitVec 8) := encodeInt (decodeInt (sha512 ([] ++ rv c m0 ++ pv c m0 ++ mv c m0)) % L)

/-- The points after both decompressions: `A` at `PA`, `R` at `PR`. -/
def Av : Loc → V := updOuts (updOuts (fun _ => .none) l0 (csemX [.b (pv c m0)])) l1 (csemX [.b (rv c m0)])

/-- `ge_dsm`'s inputs. -/
def i7v : List V := [.b (wnafBytes 5 (decodeInt (sv c m0))), .b (wnafBytes 3 (decodeInt (hv c m0))),
  Av c m0 (.fr 112), Av c m0 (.fr 144), Av c m0 (.fr 176), Av c m0 (.fr 208)]

/-- `ge_dsm`'s outputs. -/
def dsmO : List (Loc × Kd) := [(.fr 16, .fe), (.fr 48, .fe), (.fr 80, .fe)]

section
attribute [local irreducible] csemX decodeInt wnafBytes decodePoint sha512 encodeInt dsmSem
variable {b c m0}
local notation "D" => (vAd b)

theorem i0_eq : VAd.i0 (cb := b.codeBytes) D c m0 = [.b (pv c m0)] := rfl
theorem i1_eq : VAd.i1 (cb := b.codeBytes) D c m0 = [.b (rv c m0)] := rfl
theorem i2_eq : VAd.i2 (cb := b.codeBytes) D c m0 = [.b (sv c m0), .b (lv c m0)] := rfl
theorem i7_eq : VAd.i7 (cb := b.codeBytes) D c m0 = i7v c m0 := rfl
theorem E9_eq : VAd.E9 (cb := b.codeBytes) D c m0 = updOuts (VAd.E8 (cb := b.codeBytes) D c m0) dsmO
    (dsmSem b (i7v c m0)) := rfl
theorem E8_R : VAd.E8 (cb := b.codeBytes) D c m0 (.fr 240) = Av c m0 (.fr 240) ∧
    VAd.E8 (cb := b.codeBytes) D c m0 (.fr 272) = Av c m0 (.fr 272) := ⟨rfl, rfl⟩
theorem i9_eq : VAd.i9 (cb := b.codeBytes) D c m0 = [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 16),
    paV .mul [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 240), VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80)]] :=
  show [VAd.E10 (cb := b.codeBytes) D c m0 (.fr 16), VAd.E10 (cb := b.codeBytes) D c m0 (.fr 624)] = _ from rfl
theorem E11_eq : VAd.E11 (cb := b.codeBytes) D c m0 = VAd.E10 (cb := b.codeBytes) D c m0 := by
  unfold VAd.E11
  rw [Ed25519DecompressStitch.updOuts_none, xcallEv_nil io9]
theorem E10_eq : VAd.E10 (cb := b.codeBytes) D c m0 = updOuts (VAd.E9 (cb := b.codeBytes) D c m0) [(.fr 624, .fe)]
    [paV .mul [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 240), VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80)]] := by
  unfold VAd.E10
  exact ev_call1 m3_facts.1 m3_facts.2.1 m3_facts.2.2
theorem E10_at : VAd.E10 (cb := b.codeBytes) D c m0 (.fr 48) = VAd.E9 (cb := b.codeBytes) D c m0 (.fr 48) ∧
    VAd.E10 (cb := b.codeBytes) D c m0 (.fr 80) = VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80) ∧
    VAd.E10 (cb := b.codeBytes) D c m0 (.fr 272) = VAd.E9 (cb := b.codeBytes) D c m0 (.fr 272) := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [E10_eq]; exact updOuts_nmem _ _ (by decide))
theorem E12_eq : VAd.E12 (cb := b.codeBytes) D c m0 = updOuts (VAd.E10 (cb := b.codeBytes) D c m0) [(.fr 624, .fe)]
    [paV .mul [VAd.E10 (cb := b.codeBytes) D c m0 (.fr 272), VAd.E10 (cb := b.codeBytes) D c m0 (.fr 80)]] := by
  unfold VAd.E12
  rw [E11_eq]
  exact ev_call1 m4_facts.1 m4_facts.2.1 m4_facts.2.2
theorem E12_48 : VAd.E12 (cb := b.codeBytes) D c m0 (.fr 48) = VAd.E9 (cb := b.codeBytes) D c m0 (.fr 48) := by
  rw [E12_eq, updOuts_nmem _ _ (by decide)]; exact E10_at.1
theorem E12_624 : VAd.E12 (cb := b.codeBytes) D c m0 (.fr 624) =
    paV .mul [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 272), VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80)] := by
  rw [E12_eq, ← E10_at.2.1, ← E10_at.2.2]; rfl
theorem i11_eq : VAd.i11 (cb := b.codeBytes) D c m0 = [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 48),
    paV .mul [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 272), VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80)]] := by
  unfold VAd.i11
  rw [ioVs_of src11]
  simp only [List.map_cons, List.map_nil, Src.val]
  rw [E12_48, E12_624]

theorem d0_eq : VAd.d0 (cb := b.codeBytes) D c m0 = (decodePoint (pv c m0)).isSome :=
  show okX (VAd.i0 (cb := b.codeBytes) D c m0) = _ by rw [i0_eq]; rfl
theorem d1_eq : VAd.d1 (cb := b.codeBytes) D c m0 = (decodePoint (rv c m0)).isSome :=
  show okX (VAd.i1 (cb := b.codeBytes) D c m0) = _ by rw [i1_eq]; rfl
theorem d2_eq : VAd.d2 (cb := b.codeBytes) D c m0 = decide (decodeInt (sv c m0) < decodeInt (lv c m0)) :=
  show ltOk (VAd.i2 (cb := b.codeBytes) D c m0) = _ by rw [i2_eq]; rfl
theorem ze_ok : (VAd.ze (cb := b.codeBytes) D).ok = okE := rfl
theorem d3_eq : VAd.d3 (cb := b.codeBytes) D c m0 = okE (VAd.i9 (cb := b.codeBytes) D c m0) :=
  show (VAd.ze (cb := b.codeBytes) D).ok _ = _ by rw [ze_ok]
theorem d4_eq : VAd.d4 (cb := b.codeBytes) D c m0 = okE (VAd.i11 (cb := b.codeBytes) D c m0) :=
  show (VAd.ze (cb := b.codeBytes) D).ok _ = _ by rw [ze_ok]

end
end

/-! ## The decoded points -/

section
variable {c : Ctx} {m0 : Mem}

theorem fI_val (x : Fp) : fI (x.val : Int) = x := by rw [fI_nat, toF_val]

/-- `ge_decompress`'s outputs on success. -/
theorem csemX_some {l : List (BitVec 8)} {Q : Spec.Ed25519.Point} (h : decodePoint l = some Q) :
    csemX [.b l] = ptV (ofSpec Q) := by
  simp only [csemX, h, Option.map_some, Option.getD_some]

/-- `A`'s coordinates at `PA`. -/
theorem Av_A {A' : Spec.Ed25519.Point} (h : decodePoint (pv c m0) = some A') :
    [Av c m0 (.fr 112), Av c m0 (.fr 144), Av c m0 (.fr 176), Av c m0 (.fr 208)] = ptV (ofSpec A') := by
  simp only [Av]
  rw [updOuts_nmem l1 _ (by decide), updOuts_nmem l1 _ (by decide), updOuts_nmem l1 _ (by decide),
    updOuts_nmem l1 _ (by decide), csemX_some h]
  rfl

/-- `R`'s coordinates at `PR`. -/
theorem Av_R {R : Spec.Ed25519.Point} (h : decodePoint (rv c m0) = some R) :
    Av c m0 (.fr 240) = .f ((ofSpec R).X.val : Int) ∧ Av c m0 (.fr 272) = .f ((ofSpec R).Y.val : Int) ∧
    Av c m0 (.fr 304) = .f ((ofSpec R).Z.val : Int) ∧ Av c m0 (.fr 336) = .f ((ofSpec R).T.val : Int) := by
  simp only [Av, csemX_some h]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `A`'s coordinates represent its point. -/
theorem repV_A {A' : Spec.Ed25519.Point} {A : EdPt} (h : decodePoint (pv c m0) = some A') (hr : SpecRep A' A) :
    RepV [Av c m0 (.fr 112), Av c m0 (.fr 144), Av c m0 (.fr 176), Av c m0 (.fr 208)] A := by
  rw [Av_A h]
  refine ⟨_, _, _, _, rfl, ?_⟩
  simp only [fI_val]
  exact hr

/-- `h` is reduced. -/
theorem hv_val : decodeInt (hv c m0) = decodeInt (sha512 ([] ++ rv c m0 ++ pv c m0 ++ mv c m0)) % L := by
  rw [Ed25519CallProg.decodeInt_encodeInt]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem hv_lt : decodeInt (hv c m0) < L := by rw [hv_val]; exact Nat.mod_lt _ (by decide)

end

/-! ## The tests -/

section
variable (b : Build) (c : Ctx) (m0 : Mem)

/-- The field value of a value. -/
def fv : V → Int
  | .f x => x
  | _ => 0

/-- `SB`, the double multiplication's `p2` result. -/
noncomputable def SBv : Ext Fp :=
  letI := b.codeBytes
  ⟨fI (fv (VAd.E9 (vAd b) c m0 (.fr 16))), fI (fv (VAd.E9 (vAd b) c m0 (.fr 48))),
    fI (fv (VAd.E9 (vAd b) c m0 (.fr 80))), 0⟩

/-- `ER`, the decoded `R`. -/
noncomputable def ERv : Ext Fp :=
  ⟨fI (fv (Av c m0 (.fr 240))), fI (fv (Av c m0 (.fr 272))), fI (fv (Av c m0 (.fr 304))),
    fI (fv (Av c m0 (.fr 336)))⟩

variable {b c m0}

theorem ER_of {R : Spec.Ed25519.Point} (h : decodePoint (rv c m0) = some R) : ERv c m0 = ofSpec R := by
  obtain ⟨h1, h2, h3, h4⟩ := Av_R h
  simp only [ERv, h1, h2, h3, h4, fv, fI_val]

/-- With `A` decoded and `s < L`, `ge_dsm`'s outputs are `SB`'s values and represent
`[s]B − [h]A`. -/
theorem sb_of {A' : Spec.Ed25519.Point} {A : EdPt} (hA : decodePoint (pv c m0) = some A') (hr : SpecRep A' A)
    (hs : decodeInt (sv c m0) < L) :
    ∃ x y z : Int, dsmSem b (i7v c m0) = [.f x, .f y, .f z] ∧
      Rep2V [.f x, .f y, .f z] ((decodeInt (sv c m0) : Int) • Bpt - (decodeInt (hv c m0) : Int) • A) := by
  rw [show i7v c m0 = .b (wnafBytes 5 (decodeInt (sv c m0))) :: .b (wnafBytes 3 (decodeInt (hv c m0))) ::
    [Av c m0 (.fr 112), Av c m0 (.fr 144), Av c m0 (.fr 176), Av c m0 (.fr 208)] from rfl]
  obtain ⟨x, y, z, he, hrep⟩ := dsm_sem b hs hv_lt (repV_A hA hr)
  exact ⟨x, y, z, he, ⟨x, y, z, rfl, hrep⟩⟩

theorem E9_at {x y z : Int} (he : dsmSem b (i7v c m0) = [.f x, .f y, .f z]) :
    letI := b.codeBytes
    VAd.E9 (vAd b) c m0 (.fr 16) = .f x ∧ VAd.E9 (vAd b) c m0 (.fr 48) = .f y ∧
      VAd.E9 (vAd b) c m0 (.fr 80) = .f z ∧ VAd.E9 (vAd b) c m0 (.fr 240) = Av c m0 (.fr 240) ∧
      VAd.E9 (vAd b) c m0 (.fr 272) = Av c m0 (.fr 272) := by
  letI := b.codeBytes
  rw [E9_eq, he]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [updOuts_nmem _ _ (by decide)]; exact E8_R.1
  · rw [updOuts_nmem _ _ (by decide)]; exact E8_R.2

/-- **The verdict is `Spec.Ed25519.verify`'s** (C3), with `L` read from the code. -/
theorem ok_eq (hL : decodeInt (lv c m0) = L) :
    letI := b.codeBytes
    VAd.ok (vAd b) c m0 = Spec.Ed25519.verify (rv c m0 ++ sv c m0) (mv c m0) (pv c m0) := by
  letI := b.codeBytes
  have ht : (rv c m0 ++ sv c m0).take 32 = rv c m0 := List.take_left' (bytesAt_length _ _ _)
  have hd : (rv c m0 ++ sv c m0).drop 32 = sv c m0 := List.drop_left' (bytesAt_length _ _ _)
  rw [Ed25519VerifyBlocks.verify_tests (SB := SBv b c m0) (ER := ERv c m0) (fun R h => ER_of (ht ▸ h))
    (fun R A' hR hA => ?_)]
  · simp only [VAd.ok, d0_eq, d1_eq, d2_eq, d3_eq, d4_eq, hL, ht, hd]
    cases hA : decodePoint (pv c m0) with
    | none => simp
    | some A' =>
      cases hR : decodePoint (rv c m0) with
      | none => simp
      | some R =>
        by_cases hs : decodeInt (sv c m0) < L
        · obtain ⟨A, hr, -⟩ := Ed25519Verify.specRep_of_decode hA
          obtain ⟨x, y, z, he, -⟩ := sb_of (b := b) hA hr hs
          obtain ⟨e16, e48, e80, e240, e272⟩ := E9_at he
          obtain ⟨a1, a2, -, -⟩ := Av_R hR
          simp only [Option.isSome_some, hs, decide_true, Bool.true_and, i9_eq, i11_eq, e16, e48, e80, e240,
            e272, a1, a2, paV, okE, SBv, ERv, fv, fI_mul]
        · simp [hs]
  · rw [ht] at hR ⊢; rw [hd]
    obtain ⟨A, hr, -⟩ := Ed25519Verify.specRep_of_decode hA
    refine ⟨A, hr, fun hs => ?_⟩
    obtain ⟨x, y, z, he, hrep⟩ := sb_of (b := b) hA hr hs
    obtain ⟨e16, e48, e80, -, -⟩ := E9_at he
    obtain ⟨x', y', z', hx, hrep'⟩ := hrep
    simp only [List.cons.injEq, V.f.injEq, and_true] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    have hh : (decodeInt (hv c m0) : Int) = ((decodeInt (sha512 (rv c m0 ++ pv c m0 ++ mv c m0)) % L : Nat) : Int) := by
      rw [hv_val, List.nil_append]
    rw [hh] at hrep'
    simpa only [SBv, e16, e48, e80, fv] using hrep'

/-- **The callees' premises** along the passing tests. -/
theorem body_pre (hL : decodeInt (lv c m0) = L) :
    letI := b.codeBytes
    (vAd b).zl.vpre ((vAd b).i2 c m0) ∧
    ((vAd b).d0 c m0 = true → (vAd b).d1 c m0 = true → (vAd b).d2 c m0 = true →
      (vAd b).dm.vpre ((vAd b).i7 c m0)) := by
  letI := b.codeBytes
  refine ⟨by rw [i2_eq]; exact hL, fun h0 h1 h2 => ?_⟩
  rw [d0_eq] at h0
  rw [d2_eq, hL, decide_eq_true_iff] at h2
  obtain ⟨A', hA⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨A, hr, -⟩ := Ed25519Verify.specRep_of_decode hA
  rw [i7_eq]
  exact ⟨_, _, h2, hv_lt, _, A, rfl, repV_A hA hr⟩

end

end M0Crypto.Release.Ed25519VerifyProg
