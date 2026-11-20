import M0Crypto.Release.Ed25519VerifyRun
import M0Crypto.Release.Ed25519VerifyAd
import M0Crypto.Release.Ed25519VerifyVal
import M0Crypto.Release.Ed25519Callees
import M0Crypto.Release.Ed25519DecompressAd
import M0Crypto.Release.Ed25519DecompressPack
import M0Crypto.Release.Ed25519DsmPack
import M0Crypto.Release.Ed25519VerifyEncode
import M0Crypto.Release.Ed25519RCheckRun

/-!
# `m0c_ed25519_verify`'s tests are `Spec.Ed25519.verify`'s

The status sites test whether A decodes, whether R passes the early encoding check,
whether S is below the group order, and whether the canonical encoding of the double-scalar result equals the
original R bytes. The last test uses the full encoding, including the sign bit.

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
open M0Crypto.Release.Ed25519GeProg (fI fI_nat RepV Rep2V)
open M0Crypto.Release.Ed25519DecompressW (csemX okX okX_b ptV)
open M0Crypto.Release.Ed25519VerifyVal (wnafBytes)
open M0Crypto.Release.Ed25519DsmSem (dsmSem dsmPre dsm_sem)
open M0Crypto.Release.Ed25519CompressP2 (cp2Ad cp2V)
open M0Crypto.Release.Ed25519Encode (compressCode)
open M0Crypto.Release.Ed25519Formulas (Rep2)
open M0Crypto.Release.Ed25519VerifyEncode (verify_encode_compare)
open M0Crypto.Spec.Ed25519 (encodeInt decodeInt decodePoint L)
open M0Crypto.Spec.Sha512 (sha512)

/-! ## The adapters -/

/-- The relations of verify's callees: sign's. -/
abbrev vRels : Rels := calleeRels

/-- The straight lines' callees: sign's SHA-512 and reduction, and projective compression. -/
noncomputable def vAp (b : Build) : ∀ a, @Ad vRels b.bytes b.size b.codeBytes (vpS a)
  | .e a => (callees b).ad a
  | .compress => (cp2Ad b vRels).ad

theorem vAp_E (b : Build) : ∀ a base p, @CalleeS.Eff (vpS a) p b.bytes b.size b.codeBytes base
    (@Ad.T vRels b.bytes b.size b.codeBytes _ (vAp b a) base p)
  | .e a => (callees b).ef a
  | .compress => (cp2Ad b vRels).ef

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
    rc := Ed25519RCheck.checkAd b vRels
    zr := Ed25519RCheck.checkZ b vRels
    zr_co := rfl
    w5 := Ed25519WnafAd.wnafAd b vRels 5 (by decide) (by decide)
    w3 := Ed25519WnafAd.wnafAd b vRels 3 (by decide) (by decide)
    dm := Ed25519DsmPack.dsmAd b vRels
    cmp := Ed25519BytesDiff.diffAd b vRels
    zc := Ed25519BytesDiff.diffZ b vRels
    zc_co := rfl }

/-- A stitched call's inputs from its sources. -/
theorem ioVs_of {G : Geo} {c : Ctx} {m0 : Mem} {st : St} {σ : List (M0Crypto.Armv6M.Reg × SV)} {io : Iface}
    {E : Loc → V} {l : List Src} (h : (ioRes G st σ io).map (·.srcs) = some l) :
    ioVs G c m0 st σ io E = l.map (Src.val G c m0 E) := by
  unfold ioVs; cases e : ioRes G st σ io <;> rw [e] at h <;> simp at h; subst h; rfl

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

private theorem encoding_io :
    ((Op.call .compress aEncode : Op VP VB).ty vpS vbS verifyGeo v8).isSome = true ∧
    (ioRes verifyGeo v8 (regsOf v8.Γ v8.σ aEncode) (vpS .compress).io).map (·.srcs) =
      some [.view (.fr 16),.view (.fr 48),.view (.fr 80)] ∧
    (ioRes verifyGeo v8 (regsOf v8.Γ v8.σ aEncode) (vpS .compress).io).map (·.outs) =
      some [(.fr ENC,.bytes 32)] := by decide +kernel

private theorem compare_io :
    (ioRes verifyGeo v9 (regsOf v9.Γ v9.σ aCompare) (vxS .compare).io).map (·.srcs) =
      some [.view (.fr ENC),.ext ⟨.ex 0 0,.k 32⟩] := by decide +kernel

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

/-- The decoded public key at PA. -/
def Av : Loc → V := updOuts (fun _ => .none) l0 (csemX [.b (pv c m0)])

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
theorem i2_eq : VAd.i2 (cb := b.codeBytes) D c m0 = [.b (sv c m0), .b (lv c m0)] := rfl
theorem i7_eq : VAd.i7 (cb := b.codeBytes) D c m0 = i7v c m0 := rfl
theorem E9_eq : VAd.E9 (cb := b.codeBytes) D c m0 = updOuts (VAd.E8 (cb := b.codeBytes) D c m0) dsmO
    (dsmSem b (i7v c m0)) := rfl
theorem E10_eq : VAd.E10 (cb := b.codeBytes) D c m0 =
    updOuts (VAd.E9 (cb := b.codeBytes) D c m0) [(.fr ENC,.bytes 32)]
      (cp2V [VAd.E9 (cb := b.codeBytes) D c m0 (.fr 16),
        VAd.E9 (cb := b.codeBytes) D c m0 (.fr 48),VAd.E9 (cb := b.codeBytes) D c m0 (.fr 80)]) := by
  unfold VAd.E10
  exact ev_call1 encoding_io.1 encoding_io.2.1 encoding_io.2.2

theorem i9_eq : VAd.i9 (cb := b.codeBytes) D c m0 =
    [VAd.E10 (cb := b.codeBytes) D c m0 (.fr ENC),.b (rv c m0)] := by
  unfold VAd.i9
  rw [ioVs_of compare_io]
  rfl

theorem iR_eq : VAd.iR (cb := b.codeBytes) D c m0 = [.b (rv c m0)] := by
  have hIO :
      (ioRes verifyGeo (addViews v1 l0) (regsOf (addViews v1 l0).Γ (addViews v1 l0).σ aR)
        (vxS .checkR).io).map (·.srcs) =
        some [.ext ⟨.ex 0 0,.k 32⟩] := by decide +kernel
  unfold VAd.iR
  rw [ioVs_of hIO]
  rfl

theorem dR_eq : VAd.dR (cb := b.codeBytes) D c m0 = Ed25519RCheck.ok [.b (rv c m0)] := by
  change Ed25519RCheck.ok (VAd.iR (cb := b.codeBytes) D c m0) = _
  rw [iR_eq]

theorem d0_eq : VAd.d0 (cb := b.codeBytes) D c m0 = (decodePoint (pv c m0)).isSome :=
  show okX (VAd.i0 (cb := b.codeBytes) D c m0) = _ by rw [i0_eq]; rfl
theorem d2_eq : VAd.d2 (cb := b.codeBytes) D c m0 = decide (decodeInt (sv c m0) < decodeInt (lv c m0)) :=
  show ltOk (VAd.i2 (cb := b.codeBytes) D c m0) = _ by rw [i2_eq]; rfl
theorem d3_eq : VAd.d3 (cb := b.codeBytes) D c m0 =
    Ed25519BytesDiff.ok (VAd.i9 (cb := b.codeBytes) D c m0) := rfl

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
  rw [Av,csemX_some h]
  rfl

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

variable {b c m0}

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
      VAd.E9 (vAd b) c m0 (.fr 80) = .f z := by
  letI := b.codeBytes
  rw [E9_eq, he]
  exact ⟨rfl,rfl,rfl⟩

/-- The byte comparison and the cofactorless verification specification have the same verdict. -/
theorem ok_eq (hL : decodeInt (lv c m0) = L) :
    letI := b.codeBytes
    VAd.ok (vAd b) c m0 = Spec.Ed25519.verify (rv c m0 ++ sv c m0) (mv c m0) (pv c m0) := by
  letI := b.codeBytes
  have ht : (rv c m0 ++ sv c m0).take 32 = rv c m0 := List.take_left' (bytesAt_length _ _ _)
  have hd : (rv c m0 ++ sv c m0).drop 32 = sv c m0 := List.drop_left' (bytesAt_length _ _ _)
  cases hR : (vAd b).dR c m0
  · have hBad := Ed25519RCheck.reject_of_failure m0 (c.ptr 0 + 0#32) (dR_eq.symm.trans hR)
    rw [Ed25519VerifyEncode.verify_of_earlyReject (ht.symm ▸ hBad)]
    simp [VAd.ok,hR]
  · cases hA : decodePoint (pv c m0) with
    | none =>
      rw [Ed25519Verify.verify_of_decode_A_none hA]
      simp [VAd.ok,d0_eq,hA]
    | some A' =>
      obtain ⟨A,hr,-⟩ := Ed25519Verify.specRep_of_decode hA
      have hrep (hs : decodeInt (sv c m0) < L) :
          Rep2 (SBv b c m0) ((decodeInt (sv c m0) : Int) • Bpt -
            ((decodeInt (sha512 (rv c m0 ++ pv c m0 ++ mv c m0)) % L : Nat) : Int) • A) := by
        obtain ⟨x,y,z,he,h⟩ := sb_of (b := b) hA hr hs
        obtain ⟨e16,e48,e80⟩ := E9_at he
        obtain ⟨x',y',z',hv,h⟩ := h
        simp only [List.cons.injEq,V.f.injEq,and_true] at hv
        obtain ⟨rfl,rfl,rfl⟩ := hv
        simpa only [SBv,e16,e48,e80,fv,hv_val,List.nil_append] using h
      rw [verify_encode_compare (SB := SBv b c m0) (ht.symm ▸ bytesAt_length _ _ _) hA hr
        (by rw [ht,hd]; exact hrep),ht,hd]
      simp only [VAd.ok,d0_eq,d2_eq,hA,hR,hL,Option.isSome_some,Bool.true_and]
      by_cases hs : decodeInt (sv c m0) < L
      · obtain ⟨x,y,z,he,-⟩ := sb_of (b := b) hA hr hs
        obtain ⟨e16,e48,e80⟩ := E9_at he
        simp only [hs,decide_true,Bool.true_and,d3_eq,i9_eq,E10_eq,SBv,e16,e48,e80,fv]
        change decide (encodeInt (compressCode ⟨fI x,fI y,fI z,0⟩) = rv c m0) = _
        simp only [eq_comm]
      · simp [hs]

/-- **The callees' premises** along the passing tests. -/
theorem body_pre (hL : decodeInt (lv c m0) = L) :
    letI := b.codeBytes
    (vAd b).zl.vpre ((vAd b).i2 c m0) ∧
    ((vAd b).d0 c m0 = true → (vAd b).d2 c m0 = true →
      (vAd b).dm.vpre ((vAd b).i7 c m0)) := by
  letI := b.codeBytes
  refine ⟨by rw [i2_eq]; exact hL, fun h0 h2 => ?_⟩
  rw [d0_eq] at h0
  rw [d2_eq, hL, decide_eq_true_iff] at h2
  obtain ⟨A', hA⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨A, hr, -⟩ := Ed25519Verify.specRep_of_decode hA
  rw [i7_eq]
  exact ⟨_, _, h2, hv_lt, _, A, rfl, repV_A hA hr⟩

end

end M0Crypto.Release.Ed25519VerifyProg
