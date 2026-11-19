import M0Crypto.Release.Ed25519FragC
import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519ScReduceProg
import M0Crypto.Release.Ed25519Wnaf
import M0Crypto.Release.Ed25519WordAd

/-!
# The straight-line parts of `m0c_ge_dsm`

`m0c_ge_dsm(r0 = out, r1 = s digits, r2 = h digits, r3 = A)` (`gen_ed25519.py`, `emit_dsm`)
between its branches, loops and public blocks is these straight lines:

* `segPre`: the spills and the table `AI` of the cached odd multiples `−A`, `−3A` (`neg_a`,
  `to_cached`, `ge_dbl`, `ge_p1p1_to_p3`, cached `ge_add`);
* `segId`: the identity in `R` (`m0c_zero`, then the block `ident` storing the two ones);
* in the loop: `segDbl` (`ge_dbl`); `segP3 a` / `segP2 a` (`ge_p1p1_to_p3` with or without `T`)
  at the three joins `a`; `signed_add` over the frame table (`segSA`, across a literal pool)
  and over `m0c_ed_odd_b` (`segSB`);
* `segEnd`: `X, Y, Z` of `R` to `out`.

The field operations are `fragC` fragments; the code constants are buffer `4` (`m0c_ed_zero`,
the zero at `0`, `2d` at `96`) and the odd multiples of `B` buffer `5` (`m0c_ed_odd_b`).
`seg_pieces` and `seg_bok` decide each line's bytes at its offset in both builds.
-/

namespace M0Crypto.Release.Ed25519DsmProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519FragC
open M0Crypto.Release.Ed25519FePow (paS ioCopy)
open M0Crypto.Release.Ed25519MulBaseProg (ioZeroN mbS)
open M0Crypto.Release.Ed25519WordAd (ioCopyN)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ge_dsm ed_zero ed_odd_b copy zero)
open M0Crypto.Release.Ed25519Group (EdPt)
open Lean.Grind
open M0Crypto.Artifacts.Ed25519Compact (dsm_a_add dsm_a_done dsm_a_jump_join dsm_a_p2 dsm_a_p3 dsm_a_test_next dsm_b_add dsm_b_p2
  dsm_body dsm_dbl_jump dsm_dbl_p2 dsm_dbl_p3 dsm_dec_index dsm_double dsm_identity dsm_leave
  dsm_loop dsm_output dsm_start_scan dsm_test_a dsm_test_digits)

/-! ## The frame -/

def oOut : Nat := 0
def oI : Nat := 4
def oDa : Nat := 8
def oDb : Nat := 12
def oEp : Nat := 16
def oSp : Nat := 20
def oHp : Nat := 24
def oAp : Nat := 28
def oEa : Nat := 32
def oEb : Nat := 36
def oTz : Nat := 40
def oTt : Nat := 44
def oR : Nat := 48
def oT : Nat := 176
def oA : Nat := 304
def oB : Nat := 336
def oC : Nat := 368
def oD : Nat := 400
def oAI : Nat := 432
def oTop : Nat := 688

/-! ## Callees and blocks -/

inductive DS where
  | f (a : FA) | copy | copy2 | copy3 | zero
  deriving DecidableEq

/-- The field callees, `copy` of one, two and three field elements, and `zero` of a point. -/
def dsS : DS → CalleeS
  | .f a => faS a
  | .copy => paS .copyOut
  | .copy2 => calleeAt copy (ioCopyN 2) [0, 1, 2]
  | .copy3 => calleeAt copy (ioCopyN 3) [0, 1, 2]
  | .zero => calleeAt zero (ioZeroN 4) [0, 1]

theorem dsS_f (a : FA) : dsS (.f a) = faS a := rfl

inductive DB where
  | ident
  deriving DecidableEq

def dbS : DB → BlockS
  | .ident => mbS .ident

/-! ## The geometry -/

/-- `out` (written, aligned), the digit bytes of `s` and `h` (read, any alignment), `A` (read,
aligned). -/
def dsXr : List (Reg × XInfo) :=
  [(0, ⟨.k 96, true, false, true⟩), (1, ⟨.k 256, false, true, false⟩), (2, ⟨.k 256, false, true, false⟩),
   (3, ⟨.k 128, false, true, true⟩)]

/-- The callee with interface `io` and body `P`; the constants are code buffer `4`, the odd
multiples of `B` buffer `5`. -/
def dsQ (io : Iface) (P : Prog DS DB) : CalleeP DS DB :=
  ⟨calleeAt ge_dsm io [0, 1, 2, 3], P, oTop, dsXr, [], [(ed_zero, 128), (ed_odd_b, 768)], []⟩

def dsGeo : Geo :=
  { N := stackOf ge_dsm - 4, top := oTop,
    xs := [⟨.k 96, true, false, true⟩, ⟨.k 256, false, true, false⟩, ⟨.k 256, false, true, false⟩,
      ⟨.k 128, false, true, true⟩, ⟨.k 128, false, true, true⟩, ⟨.k 768, false, true, true⟩],
    cs := footprint ge_dsm, cd := [(4, ed_zero), (5, ed_odd_b)] }

theorem dsQ_geo (io : Iface) (P : Prog DS DB) : (dsQ io P).geo = dsGeo := rfl

/-! ## The straight lines -/

section
open Op Ld

/-- The zero and `2d` from `m0c_ed_zero`, by the literal at `imm`. -/
def cZ (imm : Nat) : Ld := .C 4 0 imm
def cD2 (imm : Nat) : Ld := .C 4 96 imm

/-- The four coordinates of a frame point at `o`. -/
def pt (o : Nat) : List Ld := (List.range 4).map fun i => S (o + 32 * i)
/-- Entry `k` of the table `AI`. -/
def ai (k : Nat) : List Ld := pt (oAI + 128 * k)

/-- `neg_a`: `R = (−X, Y, Z, −T)` of `A`, with the zero's literals at `i0`, `i3`. -/
def negA (i0 i3 : Nat) (k : Prog DS DB) : Prog DS DB :=
  fragC .f [⟨.sub, S oR, cZ i0, W oAp 0⟩]
    (.op (call .copy2 [(0, S (oR + 32)), (1, W oAp 32), (2, K 16)])
      (fragC .f [⟨.sub, S (oR + 96), cZ i3, W oAp 96⟩] k))

/-- `to_cached(R, k)` with `2d`'s literal at `i`. -/
def toCached (j i : Nat) (k : Prog DS DB) : Prog DS DB :=
  fragC .f [⟨.add, S (oAI + 128 * j), S (oR + 32), S oR⟩, ⟨.sub, S (oAI + 128 * j + 32), S (oR + 32), S oR⟩]
    (.op (call .copy [(0, S (oAI + 128 * j + 64)), (1, S (oR + 64)), (2, K 8)])
      (fragC .f [⟨.mul, S (oAI + 128 * j + 96), S (oR + 96), cD2 i⟩] k))

def dblF : List FOp :=
  dblOps oA oB oC oD (S oR) (S (oR + 32)) (S (oR + 64)) (S oT) (S (oT + 32)) (S (oT + 64)) (S (oT + 96))

def p3F (withT : Bool) : List FOp :=
  p3Ops withT (S oT) (S (oT + 32)) (S (oT + 64)) (S (oT + 96)) (S oR) (S (oR + 32)) (S (oR + 64)) (S (oR + 96))

/-- Cached `ge_add(R, AI[1], T)`. -/
def addF : List FOp :=
  addOps true false oA oB oC oD (S oR) (S (oR + 32)) (S (oR + 64)) (S (oR + 96))
    (S (oAI + 128)) (S (oAI + 160)) (S (oAI + 192)) (S (oAI + 224))
    (S oT) (S (oT + 32)) (S (oT + 64)) (S (oT + 96))

/-- From the body's start to the top-digit scan. -/
def segPre : Prog DS DB :=
  .op (spill 0 oOut) <| .op (spill 1 oSp) <| .op (spill 2 oHp) <| .op (spill 3 oAp) <|
  negA 201 196 <| toCached 0 186 <| fragC .f dblF <| fragC .f (p3F true) <| toCached 1 143 <|
  negA 142 137 <| fragC .f addF <| fragC .f (p3F true) <| toCached 1 89 .nil

/-- `set_identity(R)`. -/
def segId : Prog DS DB := Prog.ofList [call .zero [(0, S oR), (1, K 32)], blk .ident [(0, S oR)]]

def segDbl : Prog DS DB := fragC .f dblF .nil
def segP3 : Prog DS DB := fragC .f (p3F true) .nil
def segP2 : Prog DS DB := fragC .f (p3F false) .nil

/-- `signed_add` over `AI` after its pointer block. -/
def saF : List FOp := saOps true oA oB oC oD oEa oEb oEp oTz oTt (S oR) (S (oR + 32)) (S (oR + 64)) (S (oR + 96))
  (S oT) (S (oT + 32))

/-- `signed_add` over `AI`: the first load of `A · (y + x)` is before the literal pool (`b` over
`mov r8, r8` and 28 data bytes), the call after it. -/
def segSA : Prog DS DB :=
  fragC .f (saF.take 2) (.op (ld 0 (S oA)) (.op (.isl true 28)
    (.op (call (.f .mul) [(1, S oA), (2, W oEa 0)]) (fragC .f (saF.drop 3) .nil))))

/-- `signed_add` over `m0c_ed_odd_b` after its pointer block. -/
def sbF : List FOp := saOps false oA oB oC oD oEa oEb oEp oTz oTt (S oR) (S (oR + 32)) (S (oR + 64)) (S (oR + 96))
  (S oT) (S (oT + 32))

def segSB : Prog DS DB := fragC .f sbF .nil

/-- `X, Y, Z` of `R` to `out`. -/
def segEnd : Prog DS DB := Prog.ofList [call .copy3 [(0, W oOut 0), (1, S oR), (2, K 24)]]

end

/-- The lines at their code offsets, and where each ends. -/
def segs : List (Nat × Prog DS DB) :=
  [(dsm_body, segPre), (dsm_identity, segId), (dsm_double, segDbl), (dsm_dbl_p3, segP3), (dsm_dbl_p2, segP2), (dsm_a_add, segSA),
   (dsm_a_p3, segP3), (dsm_a_p2, segP2), (dsm_b_add, segSB), (dsm_b_p2, segP2), (dsm_output, segEnd)]

def segEnds : List Nat :=
  [dsm_start_scan, dsm_loop, dsm_test_digits, dsm_dbl_jump, dsm_test_a, dsm_a_test_next, dsm_a_jump_join, dsm_a_done, dsm_b_p2, dsm_dec_index, dsm_leave]

/-! ## The decided checks, both builds -/

theorem seg_ends : (segs.zip segEnds).all (fun p => p.1.1 + p.1.2.size dsS dbS == p.2) = true := by decide +kernel

theorem seg_pieces (b : Build) :
    segs.all (fun p => piecesAt b.bytes p.1 (Prog.emit dsS dbS [] p.1 p.2)) = true := by
  cases b <;> (simp only [segs, List.all_cons, List.all_nil, Bool.and_true, piecesAt_eq_scan]; decide +kernel)

theorem seg_bok (b : Build) :
    segs.all (fun p => @Prog.bok _ _ b.codeBytes _ _ dsS dbS dsGeo [] p.2 p.1) = true := by
  cases b <;> decide +kernel

/-! ## The static states -/

def rs (st : St) : St := { st with σ := σsp }

def stE : St := { Γ := [], σ := [(0, .ext 0 0), (1, .ext 1 0), (2, .ext 2 0), (3, .ext 3 0), (13, .sp 0)], X := [] }
def s0 : St := (segPre.ty dsS dbS dsGeo stE).getD stE
def s1 : St := (segId.ty dsS dbS dsGeo (rs s0)).getD stE

def sD : St := (segDbl.ty dsS dbS dsGeo (rs s1)).getD stE
def sP3 : St := (segP3.ty dsS dbS dsGeo (rs sD)).getD stE

/-- The pointer words of `signed_add` for entry `k` at `ep` and sign `s`. -/
def ptrΓ (ep : Nat → SV) (s : Nat) : List (Loc × Kd) :=
  [(.fr oEa, .pw (ep (32 * s))), (.fr oEb, .pw (ep (32 - 32 * s))), (.fr oEp, .pw (ep 0)),
   (.fr oTz, .pw (.sp (oT + 64 + 32 * s))), (.fr oTt, .pw (.sp (oT + 96 - 32 * s)))]

def aiP (k e : Nat) : SV := .sp (oAI + 128 * k + e)
def obP (k e : Nat) : SV := .ext 5 (96 * k + e)

def saSt (k s : Nat) : St := { rs sP3 with Γ := ptrΓ (aiP k) s ++ (rs sP3).Γ }
def sbSt (k s : Nat) : St := { rs sP3 with Γ := ptrΓ (obP k) s ++ (rs sP3).Γ }

/-! ## The values of `signed_add` -/

def frL (o : Nat) : Tm := .v (.view (.fr o))
def obL (e : Nat) : Tm := .v (.xf ⟨.ex 5 e, .k 32⟩)

/-- `T`'s four coordinates. -/
def tLocs : List Loc := [.fr oT, .fr (oT + 32), .fr (oT + 64), .fr (oT + 96)]

/-- `ge_add`'s terms from `R` and the entry with leaves `e`, negated for sign `s`. -/
def addR (cached : Bool) (s : Nat) (e : Nat → Tm) : List Tm :=
  addT cached (s == 1) (frL oR) (frL (oR + 32)) (frL (oR + 64)) (frL (oR + 96)) (e 0) (e 32) (e 64)
    (if cached then e 96 else .bot)

/-- The decided check at a state: the fragment resolves, and `T`'s terms are `ge_add`'s with the
entry `e` and sign `s` (the swapped pointers negate the entry). -/
def chkAt (st : St) (ops : List FOp) (cached : Bool) (s : Nat) (e : Nat → Tm) : Bool :=
  match fresC dsGeo st ops with
  | some (L, _) => decide (tLocs.map (symL tm0 L) = addR cached s e)
  | none => false

theorem chkAt_sound {st : St} {ops : List FOp} {cached : Bool} {s : Nat} {e : Nat → Tm}
    (h : chkAt st ops cached s e = true) :
    ∃ L st', fresC dsGeo st ops = some (L, st') ∧ tLocs.map (symL tm0 L) = addR cached s e := by
  unfold chkAt at h
  split at h
  · rename_i L st' hf; exact ⟨L, st', hf, of_decide_eq_true h⟩
  · exact absurd h (by simp)

/-- **`signed_add` over `AI` resolves**, for both entries and signs, at the first pass. -/
theorem sa_terms : ∀ k < 2, ∀ s < 2, chkAt (saSt k s) saF true s (fun e => frL (oAI + 128 * k + e)) = true := by
  decide +kernel

/-- **`signed_add` over `m0c_ed_odd_b` resolves**, for the eight entries and both signs. -/
theorem sb_terms : ∀ k < 8, ∀ s < 2, chkAt (sbSt k s) sbF false s (fun e => obL (96 * k + e)) = true := by
  decide +kernel

/-- **The values of a resolved `signed_add`**: from `p3` values of `A` at `R` and the entry's
cached (or Niels) values of `Q`, `p1p1` values of `A + Q` at `T`, or `A − Q` for sign `1`. -/
theorem add_rep {st : St} {ops : List FOp} {cached : Bool} {s : Nat} {e : Nat → Lf}
    (h : chkAt st ops cached s (fun o => .v (e o)) = true) :
    ∃ L st', fresC dsGeo st ops = some (L, st') ∧ ∀ (val : Lf → V) (A Q : EdPt),
      RepV [val (.view (.fr oR)), val (.view (.fr (oR + 32))), val (.view (.fr (oR + 64))), val (.view (.fr (oR + 96)))] A →
      (if cached then CachedV [val (e 0), val (e 32), val (e 64), val (e 96)] Q else NielsV [val (e 0), val (e 32), val (e 64)] Q) →
      RepCV (tLocs.map fun l => (symL tm0 L l).ev val) (if s == 1 then A - Q else A + Q) := by
  obtain ⟨L, st', hf, ht⟩ := chkAt_sound h
  refine ⟨L, st', hf, fun val A Q hA hQ => ?_⟩
  cases cached
  · exact madd_val (val := val) ht hA hQ
  · exact cadd_val (val := val) ht hA hQ

/-- **The digit's entry**: entry `|δ| / 2` (the multiple `2 (|δ| / 2) + 1`), negated by the sign
bit, adds `[δ] P`. -/
theorem signed_eq {δ : Int} (hodd : δ % 2 = 1) (A P : EdPt) :
    (if (if δ < 0 then 1 else 0) == 1 then A - ((2 * (δ.natAbs / 2) + 1 : Nat) : Int) • P
      else A + ((2 * (δ.natAbs / 2) + 1 : Nat) : Int) • P) = A + δ • P := by
  rw [← Ed25519Wnaf.oddEntry_eq hodd P]
  by_cases h : δ < 0
  · simp only [h, ↓reduceIte, beq_self_eq_true]
    rw [AddCommGroup.sub_eq_add_neg]
  · simp only [h, ↓reduceIte]
    rfl

/-! ## `ge_dbl` and `ge_p1p1_to_p3` -/

/-- `R`'s coordinates. -/
def rLocs : List Loc := [.fr oR, .fr (oR + 32), .fr (oR + 64), .fr (oR + 96)]

/-- The decided check of `ge_dbl` at a state: `T`'s terms are the doubling of `R`'s `X, Y, Z`. -/
def dblChk (st : St) : Bool :=
  match fresC dsGeo st dblF with
  | some (L, _) => decide (tLocs.map (symL tm0 L) = dblT (frL oR) (frL (oR + 32)) (frL (oR + 64)))
  | none => false

/-- The decided check of `ge_p1p1_to_p3` (`p2` without `T`) at a state. -/
def p3Chk (withT : Bool) (st : St) : Bool :=
  match fresC dsGeo st (p3F withT) with
  | some (L, _) => decide ((if withT then rLocs else rLocs.take 3).map (symL tm0 L) =
      p3T withT (frL oT) (frL (oT + 32)) (frL (oT + 64)) (frL (oT + 96)))
  | none => false

/-- **`ge_dbl` resolved**: from `p2` values of `A` at `R`, `p1p1` values of `2A` at `T`. -/
theorem dbl_rep {st : St} (h : dblChk st = true) :
    ∃ L st', fresC dsGeo st dblF = some (L, st') ∧ ∀ (val : Lf → V) (A : EdPt),
      Rep2V [val (.view (.fr oR)), val (.view (.fr (oR + 32))), val (.view (.fr (oR + 64)))] A →
      RepCV (tLocs.map fun l => (symL tm0 L l).ev val) (A + A) := by
  unfold dblChk at h
  split at h
  · rename_i L st' hf
    exact ⟨L, st', hf, fun val A hA => dbl_val (val := val) (of_decide_eq_true h) hA⟩
  · exact absurd h (by simp)

/-- **`ge_p1p1_to_p3` resolved**: from `p1p1` values of `A` at `T`, `p3` values at `R`. -/
theorem p3_rep {st : St} (h : p3Chk true st = true) :
    ∃ L st', fresC dsGeo st (p3F true) = some (L, st') ∧ ∀ (val : Lf → V) (A : EdPt),
      RepCV [val (.view (.fr oT)), val (.view (.fr (oT + 32))), val (.view (.fr (oT + 64))), val (.view (.fr (oT + 96)))] A →
      RepV (rLocs.map fun l => (symL tm0 L l).ev val) A := by
  unfold p3Chk at h
  split at h
  · rename_i L st' hf
    exact ⟨L, st', hf, fun val A hA => p3_val (val := val) (of_decide_eq_true h) hA⟩
  · exact absurd h (by simp)

/-- **Without `T`**: `p2` values at `R`'s `X, Y, Z`. -/
theorem p2_rep {st : St} (h : p3Chk false st = true) :
    ∃ L st', fresC dsGeo st (p3F false) = some (L, st') ∧ ∀ (val : Lf → V) (A : EdPt),
      RepCV [val (.view (.fr oT)), val (.view (.fr (oT + 32))), val (.view (.fr (oT + 64))), val (.view (.fr (oT + 96)))] A →
      Rep2V ((rLocs.take 3).map fun l => (symL tm0 L l).ev val) A := by
  unfold p3Chk at h
  split at h
  · rename_i L st' hf
    exact ⟨L, st', hf, fun val A hA => p2_val (val := val) (of_decide_eq_true h) hA⟩
  · exact absurd h (by simp)

/-- The first pass: the doubling after the identity, then both conversions. -/
theorem pass_chks : dblChk (rs s1) = true ∧ p3Chk true (rs sD) = true ∧ p3Chk false (rs sD) = true ∧
    p3Chk true (rs sP3) = true ∧ p3Chk false (rs sP3) = true := by
  decide +kernel

/-! ## `neg_a` and `to_cached` in values -/

open M0Crypto.Release.Ed25519Formulas (Rep Cached d2 negExt negExt_rep)

/-- **`neg_a`**: `(0 − X, Y, Z, 0 − T)` represents `−A`. -/
theorem negA_rep {x y z t zr : Int} {A : EdPt} (hz : fI zr = 0) (h : RepV [.f x, .f y, .f z, .f t] A) :
    RepV [.f (zr - x), .f y, .f z, .f (zr - t)] (-A) := by
  obtain ⟨x', y', z', t', he, hr⟩ := h
  simp only [List.cons.injEq, V.f.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  refine ⟨_, _, _, _, rfl, ?_⟩
  rw [fI_sub, fI_sub, hz]
  exact negExt_rep hr

/-- **`to_cached`**: `(Y + X, Y − X, Z, T · 2d)` is the cached form of a representative of `A`. -/
theorem cached_rep {x y z t dv : Int} {A : EdPt} (hd : fI dv = d2) (h : RepV [.f x, .f y, .f z, .f t] A) :
    CachedV [.f (y + x), .f (y - x), .f z, .f (t * dv)] A := by
  obtain ⟨x', y', z', t', he, hr⟩ := h
  simp only [List.cons.injEq, V.f.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  refine ⟨_, _, _, _, rfl, _, hr, ?_⟩
  rw [fI_add, fI_sub, fI_mul, hd]; rfl

/-! ## The table `AI` -/

/-- The precomputation's prefixes: to the doubling, and from the first `AI[1]` to the addition. -/
def preA : Prog DS DB :=
  .op (.spill 0 oOut) <| .op (.spill 1 oSp) <| .op (.spill 2 oHp) <| .op (.spill 3 oAp) <|
  negA 201 196 <| toCached 0 186 .nil
def preB : Prog DS DB := toCached 1 143 <| negA 142 137 .nil

def stA : St := (preA.ty dsS dbS dsGeo stE).getD stE
def stB : St := ((fresC dsGeo stA dblF).map (·.2)).getD stE
def stC : St := ((fresC dsGeo stB (p3F true)).map (·.2)).getD stE
def stD : St := (preB.ty dsS dbS dsGeo stC).getD stE
def stF : St := ((fresC dsGeo stD addF).map (·.2)).getD stE

/-- **The precomputation's fragments resolve**: the doubling of `−A`, its `p3` form, the cached
addition of `AI[1]` to `−A`, its `p3` form; `segPre` is these lines in this order (`pre_split`). -/
theorem pre_chks : preA.ty dsS dbS dsGeo stE = some stA ∧ dblChk stA = true ∧ p3Chk true stB = true ∧
    preB.ty dsS dbS dsGeo stC = some stD ∧ chkAt stD addF true 0 (fun e => frL (oAI + 128 + e)) = true ∧
    p3Chk true stF = true := by
  decide +kernel

theorem pre_split : segPre = preA.seq (fragC .f dblF (fragC .f (p3F true) (preB.seq (fragC .f addF
    (fragC .f (p3F true) (toCached 1 89 .nil)))))) := rfl

/-- `−A + 2(−A) = [3](−A)`: the second entry. -/
theorem three_eq (P : EdPt) : P + (P + P) = ((2 * 1 + 1 : Nat) : Int) • P := by
  rw [show ((2 * 1 + 1 : Nat) : Int) = 1 + 1 + 1 from rfl, IntModule.add_zsmul, IntModule.add_zsmul,
    IntModule.one_zsmul]
  grind

theorem one_eq (P : EdPt) : P = ((2 * 0 + 1 : Nat) : Int) • P := by
  rw [show ((2 * 0 + 1 : Nat) : Int) = 1 from rfl, IntModule.one_zsmul]

end M0Crypto.Release.Ed25519DsmProg
