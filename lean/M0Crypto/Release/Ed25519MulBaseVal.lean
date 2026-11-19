import M0Crypto.Release.Ed25519MulBaseProg
import M0Crypto.Release.Ed25519CallProgLin
import M0Crypto.Release.Ed25519WordAd
import M0Crypto.Release.Ed25519TableLink
import M0Crypto.Release.Ed25519ScalarMul

/-!
# `m0c_ge_mul_base`'s values

The program's control flow is public, so its static run `Prog.lin` lists its updates; `mb_lin`
decides that list in a closed form: the prologue `proR`, the digit passes `runsR` (a lookup, the
addition, the conversion, and at the end of a round the doubling), and the epilogue `epiR`. A
field fragment's updates are its symbolic run (`runR_frR`), so `GeProg`'s formula lemmas apply to
each pass. The passes follow `Ed25519Comb.combRun`.
-/

namespace M0Crypto.Release.Ed25519MulBaseVal

open M0Crypto.Armv6M (Word Reg Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519MulBaseProg
open M0Crypto.Release.Ed25519Group (EdPt)
open Lean.Grind

/-! ## Fragments as updates -/

/-- A frame loader's location. -/
def ldLoc : Ld → Loc
  | .S o => .fr o
  | _ => .rg 0

def lfSrc : Lf → Src
  | .view l => .view l
  | .xf r => .extF r

/-- A fragment of frame operands, resolved. -/
def flOf (ops : List FOp) : FL :=
  ops.map fun o => (ldLoc o.d, o.a, (match o.a with | .sqr => [o.s] | _ => [o.s, o.t]).map fun l => .view (ldLoc l))

/-- A resolved fragment's updates. -/
def frR {A Bk : Type} (ι : FA → A) (L : FL) : List (ROp A Bk) :=
  L.map fun p => .call (ι p.2.1) [(p.1, .fe)] (p.2.2.map lfSrc)

section
variable {A Bk : Type} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V}
  {c : Ctx} {m0 : Mem} {ι : FA → A}

theorem lf_val (E0 : Loc → V) {cur : Loc → Tm} {E : Loc → V} (hE : ∀ l, E l = (cur l).ev (lfV G c m0 E0)) :
    ∀ ls : List Lf, (ls.map lfSrc).map (Src.val G c m0 E) = ls.map fun x => (lfT cur x).ev (lfV G c m0 E0)
  | [] => rfl
  | x :: ls => by
    rw [List.map_cons, List.map_cons, List.map_cons, lf_val E0 hE ls]
    cases x
    · exact congrArg (· :: _) (hE _)
    · rfl

/-- **A fragment's updates** are its symbolic run. -/
theorem runR_frR (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) (E0 : Loc → V) :
    ∀ (L : FL) (cur : Loc → Tm) (E : Loc → V), (∀ l, E l = (cur l).ev (lfV G c m0 E0)) →
      ∀ l, runR bE G semA semB c m0 (frR ι L) E l = (symL cur L l).ev (lfV G c m0 E0)
  | [], _, _, hE, l => hE l
  | p :: L, cur, E, hE, l => by
    refine runR_frR hS E0 L (stepT cur p) _ (fun x => ?_) l
    simp only [ROp.ev, hS, updOuts, stepT]
    split
    · rw [opT_ev, lf_val E0 hE, List.map_map]; rfl
    · exact hE x

theorem runR_frag (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) (L : FL) (E : Loc → V) :
    runR bE G semA semB c m0 (frR ι L) E = fragE G c m0 E L :=
  funext (runR_frR hS E L tm0 E fun _ => rfl)

end

/-! ## The program's updates -/

/-- Views of `n` elements from `o`, of kind `k`. -/
def fes (o n : Nat) (k : Kd) : List (Loc × Kd) := (List.range n).map fun j => (.fr (o + 32 * j), k)
def vws (o n : Nat) : List Src := (List.range n).map fun j => .view (.fr (o + 32 * j))

/-- Digit `q` closes a round other than the last. -/
def dbl? (nc q : Nat) : Bool := q % nc == 0 && q != 0

/-- The comb (row) of digit `q`. -/
def row (nc q : Nat) : Nat := nc - 1 - q % nc

/-- Digit `q`'s pass: its byte, the digit, the lookup in its row, the addition, the conversion,
and the doubling that closes a round. -/
def passR (nc q : Nat) : List (ROp MA MB) :=
  [.ldb 2 (.slice (.fr E) q 1), .blk .sub8 [] [.view (.rg 2)],
   .call .look (fes N 3 .fe) [.ext ⟨.ex 2 (768 * row nc q), .k 768⟩, .view (.rg 2)]] ++
  frR MA.f (flOf (addF false)) ++ frR MA.f (flOf (p3F (!dbl? nc q))) ++
  (if dbl? nc q then frR MA.f (flOf dblF) ++ frR MA.f (flOf (p3F true)) else [])

/-- The passes of the digits `q − 1, …, 0`. -/
def runsR (nc : Nat) : Nat → List (ROp MA MB)
  | 0 => []
  | q + 1 => passR nc q ++ runsR nc q

def proR : List (ROp MA MB) :=
  [.call .recode [(.fr E, .bytes 64)] [.ext ⟨.ex 1 0, .k 32⟩], .call .zero4 (fes H 4 (.bytes 32)) [],
   .blk .ident (fes H 4 .fe) (vws H 4)]

def epiR : List (ROp MA MB) :=
  [.call .zero3 (fes N 3 (.bytes 32)) [], .blk .nset (fes N 3 (.bytes 32)) (vws N 3),
   .blk .mask [] [.ext ⟨.ex 1 0, .k 32⟩],
   .call .cmov3 (fes N 3 .fe) (vws N 3 ++ [.ext ⟨.ex 3 0, .k 96⟩, .view (.rg 3)])] ++
  frR MA.f (flOf (addF true)) ++ frR MA.f (flOf (p3F true)) ++ [.call .copyPt [(.ex 0 0, .fe4)] (vws H 4)]

/-- **The program's updates**, one closed `decide` per build. -/
theorem mb_lin (b : Build) :
    ((mbP b.combs).lin maS mbS (mbQ b.combs).geo (mbQ b.combs).st0).map Prod.fst =
      some (proR ++ runsR b.combs 64 ++ epiR) := by
  cases b <;> decide +kernel

/-! ## The values of the callees and blocks -/

open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519Words (wsum)
open M0Crypto.Release.Ed25519WordLoop (sel)
open M0Crypto.Release.Ed25519ScReduceProg (dW)
open M0Crypto.Release.Ed25519LookupTE (lookV)
open M0Crypto.Release.Ed25519RecodeAd (recV)

/-- The bytes with their low word `1`. -/
def setLo (l : List (BitVec 8)) : List (BitVec 8) := [1, 0, 0, 0] ++ l.drop 4

def identV : List V → List V
  | [.b a, .b b, .b c, .b d] => [.f (decodeInt a), .f (decodeInt (setLo b)), .f (decodeInt (setLo c)), .f (decodeInt d)]
  | _ => [.none, .none, .none, .none]

def nsetV : List V → List V
  | [.b a, .b b, .b c] => [.b (setLo a), .b (setLo b), .b c]
  | _ => [.none, .none, .none]

/-- All ones for an even first byte, else zero. -/
def maskV : List V → List V
  | [.b l] => [.w (((l.headD 0).setWidth 32 &&& 1#32) - 1#32)]
  | _ => [.none]

def sub8V : List V → List V
  | [.w x] => [.w (x - 8#32)]
  | _ => [.none]

/-- The number of `m0c_cmov`'s words of `d` and `s` under the mask `κ`. -/
def selF (κ : Word) (d s : List (BitVec 8)) : Int := wsum (fun j => (sel κ (dW d j) (dW s j)).toNat) 8

def cmov3V : List V → List V
  | [.b x, .b y, .b z, .b l, .w κ] =>
    [.f (selF κ x (l.take 32)), .f (selF κ y ((l.drop 32).take 32)), .f (selF κ z (l.drop 64))]
  | _ => [.none, .none, .none]

/-- A field value as its residue. -/
def nm (x : Int) : Nat := (x % Field25519Congr.p).toNat

def copyPtV : List V → List V
  | [.f x, .f y, .f z, .f t] => [.p ⟨nm x, nm y, nm z, nm t⟩]
  | _ => [.none]

/-- The callees' values for `nc` combs. -/
def mbV (nc : Nat) : MA → List V → List V
  | .recode => recV nc
  | .zero4 => Ed25519WordAd.zeroV 4
  | .zero3 => Ed25519WordAd.zeroV 3
  | .look => lookV
  | .f a => fun vs => [faV a vs]
  | .cmov3 => cmov3V
  | .copyPt => copyPtV

def mbBV : MB → List V → List V
  | .ident => identV
  | .nset => nsetV
  | .mask => maskV
  | .sub8 => sub8V

/-! ## The fragments' terms -/

def lv (o : Nat) : Tm := .v (.view (.fr o))
def Hs : List Loc := [.fr H, .fr (H + 32), .fr (H + 64), .fr (H + 96)]
def Ts : List Loc := [.fr T, .fr (T + 32), .fr (T + 64), .fr (T + 96)]

theorem add_terms (neg : Bool) : Ts.map (symL tm0 (flOf (addF neg))) =
    addT false neg (lv H) (lv (H + 32)) (lv (H + 64)) (lv (H + 96)) (lv N) (lv (N + 32)) (lv (N + 64)) .bot := by
  cases neg <;> decide

theorem p3_terms : Hs.map (symL tm0 (flOf (p3F true))) = p3T true (lv T) (lv (T + 32)) (lv (T + 64)) (lv (T + 96)) := by
  decide

theorem p2_terms : (Hs.take 3).map (symL tm0 (flOf (p3F false))) =
    p3T false (lv T) (lv (T + 32)) (lv (T + 64)) (lv (T + 96)) := by
  decide

theorem dbl_terms : Ts.map (symL tm0 (flOf dblF)) = dblT (lv H) (lv (H + 32)) (lv (H + 64)) := by
  decide

/-- The fragments keep the digit bytes. -/
theorem keepE : ∀ L ∈ [flOf (addF false), flOf (addF true), flOf (p3F true), flOf (p3F false), flOf dblF],
    symL tm0 L (.fr E) = tm0 (.fr E) := by
  decide

/-! ## One pass -/

section
variable {nc : Nat} {c : Ctx} {m0 : Mem}

/-- The program's updates as values. -/
abbrev runM (nc : Nat) (c : Ctx) (m0 : Mem) : List (ROp MA MB) → (Loc → V) → Loc → V :=
  runR mbS (mbQ nc).geo (mbV nc) mbBV c m0

/-- The bytes of digit `q`'s row. -/
def rowV (nc : Nat) (c : Ctx) (m0 : Mem) (q : Nat) : V :=
  Src.val (mbQ nc).geo c m0 (fun _ => .none) (.ext ⟨.ex 2 (768 * row nc q), .k 768⟩)

/-- The digit word of a digit byte. -/
def dword (x : BitVec 8) : Word := x.setWidth 32 - 8#32

theorem hS (nc : Nat) : ∀ a vs, mbV nc (MA.f a) vs = [faV a vs] := fun _ _ => rfl

theorem run_app (L L' : List (ROp MA MB)) (ε : Loc → V) :
    runM nc c m0 (L ++ L') ε = runM nc c m0 L' (runM nc c m0 L ε) := runR_append _ _ _ _ _ _ _ _ _

theorem run_frag (L : FL) (R : List (ROp MA MB)) (ε : Loc → V) :
    runM nc c m0 (frR MA.f L ++ R) ε = runM nc c m0 R (fragE (mbQ nc).geo c m0 ε L) := by
  unfold runM; rw [runR_append, runR_frag (hS nc)]

theorem run_frag1 (L : FL) (ε : Loc → V) :
    runM nc c m0 (frR MA.f L) ε = fragE (mbQ nc).geo c m0 ε L := runR_frag (hS nc) L ε

theorem fesN : fes N 3 .fe = [(.fr N, .fe), (.fr (N + 32), .fe), (.fr (N + 64), .fe)] := rfl

theorem fragE_E {L : FL} (h : symL tm0 L (.fr E) = tm0 (.fr E)) (ε : Loc → V) :
    fragE (mbQ nc).geo c m0 ε L (.fr E) = ε (.fr E) := by
  simp only [fragE, h, tm0, Tm.ev, lfV]

/-- **A digit pass**: from `p3` values of `A` at `H`, `p3` values of `A + P` (doubled at the end
of a round), where `P` is the lookup's entry; the digit bytes stay. -/
theorem pass_val {q : Nat} {ε : Loc → V} {dg : List (BitVec 8)} {A P : EdPt} (hq : q < dg.length)
    (hE : ε (.fr E) = .b dg) (hH : RepV (Hs.map ε) A)
    (hP : NielsV (lookV [rowV nc c m0 q, .w (dword dg[q])]) P) :
    runM nc c m0 (passR nc q) ε (.fr E) = .b dg ∧
      RepV (Hs.map (runM nc c m0 (passR nc q) ε)) (if dbl? nc q then (A + P) + (A + P) else A + P) := by
  obtain ⟨a, b, e, hl, hn⟩ := hP
  generalize hε' : runM nc c m0 [.ldb 2 (.slice (.fr E) q 1), .blk .sub8 [] [.view (.rg 2)]] ε = ε'
  have hsl : Src.val (mbQ nc).geo c m0 ε (.slice (.fr E) q 1) = .b [dg[q]] := by
    simp only [Src.val, hE, List.drop_eq_getElem_cons hq, List.take_succ_cons, List.take_zero]
  have hr2 : ε' (.rg 2) = .w (dword dg[q]) := by
    rw [← hε']
    simp only [runM, runR, ROp.ev, hsl]
    rfl
  have hfr : ∀ o, ε' (.fr o) = ε (.fr o) := fun o => by rw [← hε']; rfl
  generalize hε1 : runM nc c m0 [.ldb 2 (.slice (.fr E) q 1), .blk .sub8 [] [.view (.rg 2)],
    .call .look (fes N 3 .fe) [.ext ⟨.ex 2 (768 * row nc q), .k 768⟩, .view (.rg 2)]] ε = ε1
  have e1 : ε1 = updOuts ε' (fes N 3 .fe) [.f a, .f b, .f e] := by
    rw [← hε1, ← hl, ← hr2, ← hε']; rfl
  have h1 : ∀ o, o ≠ N → o ≠ N + 32 → o ≠ N + 64 → ε1 (.fr o) = ε (.fr o) := fun o h0 h1 h2 => by
    rw [e1, ← hfr o, fesN]; simp only [updOuts, Loc.fr.injEq, h0, h1, h2, ↓reduceIte]
  have hA : RepV [lfV (mbQ nc).geo c m0 ε1 (.view (.fr H)), lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 32))),
      lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 64))), lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 96)))] A := by
    simp only [lfV]
    rw [h1 _ (by decide) (by decide) (by decide), h1 _ (by decide) (by decide) (by decide),
      h1 _ (by decide) (by decide) (by decide), h1 _ (by decide) (by decide) (by decide)]
    exact hH
  have hQ : NielsV [lfV (mbQ nc).geo c m0 ε1 (.view (.fr N)), lfV (mbQ nc).geo c m0 ε1 (.view (.fr (N + 32))),
      lfV (mbQ nc).geo c m0 ε1 (.view (.fr (N + 64)))] P := by
    simp only [lfV, e1]
    exact ⟨a, b, e, by simp [updOuts, fesN], hn⟩
  have hadd := madd_val (add_terms false) hA hQ
  simp only [Bool.false_eq_true, ↓reduceIte] at hadd
  have hE1 : ε1 (.fr E) = .b dg := by rw [h1 _ (by decide) (by decide) (by decide), hE]
  have hkE := fun L h => @fragE_E nc c m0 L h
  unfold passR
  rw [show ∀ (x : List (ROp MA MB)) y z w, x ++ y ++ z ++ w = x ++ (y ++ (z ++ w)) from fun _ _ _ _ => by
    simp only [List.append_assoc], run_app, hε1, run_frag]
  generalize hε2 : fragE (mbQ nc).geo c m0 ε1 (flOf (addF false)) = ε2
  have hE2 : ε2 (.fr E) = .b dg := by rw [← hε2, hkE _ (keepE _ (by simp)), hE1]
  have hT2 : RepCV (Ts.map ε2) (A + P) := by rw [← hε2]; exact hadd
  cases hd : dbl? nc q
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, run_frag1]
    exact ⟨by rw [hkE _ (keepE _ (by simp))]; exact hE2, p3_val p3_terms hT2⟩
  · simp only [Bool.not_true, ↓reduceIte, run_frag, run_frag1]
    generalize hε3 : fragE (mbQ nc).geo c m0 ε2 (flOf (p3F false)) = ε3
    have hE3 : ε3 (.fr E) = .b dg := by rw [← hε3, hkE _ (keepE _ (by simp)), hE2]
    have hH3 : Rep2V ((Hs.take 3).map ε3) (A + P) := by rw [← hε3]; exact p2_val p2_terms hT2
    generalize hε4 : fragE (mbQ nc).geo c m0 ε3 (flOf dblF) = ε4
    have hE4 : ε4 (.fr E) = .b dg := by rw [← hε4, hkE _ (keepE _ (by simp)), hE3]
    have hT4 : RepCV (Ts.map ε4) (A + P + (A + P)) := by rw [← hε4]; exact dbl_val dbl_terms hH3
    exact ⟨by rw [hkE _ (keepE _ (by simp))]; exact hE4, p3_val p3_terms hT4⟩
end

/-! ## The passes, the prologue, the epilogue -/

section
variable {nc : Nat} {c : Ctx} {m0 : Mem}
open M0Crypto.Release.Ed25519Comb

/-- **The digit passes** follow `combRun`. -/
theorem runs_val {dg : List (BitVec 8)} {δ : Nat → Int}
    (hP : ∀ q (h : q < dg.length), q < 64 → NielsV (lookV [rowV nc c m0 q, .w (dword dg[q])]) (combPt nc δ q))
    (hl : 64 ≤ dg.length) :
    ∀ q, q ≤ 64 → ∀ (ε : Loc → V) (A : EdPt), ε (.fr E) = .b dg → RepV (Hs.map ε) A →
      runM nc c m0 (runsR nc q) ε (.fr E) = .b dg ∧
        RepV (Hs.map (runM nc c m0 (runsR nc q) ε)) (combRun nc δ q A)
  | 0, _, _, _, hE, hH => ⟨hE, hH⟩
  | q + 1, hq, ε, A, hE, hH => by
    obtain ⟨e1, r1⟩ := pass_val (by omega) hE hH (hP q (by omega) (by omega))
    rw [runsR, run_app]
    refine runs_val hP hl q (by omega) _ _ e1 ?_
    have : (if dbl? nc q = true then A + combPt nc δ q + (A + combPt nc δ q) else A + combPt nc δ q) =
        combStep nc δ A q := by
      unfold combStep
      by_cases h : q % nc = 0 ∧ q ≠ 0
      · have hd : dbl? nc q = true := by simp only [dbl?, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]; exact h
        simp only [hd, h, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      · have hd : dbl? nc q = false := by
          simp only [dbl?, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]; omega
        simp only [hd, h, Bool.false_eq_true, ↓reduceIte]
    rw [this] at r1; exact r1

theorem r4 : List.range 4 = [0, 1, 2, 3] := rfl
theorem r3 : List.range 3 = [0, 1, 2] := rfl

/-- The scalar's bytes. -/
def kB (c : Ctx) (m0 : Mem) : List (BitVec 8) := Footprint.bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) 32

theorem zero_dec : decodeInt ((List.range 32).map fun _ => (0 : BitVec 8)) = 0 ∧
    decodeInt (setLo ((List.range 32).map fun _ => (0 : BitVec 8))) = 1 := by decide

theorem rep0 : RepV [.f 0, .f 1, .f 1, .f 0] 0 :=
  ⟨0, 1, 1, 0, rfl, by
    have h0 : fI 0 = 0 := by rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, fI_nat]; decide
    have h1 : fI 1 = 1 := by rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, fI_nat]; decide
    have e : (⟨fI 0, fI 1, fI 1, fI 0⟩ : Ed25519EdwardsExtended.Ext Ed25519Field.Fp) = Ed25519Formulas.identity := by
      rw [h0, h1]; rfl
    rw [e]; exact Ed25519Formulas.rep_identity⟩

/-- **The prologue**: the digit bytes of the scalar, `H` the identity. -/
theorem pro_val (ε0 : Loc → V) :
    runM nc c m0 proR ε0 (.fr E) = .b (Ed25519RecodeAd.recBytes nc (decodeInt (kB c m0))) ∧
      RepV (Hs.map (runM nc c m0 proR ε0)) 0 := by
  refine ⟨rfl, ?_⟩
  have : Hs.map (runM nc c m0 proR ε0) = [.f 0, .f 1, .f 1, .f 0] := by
    show [_, _, _, _] = _
    simp only [runM, runR, ROp.ev, proR, fes, vws, mbBV, mbS, ioIdent, mbV, Ed25519WordAd.zeroV, r4,
      List.map_cons, List.map_nil, Src.val, updOuts, identV]
    simp [updOuts, setRg]
    exact ⟨zero_dec.1, by decide, zero_dec.1⟩
  rw [this]; exact rep0

end

section
variable {nc : Nat} {c : Ctx} {m0 : Mem}
open M0Crypto.Release.Ed25519Comb
open M0Crypto.Release.Ed25519Bridge (Bpt)

/-- The bytes of `odd_b[0]`, `B` in Niels form. -/
def oB (c : Ctx) (m0 : Mem) : List (BitVec 8) := Footprint.bytesAt m0 (c.ptr 3 + BitVec.ofNat 32 0) 96

def oddV (c : Ctx) (m0 : Mem) : List V :=
  [.f (decodeInt ((oB c m0).take 32)), .f (decodeInt (((oB c m0).drop 32).take 32)), .f (decodeInt ((oB c m0).drop 64))]

theorem mask_byte : ∀ b : BitVec 8,
    ((b.setWidth 32 &&& 1#32) - 1#32) = if b.toNat % 2 = 0 then BitVec.allOnes 32 else 0 := by decide

theorem dec_lt {l : List (BitVec 8)} (h : l.length = 32) : decodeInt l % 2 ^ (32 * 8) = decodeInt l :=
  Nat.mod_eq_of_lt (by have := Ed25519Bytes.decodeInt_lt l; rw [h] at this; exact this)

theorem selF_zero (d s : List (BitVec 8)) (h : d.length = 32) : selF 0 d s = decodeInt d := by
  simp only [selF, Ed25519WordLoop.sel_zero, Ed25519ScReduceProg.wsum_dW, dec_lt h]

theorem selF_ones (d s : List (BitVec 8)) (h : s.length = 32) : selF (BitVec.allOnes 32) d s = decodeInt s := by
  simp only [selF, Ed25519WordLoop.sel_ones, Ed25519ScReduceProg.wsum_dW, dec_lt h]

theorem dec_two : ∀ {l : List (BitVec 8)}, l ≠ [] → decodeInt l % 2 = (l.headD 0).toNat % 2
  | b :: bs, _ => by simp only [decodeInt, List.headD_cons]; omega

theorem niels0 : NielsV [.f 1, .f 1, .f 0] 0 := ⟨1, 1, 0, rfl, by
  have h0 : fI 0 = 0 := by rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, fI_nat]; decide
  have h1 : fI 1 = 1 := by rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, fI_nat]; decide
  rw [h0, h1]; exact (Ed25519Formulas.Niels.of_zero _).symm⟩

/-- **The epilogue**: `B` subtracted for an even scalar, the point to `out`. -/
theorem epi_val {ε : Loc → V} {A : EdPt} (hH : RepV (Hs.map ε) A) (hodd : NielsV (oddV c m0) Bpt) :
    ∃ x y z t, runM nc c m0 epiR ε (.ex 0 0) = .p ⟨nm x, nm y, nm z, nm t⟩ ∧
      RepV [.f x, .f y, .f z, .f t] (A - (if decodeInt (kB c m0) % 2 = 0 then Bpt else 0)) := by
  generalize hε1 : runM nc c m0 [.call .zero3 (fes N 3 (.bytes 32)) [], .blk .nset (fes N 3 (.bytes 32)) (vws N 3),
    .blk .mask [] [.ext ⟨.ex 1 0, .k 32⟩],
    .call .cmov3 (fes N 3 .fe) (vws N 3 ++ [.ext ⟨.ex 3 0, .k 96⟩, .view (.rg 3)])] ε = ε1
  generalize hκ : (((kB c m0).headD 0).setWidth 32 &&& 1#32) - 1#32 = κ
  generalize hz : (List.range 32).map (fun _ => (0 : BitVec 8)) = z
  have hN : [ε1 (.fr N), ε1 (.fr (N + 32)), ε1 (.fr (N + 64))] =
      [.f (selF κ (setLo z) ((oB c m0).take 32)), .f (selF κ (setLo z) (((oB c m0).drop 32).take 32)),
        .f (selF κ z ((oB c m0).drop 64))] := by
    rw [← hε1, ← hκ, ← hz]
    simp only [runM, runR, ROp.ev, fes, vws, mbBV, mbS, ioNset, ioMask, mbV, Ed25519WordAd.zeroV, r3,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, Src.val, updOuts, nsetV, maskV, cmov3V]
    simp [updOuts, setRg, kB, oB, Loc.addr, XLen.v]
  have hH1 : Hs.map ε1 = Hs.map ε := by
    rw [← hε1]
    simp only [runM, runR, ROp.ev, fes, vws, mbBV, mbS, ioNset, ioMask, mbV, Ed25519WordAd.zeroV, r3, Hs,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, Src.val, updOuts, nsetV, maskV, cmov3V]
    simp [updOuts, setRg, H, N]
  have hl : (kB c m0).length = 32 := Footprint.bytesAt_length _ _ _
  have ho : (oB c m0).length = 96 := Footprint.bytesAt_length _ _ _
  generalize hQ : (if decodeInt (kB c m0) % 2 = 0 then Bpt else 0) = Q
  have hNQ : NielsV [ε1 (.fr N), ε1 (.fr (N + 32)), ε1 (.fr (N + 64))] Q := by
    rw [hN, ← hQ, dec_two (by intro h; rw [h] at hl; cases hl), ← hκ, mask_byte]
    have hzl : z.length = 32 := by rw [← hz]; rfl
    have hsl : (setLo z).length = 32 := by rw [← hz]; rfl
    have l1 : ((oB c m0).take 32).length = 32 := by simp [ho]
    have l2 : (((oB c m0).drop 32).take 32).length = 32 := by simp [ho]
    have l3 : ((oB c m0).drop 64).length = 32 := by simp [ho]
    split
    · simp only [selF_ones _ _ l1, selF_ones _ _ l2, selF_ones _ _ l3]
      exact hodd
    · simp only [selF_zero _ _ hsl, selF_zero _ _ hzl]
      rw [← hz]; exact niels0
  have hA : RepV [lfV (mbQ nc).geo c m0 ε1 (.view (.fr H)), lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 32))),
      lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 64))), lfV (mbQ nc).geo c m0 ε1 (.view (.fr (H + 96)))] A := by
    show RepV (Hs.map ε1) A; rw [hH1]; exact hH
  have hadd := madd_val (add_terms true) hA hNQ
  simp only [↓reduceIte] at hadd
  unfold epiR
  rw [show ∀ (x : List (ROp MA MB)) y z w, x ++ y ++ z ++ w = x ++ (y ++ (z ++ w)) from fun _ _ _ _ => by
    simp only [List.append_assoc], run_app, hε1, run_frag, run_frag]
  generalize hε3 : fragE (mbQ nc).geo c m0 (fragE (mbQ nc).geo c m0 ε1 (flOf (addF true))) (flOf (p3F true)) = ε3
  have hH3 : RepV (Hs.map ε3) (A - Q) := by rw [← hε3]; exact p3_val p3_terms hadd
  obtain ⟨x, y, z', t, he, hr⟩ := hH3
  refine ⟨x, y, z', t, ?_, ⟨x, y, z', t, rfl, hr⟩⟩
  simp only [Hs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  obtain ⟨e0, e1, e2, e3⟩ := he
  simp only [runM, runR, ROp.ev, vws, r4, List.map_cons, List.map_nil, Src.val, mbV]
  simp only [show H + 32 * 0 = H from rfl, show H + 32 * 1 = H + 32 from rfl, show H + 32 * 2 = H + 64 from rfl,
    show H + 32 * 3 = H + 96 from rfl, e0, e1, e2, e3, copyPtV]
  simp only [updOuts, ↓reduceIte]

end

/-! ## The result -/

section
variable {c : Ctx} {m0 : Mem}
open M0Crypto.Release.Ed25519Comb
open M0Crypto.Release.Ed25519Bridge (Bpt)
open M0Crypto.Release.Ed25519CombDigits (digitAt digitAt_bound)

/-- The bytes of comb `cr`'s row. -/
def rowAt (nc : Nat) (c : Ctx) (m0 : Mem) (cr : Nat) : V :=
  Src.val (mbQ nc).geo c m0 (fun _ => .none) (.ext ⟨.ex 2 (768 * cr), .k 768⟩)

/-- The digit word of a digit `δ`, from its stored byte `δ + 8`. -/
def dwordI (δ : Int) : Word := dword (BitVec.ofNat 8 (δ + 8).toNat)

/-- The lookup in comb `cr`'s row gives the Niels form of the comb's multiple for each nonzero
digit. -/
def LookOk (nc : Nat) (c : Ctx) (m0 : Mem) : Prop :=
  ∀ cr < nc, ∀ δ : Int, -8 ≤ δ → δ ≤ 8 → δ ≠ 0 →
    NielsV (lookV [rowAt nc c m0 cr, .w (dwordI δ)]) (combTerm nc cr δ • Bpt)

theorem outVals_eq (nc : Nat) (ε : Loc → V) : (mbQ nc).outVals ε = [ε (.ex 0 0)] := rfl

/-- **`m0c_ge_mul_base`'s values**: `out` holds `p3` values of `[e]B`, `e` the scalar, when the
lookups and `odd_b[0]` hold their table entries. -/
theorem mb_out (b : Build) (hlk : LookOk b.combs c m0) (hodd : NielsV (oddV c m0) Bpt)
    (hk : decodeInt (kB c m0) < 2 ^ 255) :
    ∃ x y z t, (mbQ b.combs).outVals (Prog.ev maS mbS (mbQ b.combs).geo (mbV b.combs) mbBV c m0 (mbP b.combs)
        (mbQ b.combs).st0 fun _ => .none) = [.p ⟨nm x, nm y, nm z, nm t⟩] ∧
      RepV [.f x, .f y, .f z, .f t] ((decodeInt (kB c m0) : Int) • Bpt) := by
  obtain ⟨⟨L, s⟩, hL, hL1⟩ := Option.map_eq_some_iff.mp (mb_lin b)
  simp only at hL1; subst hL1
  rw [outVals_eq, ((Prog.lin_ev maS mbS _ (mbV b.combs) mbBV c m0 _ _ _ _ hL).2 _)]
  have hnc : 0 < b.combs ∧ b.combs ∣ 64 := by cases b <;> decide
  obtain ⟨hE0, hH0⟩ := pro_val (nc := b.combs) (c := c) (m0 := m0) (fun _ => .none)
  have hdl : (Ed25519RecodeAd.recBytes b.combs (decodeInt (kB c m0))).length = 64 := by
    simp [Ed25519RecodeAd.recBytes]
  have hP : ∀ q (h : q < (Ed25519RecodeAd.recBytes b.combs (decodeInt (kB c m0))).length), q < 64 →
      NielsV (lookV [rowV b.combs c m0 q, .w (dword (Ed25519RecodeAd.recBytes b.combs (decodeInt (kB c m0)))[q])])
        (combPt b.combs (digitAt b.combs (decodeInt (kB c m0))) q) := fun q h _ => by
    have hb := digitAt_bound b.combs (decodeInt (kB c m0)) q
    have e : (Ed25519RecodeAd.recBytes b.combs (decodeInt (kB c m0)))[q]'h =
        BitVec.ofNat 8 (digitAt b.combs (decodeInt (kB c m0)) q + 8).toNat := by
      simp [Ed25519RecodeAd.recBytes]
    rw [e]
    exact hlk _ (by unfold row; omega) _ hb.2.1 hb.2.2 hb.1
  obtain ⟨hE1, hH1⟩ := runs_val hP (by omega) 64 (Nat.le_refl _) _ _ hE0 hH0
  obtain ⟨x, y, z, t, ho, hr⟩ := epi_val (nc := b.combs) hH1 hodd
  refine ⟨x, y, z, t, ?_, ?_⟩
  · show [runM b.combs c m0 (proR ++ runsR b.combs 64 ++ epiR) _ _] = _
    rw [run_app, run_app, ho]
  · rw [← Ed25519ScalarMul.mulBase_digitAt hnc.1 hnc.2 hk]; exact hr

end

end M0Crypto.Release.Ed25519MulBaseVal
