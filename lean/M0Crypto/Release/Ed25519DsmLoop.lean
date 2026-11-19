import M0Crypto.Release.Ed25519DsmPass

/-!
# The passes of `m0c_ge_dsm`'s loop

A pass from the digits' loads at `dsm_load_digits` to the index step at `dsm_dec_index`, on the four cases of
the digits `a` of `h` and `b` of `s`, then the loop from `I = n − 1` to its exit. Values are
tracked off the glue's words `N` (`PV`): the views agree there with the reference run of the
updates (`passR`, `runsR`), and `I`, `DA`, `DB` hold their words.
-/

namespace M0Crypto.Release.Ed25519DsmLoop

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GlueRun
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519DsmBlocks
open M0Crypto.Release.Ed25519DsmRun
open M0Crypto.Release.Ed25519DsmPass
open M0Crypto.Release.Ed25519DsmVal (dblR cvR saL sbL sgn sgn_lt passR runsR)
open M0Crypto.Release.Ed25519MulBaseVal (frR)
open M0Crypto.Release.Ed25519DecompressOut (keeps run_keep)
open M0Crypto.Artifacts.Ed25519Compact (dsm_a_add dsm_a_branch dsm_a_done dsm_a_index dsm_a_jump_join dsm_a_next_branch dsm_a_p2
  dsm_a_p3 dsm_a_test_next dsm_b_add dsm_b_branch dsm_b_p2 dsm_dbl_jump dsm_dbl_p2 dsm_dbl_p3
  dsm_dec_index dsm_double dsm_load_digits dsm_loop dsm_output dsm_test_a dsm_test_digits)

/-! ## The straight lines at the pass's states -/

/-- The glue's frame words. -/
def N : List Loc := [.fr oI, .fr oDa, .fr oDb, .fr oEp, .fr oEa, .fr oEb, .fr oTz, .fr oTt]

/-- `P` from `S` runs the updates `L` and ends in a state that weakens to `S'`. -/
def segOk (P : Prog DS DB) (S : St) (L : List (ROp DS DB)) (S' : St) : Bool :=
  S.ex.isNone && match P.lin dsS dbS dsGeo S with
    | some (L', S1) => decide (L' = L) && S1.ex.isNone && wkB S1 S'
    | none => false

/-- The updates read no glue word and keep every one. -/
def goodL (L : List (ROp DS DB)) : Bool := L.all (opOff N) && N.all fun l => L.all (keeps l)

theorem seg_facts : segOk segDbl E1 dblR E2 = true ∧ segOk segP3 E2 (cvR true) E3 = true ∧
    segOk segP2 E2 (cvR false) E1 = true ∧ segOk segP3 E3 (cvR true) E3 = true ∧
    segOk segP2 E3 (cvR false) E1 = true ∧
    (∀ k < 2, ∀ s < 2, segOk segSA (ext (saSt k s)) (frR DS.f (saL k s)) E3 = true) ∧
    (∀ k < 8, ∀ s < 2, segOk segSB (ext (sbSt k s)) (frR DS.f (sbL k s)) E3 = true) := by
  decide +kernel

theorem good_facts : goodL dblR = true ∧ goodL (cvR true) = true ∧ goodL (cvR false) = true ∧
    (∀ k < 2, ∀ s < 2, goodL (frR DS.f (saL k s)) = true) ∧ (∀ k < 8, ∀ s < 2, goodL (frR DS.f (sbL k s)) = true) := by
  decide +kernel

theorem seg_mem : (dsm_double, segDbl) ∈ segs ∧ (dsm_dbl_p3, segP3) ∈ segs ∧ (dsm_dbl_p2, segP2) ∈ segs ∧
    (dsm_a_add, segSA) ∈ segs ∧ (dsm_a_p3, segP3) ∈ segs ∧ (dsm_a_p2, segP2) ∈ segs ∧ (dsm_b_add, segSB) ∈ segs ∧
    (dsm_b_p2, segP2) ∈ segs := by
  simp [segs]

theorem seg_size : dsm_double + segDbl.size dsS dbS = dsm_test_digits ∧ dsm_dbl_p3 + segP3.size dsS dbS = dsm_dbl_jump ∧
    dsm_dbl_p2 + segP2.size dsS dbS = dsm_test_a ∧ dsm_a_add + segSA.size dsS dbS = dsm_a_test_next ∧
    dsm_a_p3 + segP3.size dsS dbS = dsm_a_jump_join ∧ dsm_a_p2 + segP2.size dsS dbS = dsm_a_done ∧
    dsm_b_add + segSB.size dsS dbS = dsm_b_p2 ∧ dsm_b_p2 + segP2.size dsS dbS = dsm_dec_index := by
  decide +kernel

/-! ## Values off the glue's words -/

section values
variable {A Bk : Type} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V}
  {c : Ctx} {m0 : Mem}

/-- The views agree off `N` with `R`, and `I`, `DA`, `DB` hold `x`, `a`, `b`. -/
def PV (E R : Loc → V) (x a b : Word) : Prop :=
  Agree N E R ∧ E (.fr oI) = .w x ∧ E (.fr oDa) = .w a ∧ E (.fr oDb) = .w b

theorem PV.run {E R : Loc → V} {x a b : Word} (h : PV E R x a b) {L : List (ROp A Bk)}
    (hL : L.all (opOff N) && N.all (fun l => L.all (keeps l)) = true) :
    PV (runR bE G semA semB c m0 L E) (runR bE G semA semB c m0 L R) x a b := by
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hL
  have hk : ∀ l ∈ N, runR bE G semA semB c m0 L E l = E l := fun l hl => run_keep L E (hL.2 l hl)
  refine ⟨run_agree L h.1 hL.1, ?_, ?_, ?_⟩
  · rw [hk _ (by simp [N])]; exact h.2.1
  · rw [hk _ (by simp [N])]; exact h.2.2.1
  · rw [hk _ (by simp [N])]; exact h.2.2.2

/-- Setting views at glue words other than `I`, `DA`, `DB` keeps `PV`. -/
theorem PV.upd {E R : Loc → V} {x a b : Word} (h : PV E R x a b) {o : List (Loc × Kd)} {vs : List V}
    (hN : ∀ p ∈ o, p.1 ∈ N) (hI : ∀ p ∈ o, p.1 ≠ .fr oI ∧ p.1 ≠ .fr oDa ∧ p.1 ≠ .fr oDb) :
    PV (updOuts E o vs) R x a b := by
  have hk : ∀ l, (∀ p ∈ o, p.1 ≠ l) → updOuts E o vs l = E l := fun l hl =>
    Ed25519DecompressOut.updOuts_nmem o vs fun hm => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hm; exact hl p hp he
  refine ⟨(agree_upd o vs hN).trans h.1, ?_, ?_, ?_⟩
  · rw [hk _ fun p hp => (hI p hp).1]; exact h.2.1
  · rw [hk _ fun p hp => (hI p hp).2.1]; exact h.2.2.1
  · rw [hk _ fun p hp => (hI p hp).2.2]; exact h.2.2.2

end values

theorem ptr_N (ep : Nat → SV) (s : Nat) :
    (∀ p ∈ ptrΓ ep s, p.1 ∈ N) ∧ (∀ p ∈ ptrΓ ep s, p.1 ≠ .fr oI ∧ p.1 ≠ .fr oDa ∧ p.1 ≠ .fr oDb) := by
  simp [ptrΓ, N, oI, oDa, oDb, oEp, oEa, oEb, oTz, oTt]

/-! ## The pass's traces -/

/-- The entry of a digit's table and its sign. -/
def kOf (w : Word) : Nat := w.toInt.natAbs / 2
def saR (a : Word) : List (ROp DS DB) := frR DS.f (saL (kOf a) (sgn a.toInt))
def sbR (b : Word) : List (ROp DS DB) := frR DS.f (sbL (kOf b) (sgn b.toInt))

/-- The updates of `s`'s digit `b`. -/
def tailL (b : Word) : List (ROp DS DB) := if b.toInt = 0 then [] else sbR b ++ cvR false

/-- The updates of `h`'s digit `a`. -/
def headL (a b : Word) : List (ROp DS DB) := if a.toInt = 0 then [] else saR a ++ cvR (b.toInt != 0)

theorem passR_eq (a b : Word) :
    passR a.toInt b.toInt = dblR ++ cvR (a.toInt != 0 || b.toInt != 0) ++ (headL a b ++ tailL b) := by
  simp only [passR, headL, tailL, saR, sbR, kOf, List.append_assoc]

section tr
variable (T : DS → Word → (Nat → Word) → List Event) (c : Ctx)

def pt (P : Prog DS DB) (o : Nat) (S : St) (Ψ : TrP) : TrP := Prog.tr dsS dbS dsGeo T c P o S Ψ [] []

/-- From the second test of `DB` at `dsm_a_done` to the index step. -/
def tDB2 (b : Word) (Ψ : TrP) : TrP :=
  tstTr c dsm_a_done 3 dsm_b_branch dsm_dec_index (b.toInt != 0)
    (pbTr c (pt T c segSB dsm_b_add (ext (sbSt (kOf b) (sgn b.toInt))) (pt T c segP2 dsm_b_p2 E3 Ψ))) Ψ

/-- From the first test of `DB` at `dsm_a_test_next`. -/
def tDB1 (b : Word) (Ψ : TrP) : TrP :=
  tstTr c dsm_a_test_next 3 dsm_a_next_branch dsm_a_p2 (b.toInt != 0)
    (pt T c segP3 dsm_a_p3 E3 (Tr.cat (Tr.is [bEv c dsm_a_jump_join dsm_a_done]) (tDB2 T c b Ψ))) (pt T c segP2 dsm_a_p2 E3 (tDB2 T c b Ψ))

/-- From the test of `DA` at `dsm_test_a`. -/
def tDA (a b : Word) (Ψ : TrP) : TrP :=
  tstTr c dsm_test_a 2 dsm_a_branch dsm_a_done (a.toInt != 0)
    (Tr.cat (Tr.is (blockTrE (headA ++ tailG 2) (c.base + BitVec.ofNat 32 dsm_a_index) [.reg0 13] [dsGeo.fsp c]))
      (pt T c segSA dsm_a_add (ext (saSt (kOf a) (sgn a.toInt))) (tDB1 T c b Ψ))) (tDB2 T c b Ψ)

/-- From the doubling at `dsm_double`. -/
def restTr (a b : Word) (Ψ : TrP) : TrP :=
  pt T c segDbl dsm_double E1 (orTr c (a.toInt != 0 || b.toInt != 0)
    (pt T c segP3 dsm_dbl_p3 E2 (Tr.cat (Tr.is [bEv c dsm_dbl_jump dsm_test_a]) (tDA T c a b Ψ))) (pt T c segP2 dsm_dbl_p2 E2 (tDA T c a b Ψ)))

/-- **The loop's trace** from the test at `dsm_loop` with `n` passes left (`I = n − 1`), then `Ψx`
after the exit; `da i`, `db i` are the digit words at `i`. -/
def lpTr (da db : Nat → Word) (Ψx : TrP) : Nat → TrP
  | 0 => loopTr c (decide (0 ≤ (BitVec.ofNat 32 0 - 1#32).toInt)) (Tr.is []) Ψx
  | n + 1 => loopTr c (decide (0 ≤ (BitVec.ofNat 32 (n + 1) - 1#32).toInt))
      (digTr c n (restTr T c (da n) (db n) (decTr c (lpTr da db Ψx n)))) Ψx

end tr

theorem small (n : Nat) (h : n ≤ 256) :
    (BitVec.ofNat 32 (n + 1) - 1#32) = BitVec.ofNat 32 n ∧ (BitVec.ofNat 32 n).toNat = n ∧
      0 ≤ (BitVec.ofNat 32 n).toInt := by
  have e : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)
  refine ⟨?_, e, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e]
    simp only [Nat.reducePow]
    omega
  · rw [BitVec.toInt_eq_toNat_cond, e]
    split <;> simp only [Nat.reducePow] at * <;> omega

/-! ## The pass -/

/-- The values after updates, with the callees' and blocks' semantics. -/
abbrev runA {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (ads : ∀ a, Ad Rs B BS (dsS a))
    (bds : ∀ b, Bd Rs (dbS b)) (c : Ctx) (m0 : Mem) (L : List (ROp DS DB)) (E : Loc → V) : Loc → V :=
  runR dbS dsGeo (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 L E

theorem runA_app {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (ads : ∀ a, Ad Rs B BS (dsS a))
    (bds : ∀ b, Bd Rs (dbS b)) (c : Ctx) (m0 : Mem) (L L' : List (ROp DS DB)) (E : Loc → V) :
    runA ads bds c m0 (L ++ L') E = runA ads bds c m0 L' (runA ads bds c m0 L E) :=
  runR_append _ _ _ _ _ _ L L' E

/-- The callees' traces. -/
abbrev TA {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (ads : ∀ a, Ad Rs B BS (dsS a)) :
    DS → Word → (Nat → Word) → List Event := fun a => (ads a).T

section run
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {Wc Rc : List Rgn} (m0 : Mem)
variable (ads : ∀ a, Ad Rs B BS (dsS a)) (bds : ∀ b, Bd Rs (dbS b))


/-- **A straight line** of the pass, carrying the values off the glue's words. -/
theorem seg_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (hcR : Sub [codeR c.base] Rc)
    (cd : Code B BS) {P : Prog DS DB} {o : Nat} (hP : (o, P) ∈ segs) {S S' : St} {L : List (ROp DS DB)}
    (hs : segOk P S L S' = true) (hL : goodL L = true) {E R : Loc → V} {x a b : Word} (hpv : PV E R x a b)
    {t : State} {Q : State → Prop} {Ψ : TrP} (hat : At Rs B c dsGeo m0 o S E t)
    (k : ∀ E' u, PV E' (runA ads bds c m0 L R) x a b → At Rs B c dsGeo m0 (o + P.size dsS dbS) S' E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (pt (TA ads) c P o S Ψ) := by
  unfold segOk at hs
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
  obtain ⟨hex, hs⟩ := hs
  split at hs
  · rename_i L' S1 hlin
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hs
    obtain ⟨⟨rfl, hex1⟩, hw⟩ := hs
    exact seg_run Rs m0 ads bds g F hcR cd hP hlin hex hex1 hw hat fun u hu => k _ u (hpv.run hL) hu
  · exact absurd hs (by simp)

variable (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (hcR : Sub [codeR c.base] Rc)
  (cd : Code B BS) (cl : CodeL B BS)
include g F hcR cd cl

/-- **The second test of `DB`** at `dsm_a_done`: for `b ≠ 0` `DB`'s pointers, `signed_add` over
`odd_b` and the conversion without `T`, then on to the index step. -/
theorem db2_go {S : St} {E R : Loc → V} {x a b : Word} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hS : S = E1 ∧ b.toInt = 0 ∨ S = E3) (hkb : b.toInt ≠ 0 → kOf b < 8) (hpv : PV E R x a b)
    (hat : At Rs B c dsGeo m0 dsm_a_done S E t)
    (k : ∀ E' u, PV E' (runA ads bds c m0 (tailL b) R) x a b → At Rs B c dsGeo m0 dsm_dec_index E1 E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (tDB2 (TA ads) c b Ψ) := by
  have hf := ext_facts S (by rcases hS with ⟨rfl, -⟩ | rfl <;> simp)
  unfold tDB2
  refine tst_go Rs m0 g F (ds := 3) tst_ok.2.2.2.2.1 tst_ok.2.2.2.2.2.2 glue_ok.2.2.2.2 (by decide) cl.tb2 rfl
    cl.brB2 ⟨hf.1, hf.2.1⟩ hf.2.2.2.1 hpv.2.2.2 hat (fun hb u hu => ?_) (fun hb u hu => ?_)
  · have hS3 : S = E3 := hS.resolve_left fun h => hb h.2
    subst hS3
    have hk := hkb hb
    refine ptrB_go Rs m0 ads g F hcR cl hk hpv.2.2.2 hu (fun u2 hu2 => ?_)
    refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.2.2.2.2.1 (seg_facts.2.2.2.2.2.2 _ hk _ (sgn_lt _))
      (good_facts.2.2.2.2 _ hk _ (sgn_lt _)) (hpv.upd (ptr_N _ _).1 (ptr_N _ _).2) hu2 (fun E3' u3 hpv3 hu3 => ?_)
    rw [seg_size.2.2.2.2.2.2.1] at hu3
    refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.2.2.2.2.2 seg_facts.2.2.2.2.1 good_facts.2.2.1 hpv3 hu3
      (fun E4 u4 hpv4 hu4 => k E4 u4 ?_ (by rwa [seg_size.2.2.2.2.2.2.2] at hu4))
    have e : tailL b = sbR b ++ cvR false := by simp [tailL, hb]
    rw [e, runA_app]; exact hpv4
  · have e : tailL b = [] := by simp [tailL, hb]
    refine k E u (by rw [e]; exact hpv) (at_wk Rs m0 hu ?_)
    rcases hS with ⟨rfl, -⟩ | rfl <;> decide

/-- **The first test of `DB`** at `dsm_a_test_next`, after `signed_add` over `AI`: for `b ≠ 0` the conversion
with `T` and on to the second test, else the conversion without. -/
theorem db1_go {E R : Loc → V} {x a b : Word} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hkb : b.toInt ≠ 0 → kOf b < 8) (hpv : PV E R x a b) (hat : At Rs B c dsGeo m0 dsm_a_test_next E3 E t)
    (k : ∀ E' u, PV E' (runA ads bds c m0 (cvR (b.toInt != 0) ++ tailL b) R) x a b → At Rs B c dsGeo m0 dsm_dec_index E1 E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (tDB1 (TA ads) c b Ψ) := by
  have hf := ext_facts E3 (by simp)
  unfold tDB1
  refine tst_go Rs m0 g F (ds := 3) tst_ok.2.2.2.1 tst_ok.2.2.2.2.2.2 glue_ok.2.2.2.2 (by decide) cl.tb1 rfl
    cl.brB1 ⟨hf.1, hf.2.1⟩ hf.2.2.2.1 hpv.2.2.2 hat (fun hb u hu => ?_) (fun hb u hu => ?_)
  · refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.2.2.1 seg_facts.2.2.2.1 good_facts.2.1 hpv hu
      (fun E2' u2 hpv2 hu2 => ?_)
    rw [seg_size.2.2.2.2.1] at hu2
    refine jmp_run Rs m0 g F cl.bj2 cl.j2 hu2 fun hu3 => ?_
    refine db2_go Rs m0 ads bds g F hcR cd cl (.inr rfl) hkb hpv2 hu3 (fun E' u' hpv' hu' => k E' u' ?_ hu')
    rw [show (b.toInt != 0) = true by simpa using hb, runA_app]; exact hpv'
  · refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.2.2.2.1 seg_facts.2.2.2.2.1 good_facts.2.2.1 hpv hu
      (fun E2' u2 hpv2 hu2 => ?_)
    rw [seg_size.2.2.2.2.2.1] at hu2
    refine db2_go Rs m0 ads bds g F hcR cd cl (.inl ⟨rfl, hb⟩) hkb hpv2 hu2 (fun E' u' hpv' hu' => k E' u' ?_ hu')
    rw [show (b.toInt != 0) = false by simpa using hb, runA_app]; exact hpv'

/-- **The test of `DA`** at `dsm_test_a`: for `a ≠ 0` `DA`'s pointers and `signed_add` over `AI`, then
the tests of `DB`. -/
theorem da_go {S : St} {E R : Loc → V} {x a b : Word} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hS : S = E1 ∧ a.toInt = 0 ∧ b.toInt = 0 ∨ S = E3) (hka : a.toInt ≠ 0 → kOf a < 2)
    (hkb : b.toInt ≠ 0 → kOf b < 8) (hpv : PV E R x a b) (hat : At Rs B c dsGeo m0 dsm_test_a S E t)
    (k : ∀ E' u, PV E' (runA ads bds c m0 (headL a b ++ tailL b) R) x a b → At Rs B c dsGeo m0 dsm_dec_index E1 E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (tDA (TA ads) c a b Ψ) := by
  have hf := ext_facts S (by rcases hS with ⟨rfl, -⟩ | rfl <;> simp)
  unfold tDA
  refine tst_go Rs m0 g F (ds := 2) tst_ok.2.2.1 tst_ok.2.2.2.2.2.1 glue_ok.2.2.2.1 (by decide) cl.ta rfl
    cl.brA ⟨hf.1, hf.2.1⟩ hf.2.2.1 hpv.2.2.1 hat (fun ha u hu => ?_) (fun ha u hu => ?_)
  · have hS3 : S = E3 := hS.resolve_left fun h => ha h.2.1
    subst hS3
    have hk := hka ha
    refine ptrA_go Rs m0 g F cl hk hpv.2.2.1 hu (fun u2 hu2 => ?_)
    refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.2.1 (seg_facts.2.2.2.2.2.1 _ hk _ (sgn_lt _))
      (good_facts.2.2.2.1 _ hk _ (sgn_lt _)) (hpv.upd (ptr_N _ _).1 (ptr_N _ _).2) hu2 (fun E3' u3 hpv3 hu3 => ?_)
    rw [seg_size.2.2.2.1] at hu3
    refine db1_go Rs m0 ads bds g F hcR cd cl hkb hpv3 hu3 (fun E' u' hpv' hu' => k E' u' ?_ hu')
    have e : headL a b = saR a ++ cvR (b.toInt != 0) := by simp [headL, ha]
    rw [e, List.append_assoc, runA_app]; exact hpv'
  · have hS' : S = E1 ∧ b.toInt = 0 ∨ S = E3 := hS.imp (fun h => ⟨h.1, h.2.2⟩) id
    refine db2_go Rs m0 ads bds g F hcR cd cl hS' hkb hpv hu (fun E' u' hpv' hu' => k E' u' ?_ hu')
    have e : headL a b = [] := by simp [headL, ha]
    rw [e, List.nil_append]; exact hpv'

/-- **From the doubling** at `dsm_double` to the index step, with the digit words `a`, `b`: the
updates `passR`. -/
theorem rest_go {E R : Loc → V} {x a b : Word} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hka : a.toInt ≠ 0 → kOf a < 2) (hkb : b.toInt ≠ 0 → kOf b < 8) (hpv : PV E R x a b)
    (hat : At Rs B c dsGeo m0 dsm_double E1 E t)
    (k : ∀ E' u, PV E' (runA ads bds c m0 (passR a.toInt b.toInt) R) x a b → At Rs B c dsGeo m0 dsm_dec_index E1 E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (restTr (TA ads) c a b Ψ) := by
  unfold restTr
  refine seg_go Rs m0 ads bds g F hcR cd seg_mem.1 seg_facts.1 good_facts.1 hpv hat (fun E2' u2 hpv2 hu2 => ?_)
  rw [seg_size.1] at hu2
  refine or_go Rs m0 g F cl hpv2.2.2.1 hpv2.2.2.2 hu2 (fun hd u hu => ?_) (fun hd u hu => ?_)
  · refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.1 seg_facts.2.1 good_facts.2.1 hpv2 hu
      (fun E3' u3 hpv3 hu3 => ?_)
    rw [seg_size.2.1] at hu3
    refine jmp_run Rs m0 g F cl.bj1 cl.j1 hu3 fun hu4 => ?_
    refine da_go Rs m0 ads bds g F hcR cd cl (.inr rfl) hka hkb hpv3 hu4 (fun E' u' hpv' hu' => k E' u' ?_ hu')
    rw [passR_eq, hd, List.append_assoc, runA_app, runA_app]; exact hpv'
  · refine seg_go Rs m0 ads bds g F hcR cd seg_mem.2.2.1 seg_facts.2.2.1 good_facts.2.2.1 hpv2 hu
      (fun E3' u3 hpv3 hu3 => ?_)
    rw [seg_size.2.2.1] at hu3
    refine da_go Rs m0 ads bds g F hcR cd cl (.inl ⟨rfl, hd⟩) hka hkb hpv3 hu3 (fun E' u' hpv' hu' => k E' u' ?_ hu')
    have e : (a.toInt != 0 || b.toInt != 0) = false := by simp [hd.1, hd.2]
    rw [passR_eq, e, List.append_assoc, runA_app, runA_app]; exact hpv'

/-- **The loop** from its test at `dsm_loop` with `n` passes left: to `segEnd` at `dsm_output` with the
updates of the passes `n − 1, …, 0` (`runsR`) off the glue's words. -/
theorem loop_go (hka : ∀ i < 256, (dv m0 c 2 i).toInt ≠ 0 → kOf (dv m0 c 2 i) < 2)
    (hkb : ∀ i < 256, (dv m0 c 1 i).toInt ≠ 0 → kOf (dv m0 c 1 i) < 8) {Q : State → Prop} {Ψx : TrP} :
    ∀ n, n ≤ 256 → ∀ (E R : Loc → V) (t : State), Agree N E R → E (.fr oI) = .w (BitVec.ofNat 32 n - 1#32) →
      At Rs B c dsGeo m0 dsm_loop LH E t →
      (∀ E' u, Agree N E' (runA ads bds c m0 (runsR (fun i => (dv m0 c 2 i).toInt) (fun i => (dv m0 c 1 i).toInt) n) R) →
        At Rs B c dsGeo m0 dsm_output LH E' u →
        ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψx) →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
        (lpTr (TA ads) c (dv m0 c 2) (dv m0 c 1) Ψx n)
  | 0, _, E, R, t, hA, hx, hat, k => by
    rw [lpTr]
    exact loop_tst Rs m0 g F cl hat hx (fun h => absurd h (by decide)) (fun _ u hu => k E u hA hu)
  | n + 1, hn, E, R, t, hA, hx, hat, k => by
    rw [lpTr]
    obtain ⟨hxn, hnn, hn0⟩ := small n (by omega)
    refine loop_tst Rs m0 g F cl hat hx (fun _ u hu => ?_) (fun h => absurd h (by rw [hxn]; omega))
    rw [hxn, hnn] at hu
    refine dig_go Rs m0 g F cl (by omega) hu (fun u2 hu2 => ?_)
    have hpv : PV (updOuts E Wd [.w (dv m0 c 2 n), .w (dv m0 c 1 n)]) R (BitVec.ofNat 32 (n + 1) - 1#32)
        (dv m0 c 2 n) (dv m0 c 1 n) :=
      ⟨(agree_upd Wd _ (by simp [Wd, N])).trans hA, by simpa [updOuts, Wd, oI, oDa, oDb] using hx,
        by simp [updOuts, Wd], by simp [updOuts, Wd, oDa, oDb]⟩
    refine rest_go Rs m0 ads bds g F hcR cd cl (hka n (by omega)) (hkb n (by omega)) hpv hu2
      (fun E' u3 hpv3 hu3 => ?_)
    refine dec_go Rs m0 g F cl hpv3.2.1 hu3 (fun u4 hu4 => ?_)
    refine loop_go hka hkb n (by omega) _ _ u4 ((agree_upd [(.fr oI, .cw)] _ (by simp [N])).trans hpv3.1)
      (by simp [updOuts, hxn]) hu4 (fun E'' u5 hA5 hu5 => k E'' u5 ?_ hu5)
    rw [runsR, runA_app]; exact hA5

end run

end M0Crypto.Release.Ed25519DsmLoop
