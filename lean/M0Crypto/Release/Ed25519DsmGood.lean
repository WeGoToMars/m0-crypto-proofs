import M0Crypto.Release.Ed25519DsmAd

/-!
# `m0c_ge_dsm`: the body's effect

The body's trace `ΨD` keeps the call program's invariant `BI` from the entry state to `Send`, at
any digit words whose halves index the tables (`hka`, `hkb`): the straight lines by `prog_good`
(their decided effects), the glue by `glue_gp` (decided frame regions; the digit bytes in the
digit buffers), the table's literal by `bufEv_gp`, the branches by `quiet_gp`.
-/

namespace M0Crypto.Release.Ed25519DsmGood

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Sym (SExpr)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GlueRun
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519DsmBlocks
open M0Crypto.Release.Ed25519DsmRun
open M0Crypto.Release.Ed25519DsmPass
open M0Crypto.Release.Ed25519DsmLoop
open M0Crypto.Release.Ed25519DsmBody
open M0Crypto.Release.Ed25519DsmVal (sgn sgn_lt)
open M0Crypto.Release.Ed25519DsmAd

/-! ## Decided facts -/

/-- The straight lines' effects at their entry states. -/
theorem eok_facts : segPre.eok dsS dbS dsGeo stE = true ∧ segId.eok dsS dbS dsGeo SI = true ∧
    segEnd.eok dsS dbS dsGeo LH = true ∧ segDbl.eok dsS dbS dsGeo E1 = true ∧
    segP3.eok dsS dbS dsGeo E2 = true ∧ segP2.eok dsS dbS dsGeo E2 = true ∧
    segP3.eok dsS dbS dsGeo E3 = true ∧ segP2.eok dsS dbS dsGeo E3 = true ∧
    (∀ k < 2, ∀ s < 2, segSA.eok dsS dbS dsGeo (ext (saSt k s)) = true) ∧
    (∀ k < 8, ∀ s < 2, segSB.eok dsS dbS dsGeo (ext (sbSt k s)) = true) := by
  decide +kernel

/-- The frame and the digits' reads of the scan and of the digits. -/
def digIni : List (SExpr × Nat) := [(spW oSp, 4), (spW oHp, 4), (bA oHp, 1), (bA oSp, 1)]
def digFp : List (SExpr × Nat) := [frR dsGeo, (bA oHp, 1), (bA oSp, 1)]
def spI : List (SExpr × Nat) := [(spW oI, 4)]
def spA : List (SExpr × Nat) := [(spW oDa, 4)]
def spB : List (SExpr × Nat) := [(spW oDb, 4)]
abbrev sp0R : List SExpr := [.reg0 13]

/-- **The glue's decided effects and frame regions.** -/
theorem glue_facts :
    blkChk [] [] [] [.movImm 0 255] = true ∧ blkChk [] [] [] [.subImm8 0 1] = true ∧
    blkChk [] spI [frR dsGeo] [.strSp 0 1] = true ∧ frChk dsGeo.top s0.Γ SI.Γ sp0R [] spI [frR dsGeo] = true ∧
    blkChk digIni [] digFp scanG = true ∧ frChk dsGeo.top s0.Γ s0.Γ scanAs digIni [] digFp = true ∧
    blkChk spI [] [frR dsGeo] loopG = true ∧ frChk dsGeo.top LH.Γ LH.Γ sp0R spI [] [frR dsGeo] = true ∧
    blkChk digIni digWg digFp digG = true ∧ frChk dsGeo.top LH.Γ E1.Γ scanAs digIni digWg digFp = true ∧
    blkChk (spA ++ spB) [] [frR dsGeo] orG = true ∧ frChk dsGeo.top E2.Γ E2.Γ sp0R (spA ++ spB) [] [frR dsGeo] = true ∧
    blkChk spA [] [frR dsGeo] (tstG 2) = true ∧ blkChk spB [] [frR dsGeo] (tstG 3) = true ∧
    (∀ S ∈ [E1, E3], frChk dsGeo.top S.Γ S.Γ sp0R spA [] [frR dsGeo] = true ∧
      frChk dsGeo.top S.Γ S.Γ sp0R spB [] [frR dsGeo] = true ∧
      frChk dsGeo.top S.Γ LH.Γ sp0R spI spI [frR dsGeo] = true) ∧
    blkChk spA ptrWg [frR dsGeo] (headA ++ tailG 2) = true ∧
    (∀ k < 2, ∀ s < 2, frChk dsGeo.top E3.Γ (ext (saSt k s)).Γ sp0R spA ptrWg [frR dsGeo] = true) ∧
    blkChk spB [] [frR dsGeo] headB1 = true ∧ frChk dsGeo.top E3.Γ E3.Γ sp0R spB [] [frR dsGeo] = true ∧
    blkChk (pwIni E3.Γ) [] [frR dsGeo] [.addPc 1] = true ∧ blkChk spB ptrWg [frR dsGeo] tailB = true ∧
    (∀ k < 8, ∀ s < 2, frChk dsGeo.top E3.Γ (ext (sbSt k s)).Γ sp0R spB ptrWg [frR dsGeo] = true) ∧
    blkChk spI spI [frR dsGeo] decG = true := by
  decide +kernel

/-- The digit buffers and the atoms of the scan's and the digits' glue. -/
theorem buf_facts : (⟨.ex 1 0, .k 256⟩ : SR).ok dsGeo = true ∧ (⟨.ex 1 0, .k 256⟩ : SR).acc dsGeo false = true ∧
    (⟨.ex 2 0, .k 256⟩ : SR).ok dsGeo = true ∧ (⟨.ex 2 0, .k 256⟩ : SR).acc dsGeo false = true ∧
    atomOf scanAs (bA oHp) = some (1, 0#32) ∧ atomOf scanAs (bA oSp) = some (2, 0#32) ∧
    spOf scanAs (spW oSp, 4) = some (oSp, 4) ∧ spOf scanAs (spW oHp, 4) = some (oHp, 4) ∧
    spOf scanAs (frR dsGeo) = some (0, dsGeo.top) := by
  decide +kernel

theorem bne_t {x : Int} (h : (x != 0) = true) : x ≠ 0 := by simpa using h
theorem bne_f {x : Int} (h : (x != 0) = false) : x = 0 := by simpa using h

theorem nOf_le {j : Nat} (h : j ≤ 255 ∨ j = 2 ^ 32 - 1) : nOf j ≤ 256 := by
  unfold nOf; split <;> omega

/-! ## The body's invariant along its trace -/

section gp
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {T : DS → Word → (Nat → Word) → List Event}
  {c : Ctx} {sp0 : Word} {n : Nat} {X0 : Word → Prop} (fm : Frm c dsGeo sp0 n X0)
  (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (dsGeo.fsp c) y ∧ X0 y)
include fm hcode

/-- A glue block on frame words. -/
theorem fr_gp {S S' : St} {g : List Instr} {ini wo fp : List (SExpr × Nat)} (hk : blkChk ini wo fp g = true)
    (hf : frChk dsGeo.top S.Γ S'.Γ sp0R ini wo fp = true)
    (hs : (ini ++ fp).all (fun r => (spOf sp0R r).isSome) = true) (pc : Word) :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (Tr.is (blockTrE g pc sp0R [dsGeo.fsp c])) (BI c dsGeo sp0 n X0 S') :=
  glue_gp fm hcode hk rfl rfl hf
    (fun r hr h => absurd h (Option.isSome_iff_ne_none.mp (List.all_eq_true.mp hs r (List.mem_append_left _ hr))))
    (fun r hr h => absurd h (Option.isSome_iff_ne_none.mp (List.all_eq_true.mp hs r (List.mem_append_right _ hr))))

/-- A block without accesses. -/
theorem nil_gp {S : St} {g : List Instr} (hk : blkChk [] [] [] g = true) (pc : Word) :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (Tr.is (blockTrE g pc [] [])) (BI c dsGeo sp0 n X0 S) :=
  bufBlk_gp fm hcode hk (fun _ ⟨_, h, _⟩ => absurd h List.not_mem_nil)
    (fun _ ⟨_, h, _⟩ => absurd h List.not_mem_nil) fun _ h => .inl h

omit fm hcode in
theorem buf_has {i j : Nat} {y : Word} (hj : j < 256) (h : Region (c.ptr i + BitVec.ofNat 32 j + 0#32) 1 y) :
    Has (SR.rgns dsGeo c ⟨.ex i 0, .k 256⟩) y := by
  have e : SR.rgns dsGeo c ⟨.ex i 0, .k 256⟩ = [⟨c.ptr i + BitVec.ofNat 32 0, 256⟩] := by
    simp [SR.rgns, XLen.v, Loc.addr]
  rw [e]
  exact ⟨_, List.mem_singleton_self _, Rgn.of_region (by simp only [Region] at *; bv_omega)⟩

/-- **The scan's and the digits' glue**: frame words and the digit bytes at `j`. -/
theorem dg_gp {S S' : St} {g : List Instr} {wo : List (SExpr × Nat)} (hk : blkChk digIni wo digFp g = true)
    (hf : frChk dsGeo.top S.Γ S'.Γ scanAs digIni wo digFp = true) {j : Nat} (hj : j < 256) (pc : Word) :
    GP sp0 n (BI c dsGeo sp0 n X0 S)
      (Tr.is (blockTrE g pc scanAs [dsGeo.fsp c, c.ptr 2 + BitVec.ofNat 32 j, c.ptr 1 + BitVec.ofNat 32 j]))
      (BI c dsGeo sp0 n X0 S') := by
  obtain ⟨o1, a1, o2, a2, t2, t1, s1, s2, s3⟩ := buf_facts
  refine glue_gp fm hcode hk rfl rfl hf (fun r hr hs y hy => ?_) fun r hr hs y hy => ?_
  · simp only [digIni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [s1] at hs; cases hs
    · rw [s2] at hs; cases hs
    · exact .inr (.inl ⟨_, o2, rfl, a2, buf_has hj (inRD_atom1 rfl t2 rfl hy)⟩)
    · exact .inr (.inl ⟨_, o1, rfl, a1, buf_has hj (inRD_atom1 rfl t1 rfl hy)⟩)
  · simp only [digFp, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [s3] at hs; cases hs
    · exact .inr (.inl ⟨_, o2, buf_has hj (inRD_atom1 rfl t2 rfl hy)⟩)
    · exact .inr (.inl ⟨_, o1, buf_has hj (inRD_atom1 rfl t1 rfl hy)⟩)

/-- A test on a frame word: on `d` to `Ψc`, else past the branch to `Ψx`. -/
theorem tst_gp {S : St} {o ds ob T' : Nat} {d : Bool} {ini : List (SExpr × Nat)} {Ψc Ψx : TrP} {J : Ef → Prop}
    (hk : blkChk ini [] [frR dsGeo] (tstG ds) = true) (hf : frChk dsGeo.top S.Γ S.Γ sp0R ini [] [frR dsGeo] = true)
    (hs : (ini ++ [frR dsGeo]).all (fun r => (spOf sp0R r).isSome) = true)
    (hc : d = true → GP sp0 n (BI c dsGeo sp0 n X0 S) Ψc J)
    (hx : d = false → GP sp0 n (BI c dsGeo sp0 n X0 S) Ψx J) :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (tstTr c o ds ob T' d Ψc Ψx) J :=
  GP.cat (fr_gp fm hcode hk hf hs _)
    (GP.cat (quiet_gp rfl rfl rfl) (GP.cond hc fun h => GP.cat (quiet_gp rfl rfl rfl) (hx h)))

/-- **A straight line** by its decided static run and effect. -/
theorem pt_gp (hT : ∀ a base p, (dsS a).Eff p base (T a base p)) (cd : Code B BS) {P : Prog DS DB} {o : Nat}
    (hm : (o, P) ∈ segs) {S S' : St} {L : List (ROp DS DB)} (hs : segOk P S L S' = true)
    (he : P.eok dsS dbS dsGeo S = true) {Ψ : TrP} {J : Ef → Prop}
    (hΨ : GP sp0 n (BI c dsGeo sp0 n X0 S') Ψ J) :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (pt T c P o S Ψ) J := by
  unfold segOk at hs
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
  obtain ⟨hex, hs⟩ := hs
  split at hs
  · next L' S1 hl =>
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
    obtain ⟨⟨-, hx1⟩, hw⟩ := hs
    have hty := (Prog.lin_ev dsS dbS dsGeo (fun _ => id) (fun _ => id) c (fun _ => 0) P S L' S1 hl).1
    have hsub : ∀ p ∈ S'.Γ, p ∈ S1.Γ := by
      unfold wkB at hw
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hw
      exact hw.1.1.1
    exact prog_good fm hT hcode P o S S1 Ψ J [] [] hty hex he (List.all_eq_true.mp cd.bok _ hm)
      (fun _ => GP.pre (fun _ hq => BI.sub hsub hq) hΨ) fun l hl => by rw [hx1] at hl; cases hl
  · cases hs

/-- **The table's literal** at `0x2c44`: a code word. -/
theorem lit_gp (cl : CodeL B BS) {S : St} :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (Tr.is [⟨c.base + BitVec.ofNat 32 0x2c44, .ldrLit 1 (BitVec.ofNat 8 48),
      [⟨.read, c.base + BitVec.ofNat 32 (litOff 0x2c44 (BitVec.ofNat 8 48)), 4⟩]⟩]) (BI c dsGeo sp0 n X0 S) := by
  have hb := cl.lb
  simp only [ldB, Op.bok, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hlit, -⟩, -⟩, -⟩ := hb
  simp only [litOk, Bool.and_eq_true, decide_eq_true_eq] at hlit
  have hcd : ∀ y, Reads [⟨.read, c.base + BitVec.ofNat 32 (litOff 0x2c44 (BitVec.ofNat 8 48)), 4⟩] y →
      Has [@codeR B BS _ c.base] y := by
    rintro y ⟨_, ha, -, k, hk, rfl⟩
    rw [List.mem_singleton] at ha; subst ha
    exact ⟨_, List.mem_singleton_self _, Rgn.of_region (lit_in hk hlit.1.1.2 CodeBytes.lt)⟩
  refine bufEv_gp fm hcode (by simp [spExact, Instr.dsts]) rfl (fun y hy => .inr (.inr (hcd y hy)))
    fun y hy => .inr (.inr ?_)
  rcases hy with hy | ⟨_, ha, hk, -⟩
  · exact hcd y hy
  · rw [List.mem_singleton] at ha; subst ha; cases hk

variable (hT : ∀ a base p, (dsS a).Eff p base (T a base p)) (cd : Code B BS) (cl : CodeL B BS)
  {Ψ : TrP} {J : Ef → Prop} (hΨ : ∀ S, S = E1 ∨ S = E3 → GP sp0 n (BI c dsGeo sp0 n X0 S) Ψ J)
include hT cd cl hΨ

/-- From the second test of `DB`. -/
theorem db2_gp {b : Word} (hkb : b.toInt ≠ 0 → Ed25519DsmLoop.kOf b < 8) {S : St} (hS : S = E1 ∧ b.toInt = 0 ∨ S = E3) :
    GP sp0 n (BI c dsGeo sp0 n X0 S) (tDB2 T c b Ψ) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, g14, g15, -, -, g18, g19, g20, g21, g22, -⟩ := glue_facts
  obtain ⟨-, -, -, -, -, -, -, e8, -, e10⟩ := eok_facts
  have hf := g15 S (by rcases hS with ⟨rfl, -⟩ | rfl <;> simp)
  unfold tDB2
  refine tst_gp fm hcode g14 hf.2.1 (by decide) (fun hb => ?_) fun _ => hΨ S (hS.imp And.left id)
  obtain rfl : S = E3 := hS.resolve_left fun h => bne_t hb h.2
  have hk := hkb (bne_t hb)
  unfold pbTr
  refine GP.cat (fr_gp fm hcode g18 g19 (by decide) _) (GP.cat (lit_gp fm hcode cl)
    (GP.cat (pubBlk_gp fm g20 _) (GP.cat (fr_gp fm hcode g21 (g22 _ hk _ (sgn_lt b.toInt)) (by decide) _) ?_)))
  exact pt_gp fm hcode hT cd seg_mem.2.2.2.2.2.2.1 (seg_facts.2.2.2.2.2.2 _ hk _ (sgn_lt b.toInt)) (e10 _ hk _ (sgn_lt b.toInt))
    (pt_gp fm hcode hT cd seg_mem.2.2.2.2.2.2.2 seg_facts.2.2.2.2.1 e8 (hΨ E1 (.inl rfl)))

/-- From the first test of `DB`. -/
theorem db1_gp {b : Word} (hkb : b.toInt ≠ 0 → Ed25519DsmLoop.kOf b < 8) : GP sp0 n (BI c dsGeo sp0 n X0 E3) (tDB1 T c b Ψ) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, g14, g15, -⟩ := glue_facts
  obtain ⟨-, -, -, -, -, -, e7, e8, -⟩ := eok_facts
  unfold tDB1
  refine tst_gp fm hcode g14 (g15 E3 (by simp)).2.1 (by decide) (fun _ => ?_) fun hb => ?_
  · exact pt_gp fm hcode hT cd seg_mem.2.2.2.2.1 seg_facts.2.2.2.1 e7
      (GP.cat (quiet_gp rfl rfl rfl) (db2_gp fm hcode hT cd cl hΨ hkb (.inr rfl)))
  · exact pt_gp fm hcode hT cd seg_mem.2.2.2.2.2.1 seg_facts.2.2.2.2.1 e8
      (db2_gp fm hcode hT cd cl hΨ hkb (.inl ⟨rfl, bne_f hb⟩))

/-- From the test of `DA`. -/
theorem da_gp {a b : Word} (hka : a.toInt ≠ 0 → Ed25519DsmLoop.kOf a < 2) (hkb : b.toInt ≠ 0 → Ed25519DsmLoop.kOf b < 8) {S : St}
    (hS : S = E1 ∧ a.toInt = 0 ∧ b.toInt = 0 ∨ S = E3) : GP sp0 n (BI c dsGeo sp0 n X0 S) (tDA T c a b Ψ) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, g13, -, g15, g16, g17, -⟩ := glue_facts
  obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := eok_facts
  have hf := g15 S (by rcases hS with ⟨rfl, -⟩ | rfl <;> simp)
  unfold tDA
  refine tst_gp fm hcode g13 hf.1 (by decide) (fun ha => ?_)
    fun _ => db2_gp fm hcode hT cd cl hΨ hkb (hS.imp (fun h => ⟨h.1, h.2.2⟩) id)
  obtain rfl : S = E3 := hS.resolve_left fun h => bne_t ha h.2.1
  have hk := hka (bne_t ha)
  exact GP.cat (fr_gp fm hcode g16 (g17 _ hk _ (sgn_lt a.toInt)) (by decide) _)
    (pt_gp fm hcode hT cd seg_mem.2.2.2.1 (seg_facts.2.2.2.2.2.1 _ hk _ (sgn_lt a.toInt)) (e9 _ hk _ (sgn_lt a.toInt))
      (db1_gp fm hcode hT cd cl hΨ hkb))

/-- **From the doubling** to the index step. -/
theorem rest_gp {a b : Word} (hka : a.toInt ≠ 0 → Ed25519DsmLoop.kOf a < 2) (hkb : b.toInt ≠ 0 → Ed25519DsmLoop.kOf b < 8) :
    GP sp0 n (BI c dsGeo sp0 n X0 E1) (restTr T c a b Ψ) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g11, g12, -⟩ := glue_facts
  obtain ⟨-, -, -, e4, e5, e6, -⟩ := eok_facts
  unfold restTr
  refine pt_gp fm hcode hT cd seg_mem.1 seg_facts.1 e4 ?_
  unfold orTr
  refine GP.cat (fr_gp fm hcode g11 g12 (by decide) _) (GP.cat (quiet_gp rfl rfl rfl)
    (GP.cond (fun _ => ?_) fun h => GP.cat (quiet_gp rfl rfl rfl) ?_))
  · exact pt_gp fm hcode hT cd seg_mem.2.1 seg_facts.2.1 e5
      (GP.cat (quiet_gp rfl rfl rfl) (da_gp fm hcode hT cd cl hΨ hka hkb (.inr rfl)))
  · simp only [Bool.or_eq_false_iff] at h
    exact pt_gp fm hcode hT cd seg_mem.2.2.1 seg_facts.2.2.1 e6
      (da_gp fm hcode hT cd cl hΨ hka hkb (.inl ⟨rfl, bne_f h.1, bne_f h.2⟩))

end gp

section body
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {T : DS → Word → (Nat → Word) → List Event}
  {c : Ctx} {sp0 : Word} {n : Nat} {X0 : Word → Prop} (fm : Frm c dsGeo sp0 n X0)
  (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (dsGeo.fsp c) y ∧ X0 y)
  (hT : ∀ a base p, (dsS a).Eff p base (T a base p)) (cd : Code B BS) (cl : CodeL B BS)
include fm hcode

/-- The index step from either state between the passes. -/
theorem dec_gp {Ψ : TrP} {J : Ef → Prop} (h : GP sp0 n (BI c dsGeo sp0 n X0 LH) Ψ J) :
    ∀ S, S = E1 ∨ S = E3 → GP sp0 n (BI c dsGeo sp0 n X0 S) (decTr c Ψ) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, g15, -, -, -, -, -, -, -, g23⟩ := glue_facts
  intro S hS
  unfold decTr
  exact GP.cat (fr_gp fm hcode g23 (g15 S (by rcases hS with rfl | rfl <;> simp)).2.2 (by decide) _)
    (GP.cat (quiet_gp rfl rfl rfl) h)

include hT cd cl in
/-- **The loop** with `m ≤ 256` passes left. -/
theorem lp_gp {da db : Nat → Word} (hka : ∀ i < 256, (da i).toInt ≠ 0 → Ed25519DsmLoop.kOf (da i) < 2)
    (hkb : ∀ i < 256, (db i).toInt ≠ 0 → Ed25519DsmLoop.kOf (db i) < 8) {Ψx : TrP} {J : Ef → Prop}
    (hx : GP sp0 n (BI c dsGeo sp0 n X0 LH) Ψx J) (m : Nat) (hm : m ≤ 256) :
    GP sp0 n (BI c dsGeo sp0 n X0 LH) (lpTr T c da db Ψx m) J := by
  obtain ⟨-, -, -, -, -, -, g7, g8, g9, g10, -⟩ := glue_facts
  induction m with
  | zero =>
    rw [lpTr]
    exact GP.cat (fr_gp fm hcode g7 g8 (by decide) _) (GP.cat (quiet_gp rfl rfl rfl)
      (GP.cond (fun h => absurd h (by decide)) fun _ => GP.cat (quiet_gp rfl rfl rfl) hx))
  | succ m ih =>
    rw [lpTr]
    refine GP.cat (fr_gp fm hcode g7 g8 (by decide) _) (GP.cat (quiet_gp rfl rfl rfl)
      (GP.cond (fun _ => ?_) fun _ => GP.cat (quiet_gp rfl rfl rfl) hx))
    exact GP.cat (dg_gp fm hcode g9 g10 (by omega) _) (rest_gp fm hcode hT cd cl
      (dec_gp fm hcode (ih (by omega))) (hka m (by omega)) (hkb m (by omega)))

/-- **The scan** from index `j ≤ 255`, then `Ψ` of its result. -/
theorem scan_gp {z : Nat → Bool} {Ψ : Nat → TrP} {J : Ef → Prop}
    (hΨ : ∀ j, j ≤ 255 ∨ j = 2 ^ 32 - 1 → GP sp0 n (BI c dsGeo sp0 n X0 s0) (Ψ j) J) (j : Nat) (hj : j ≤ 255) :
    GP sp0 n (BI c dsGeo sp0 n X0 s0) (scanTr (c := c) z Ψ j) J := by
  obtain ⟨-, g2, -, -, g5, g6, -⟩ := glue_facts
  induction j with
  | zero =>
    rw [scanTr, scanHd]
    exact GP.cat (dg_gp fm hcode g5 g6 (by omega) _) (GP.cat (quiet_gp rfl rfl rfl)
      (GP.cond (fun _ => GP.cat (nil_gp fm hcode g2 _) (GP.cat (quiet_gp rfl rfl rfl)
        (GP.cond (fun _ => hΨ _ (.inr rfl)) fun h => by cases h)))
        fun _ => GP.cat (quiet_gp rfl rfl rfl) (hΨ 0 (.inl (by omega)))))
  | succ j ih =>
    rw [scanTr, scanHd]
    exact GP.cat (dg_gp fm hcode g5 g6 (by omega) _) (GP.cat (quiet_gp rfl rfl rfl)
      (GP.cond (fun _ => GP.cat (nil_gp fm hcode g2 _) (GP.cat (quiet_gp rfl rfl rfl)
        (GP.cond (fun h => by cases h) fun _ => GP.cat (quiet_gp rfl rfl rfl) (ih (by omega)))))
        fun _ => GP.cat (quiet_gp rfl rfl rfl) (hΨ _ (.inl hj))))

include hT cd cl in
/-- **The body's invariant along its trace**, from the entry state to `Send`, at digit words whose
halves index the tables. -/
theorem body_gp {z : Nat → Bool} {da db : Nat → Word}
    (hka : ∀ i < 256, (da i).toInt ≠ 0 → Ed25519DsmLoop.kOf (da i) < 2)
    (hkb : ∀ i < 256, (db i).toInt ≠ 0 → Ed25519DsmLoop.kOf (db i) < 8) {Ψ : TrP} {J : Ef → Prop}
    (hΨ : GP sp0 n (BI c dsGeo sp0 n X0 Send) Ψ J) :
    GP sp0 n (BI c dsGeo sp0 n X0 stE) (bodyTr T c z da db Ψ) J := by
  obtain ⟨g1, -, g3, g4, -⟩ := glue_facts
  obtain ⟨e1, e2, e3, -⟩ := eok_facts
  obtain ⟨-, -, -, -, -, -, -, -, -, b10, b11, b12, -, -, b15, b16, b17, -⟩ := body_ok
  unfold bodyTr mvTr
  refine pt_gp fm hcode hT cd b15 b10 e1 (GP.cat (nil_gp fm hcode g1 _) (scan_gp fm hcode (fun j hj => ?_) 255 (Nat.le_refl _)))
  unfold stTr
  exact GP.cat (fr_gp fm hcode g3 g4 (by decide) _) (pt_gp fm hcode hT cd b16 b11 e2
    (lp_gp fm hcode hT cd cl hka hkb (pt_gp fm hcode hT cd b17 b12 e3 hΨ) _ (nOf_le hj)))

end body

/-! ## The effect's premise -/

/-- **The premise on the public values**: the halves of the nonzero digits read from them index
the tables (`h`'s two entries, `s`'s eight). -/
def ppD (p : Nat → Word) : Prop :=
  ∀ i < 256, ((dP p 69 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dP p 69 i) < 2) ∧
    ((dP p 5 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dP p 5 i) < 8)

/-- The outputs are views at `Send`. -/
theorem outs_facts : ∀ x ∈ dq.s.io.outs, dq.outOk Send.Γ x = true := by decide +kernel

/-- **The body's effect** for `effW`: under `ppD`, from the frame's invariant at the entry state,
`ΨD` reaches the frame's invariant with the outputs written. -/
theorem dsm_gp {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {T : DS → Word → (Nat → Word) → List Event}
    (hT : ∀ a base p, (dsS a).Eff p base (T a base p)) (cd : Code B BS) (cl : CodeL B BS)
    (base : Word) (p : Nat → Word) (hp : ppD p) (sp0 : Word) (n : Nat) (X0 : Word → Prop)
    (fm : Frm (dq.ctx base p) dq.geo sp0 n X0)
    (hcode : ∀ y, Has [@codeR B BS _ base] y → BelowEntry sp0 n y →
      AtOrAboveSp sp0 (dq.geo.fsp (dq.ctx base p)) y ∧ X0 y) :
    GP sp0 n (BI (dq.ctx base p) dq.geo sp0 n X0 dq.st0) (ΨD T base p)
      (SIR sp0 (dq.geo.fsp (dq.ctx base p)) fun y => X0 y ∨ dq.woW p dq.s.io.outs y ∧ BelowEntry sp0 n y) := by
  rw [dq_facts.2.1]
  exact body_gp fm hcode hT cd cl (fun i hi => (hp i hi).1) (fun i hi => (hp i hi).2)
    (GP.nil fun _ hq => dq.outs_sir (CalleeP.okF_parts dq_facts.2.2.2) outs_facts hq)

/-! ## One trace -/

section tq
variable {T : DS → Word → (Nat → Word) → List Event} {c : Ctx} (Q : TrP → Prop) (hi : ∀ l, Q (Tr.is l))
  (hc : ∀ {Φ Ψ : TrP}, Q Φ → Q Ψ → Q (Tr.cat Φ Ψ)) (hd : ∀ {b : Bool} {Φ Ψ : TrP}, Q Φ → Q Ψ → Q (Tr.cond b Φ Ψ))
  (hp : ∀ {P : Prog DS DB} {o : Nat} {S : St} {Ψ : TrP}, Q Ψ → Q (pt T c P o S Ψ))
include hi hc hd hp

/-- **The loop's trace** keeps a property of traces closed under the constructors. -/
theorem lp_q {da db : Nat → Word} {Ψx : TrP} (h : Q Ψx) : ∀ m, Q (lpTr T c da db Ψx m) := by
  intro m
  induction m with
  | zero =>
    rw [lpTr]; unfold Ed25519DsmPass.loopTr
    repeat (first | assumption | exact hi _ | apply hp | apply hc | apply hd)
  | succ m ih =>
    rw [lpTr]; unfold Ed25519DsmPass.loopTr digTr restTr orTr tDA tDB1 tDB2 Ed25519DsmPass.tstTr pbTr decTr
    repeat (first | assumption | exact hi _ | apply hp | apply hc | apply hd)

omit hp in
/-- **The scan's trace** keeps it. -/
theorem scan_q {z : Nat → Bool} {Ψ : Nat → TrP} (h : ∀ j, Q (Ψ j)) : ∀ j, Q (scanTr (c := c) z Ψ j) := by
  intro j
  induction j with
  | zero =>
    rw [scanTr, scanHd]
    repeat (first | exact h _ | exact hi _ | apply hp | apply hc | apply hd)
  | succ j ih =>
    rw [scanTr, scanHd]
    repeat (first | assumption | exact h _ | exact hi _ | apply hp | apply hc | apply hd)

/-- **The body's trace** keeps it. -/
theorem body_q {z : Nat → Bool} {da db : Nat → Word} {Ψ : TrP} (h : Q Ψ) : Q (bodyTr T c z da db Ψ) := by
  unfold bodyTr mvTr
  refine hp (hc (hi _) (scan_q Q hi hc hd (fun _ => ?_) _))
  unfold stTr
  exact hc (hi _) (hp (lp_q Q hi hc hd hp (hp h) _))

end tq

theorem ψD_uniq (T : DS → Word → (Nat → Word) → List Event) (base : Word) (p : Nat → Word) :
    Tr.Uniq (ΨD T base p) :=
  body_q Tr.Uniq Tr.uniq_is Tr.uniq_cat Tr.uniq_cond
    (fun h => Prog.tr_uniq _ _ _ h fun _ hx => absurd hx List.not_mem_nil) (Tr.uniq_is _)

theorem ψD_ex (T : DS → Word → (Nat → Word) → List Event) (base : Word) (p : Nat → Word) :
    Tr.Ex (ΨD T base p) :=
  body_q Tr.Ex Tr.ex_is Tr.ex_cat Tr.ex_cond
    (fun h => Prog.tr_ex _ _ _ h fun _ hx => absurd hx List.not_mem_nil) (Tr.ex_is _)

end M0Crypto.Release.Ed25519DsmGood
