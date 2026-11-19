import M0Crypto.Release.Ed25519DsmRun

/-!
# One pass of `m0c_ge_dsm`'s loop

The loop at `dsm_loop` over the index `I` (a word at `sp + 4`): its test, the digit loads into
`DA` and `DB`, the doubling, the conversions and the signed additions chosen by the digits'
tests, and the index step. The loop's words `I`, `DA`, `DB` are `.cw` views (`ext`); the pointer
words of `signed_add` are `.pw` views. The glue sets views only at the words `N`, which no
update of a pass reads (`run_agree`).
-/

namespace M0Crypto.Release.Ed25519DsmPass

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
open M0Crypto.Sym (SExpr)
open M0Crypto.Release.BlockEffect (Eff effOk eff_run)
open M0Crypto.Release.Ed25519DsmVal (sgn sgn_lt)
open M0Crypto.Artifacts.Ed25519Compact (dsm_a_add dsm_a_branch dsm_a_done dsm_a_index dsm_a_jump_join dsm_a_next_branch dsm_a_p2
  dsm_a_test_next dsm_b_add dsm_b_branch dsm_b_entry dsm_b_index dsm_b_table dsm_dbl_jump
  dsm_dbl_p2 dsm_dbl_p3 dsm_dec_index dsm_digits_branch dsm_double dsm_jump_loop dsm_load_digits
  dsm_loop dsm_loop_branch dsm_output dsm_test_a dsm_test_digits)

/-! ## The loop's code -/

/-- A digit's test: `ldr r0, [sp, #4 ds]; cmp r0, #0`. -/
def tstG (ds : Nat) : List Instr := [.ldrSp 0 (BitVec.ofNat 8 ds), .cmpImm 0 0]

/-- `DB`'s table: `r1` from the literal and `pc`, the table `odd_b` (code buffer `5`). -/
def ldB : Op DS DB := .ld 1 (.C 5 0 48)

/-- `DB`'s pointers after the table's address: the entry, then the tail. -/
def tailB : List Instr := .addReg 0 0 1 :: tailG 3

/-- The loop's glue at its offsets, decided per build. -/
structure CodeL (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop where
  loop : piecesAt B dsm_loop (.seq loopG :: (xitBr 11#4 false dsm_loop_branch dsm_output ++ [])) = true
  brL : brOk (B := B) dsGeo false dsm_loop_branch dsm_output = true
  dig : piecesAt B dsm_load_digits [.seq digG] = true
  or : piecesAt B dsm_test_digits (.seq orG :: (xitBr 0#4 false dsm_digits_branch dsm_dbl_p2 ++ [])) = true
  brO : brOk (B := B) dsGeo false dsm_digits_branch dsm_dbl_p2 = true
  j1 : piecesAt B dsm_dbl_jump [.b dsm_test_a] = true
  bj1 : bOk (B := B) dsGeo.cs dsm_dbl_jump dsm_test_a = true
  ta : piecesAt B dsm_test_a (.seq (tstG 2) :: (xitBr 0#4 false dsm_a_branch dsm_a_done ++ [])) = true
  brA : brOk (B := B) dsGeo false dsm_a_branch dsm_a_done = true
  ha : piecesAt B dsm_a_index [.seq (headA ++ tailG 2)] = true
  tb1 : piecesAt B dsm_a_test_next (.seq (tstG 3) :: (xitBr 0#4 false dsm_a_next_branch dsm_a_p2 ++ [])) = true
  brB1 : brOk (B := B) dsGeo false dsm_a_next_branch dsm_a_p2 = true
  j2 : piecesAt B dsm_a_jump_join [.b dsm_a_done] = true
  bj2 : bOk (B := B) dsGeo.cs dsm_a_jump_join dsm_a_done = true
  tb2 : piecesAt B dsm_a_done (.seq (tstG 3) :: (xitBr 0#4 false dsm_b_branch dsm_dec_index ++ [])) = true
  brB2 : brOk (B := B) dsGeo false dsm_b_branch dsm_dec_index = true
  hb : piecesAt B dsm_b_index (.seq headB1 :: (ldB.pieces dsS dbS ++ [.seq tailB])) = true
  lb : ldB.bok (B := B) dsS dbS dsGeo dsm_b_table = true
  dec : piecesAt B dsm_dec_index [.seq decG, .b dsm_loop] = true
  bj3 : bOk (B := B) dsGeo.cs dsm_jump_loop dsm_loop = true

open M0Crypto.Release.Ed25519 (Build) in
theorem codeL_c : @CodeL _ _ Build.compact.codeBytes := by
  refine @CodeL.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem codeL_f : @CodeL _ _ Build.fast.codeBytes := by
  refine @CodeL.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem codeL_b : ∀ b : Build, @CodeL _ _ b.codeBytes
  | .compact => codeL_c
  | .fast => codeL_f

/-- `r0` after a word load and a compare. -/
def eLd (o : Nat) : Eff := { regs := [(0, dW o)] }

theorem glue_ok : sglueOk dsGeo.cs loopG dsm_loop dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oI, 4)] = true ∧
    traceOkE loopG [.reg0 13] = true ∧ effOk loopG (eLd oI) = true ∧
    effOk [.ldrSp 0 2] (eLd oDa) = true ∧ effOk [.ldrSp 0 3] (eLd oDb) = true := by
  decide +kernel

/-! ## The loop's states -/

/-- The loop head: the views after `segId` and `I`. -/
def LH : St := { rs s1 with Γ := (.fr oI, .cw) :: s1.Γ }

/-- After the loop's test: `r0 = I`. -/
def LHr (i : Nat) : St := { LH with σ := [(0, .k i), (13, .sp 0)] }

theorem s1_facts : s1.X = [] ∧ s1.ρ = [] ∧ (Loc.fr 24, Kd.pw (.ext 2 0)) ∈ s1.Γ ∧
    (Loc.fr 20, Kd.pw (.ext 1 0)) ∈ s1.Γ := by
  decide +kernel

/-- The states between the pass's straight lines: after the digits, after the doubling, after a
conversion with `T`. -/
def E1 : St := ext (rs s1)
def E2 : St := ext (rs sD)
def E3 : St := ext (rs sP3)

/-- The digit words' views and regions. -/
def Wd : List (Loc × Kd) := [(.fr oDa, .cw), (.fr oDb, .cw)]
def wsD : List SR := [⟨.fr oDa, .k 4⟩, ⟨.fr oDb, .k 4⟩]
def digWg : List (SExpr × Nat) := [(spW oDa, 4), (spW oDb, 4)]

theorem dig_ok : sglueOk dsGeo.cs digG dsm_load_digits dsGeo.top dsGeo.N scanAl digWg scanRg = true ∧
    traceOkE digG scanAs = true ∧ (∀ w ∈ wsD, w.ok dsGeo = true ∧ w.acc dsGeo true = true) ∧
    (∀ p ∈ Wd, (Kd.sr p.1 p.2).ok dsGeo = true) ∧ (Wd.map (·.1)).Nodup ∧ wkB (glueSt LH wsD Wd σsp) E1 = true := by
  decide +kernel

/-- The tests' glue at their offsets. -/
theorem tst_ok : sglueOk dsGeo.cs orG dsm_test_digits dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oDa, 8)] = true ∧
    traceOkE orG [.reg0 13] = true ∧
    sglueOk dsGeo.cs (tstG 2) dsm_test_a dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oDa, 4)] = true ∧
    sglueOk dsGeo.cs (tstG 3) dsm_a_test_next dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oDb, 4)] = true ∧
    sglueOk dsGeo.cs (tstG 3) dsm_a_done dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oDb, 4)] = true ∧
    traceOkE (tstG 2) [.reg0 13] = true ∧ traceOkE (tstG 3) [.reg0 13] = true := by
  decide +kernel

theorem ext_facts : ∀ S ∈ [E1, E2, E3], S.σ = σsp ∧ S.ρ = [] ∧ (Loc.fr oDa, Kd.cw) ∈ S.Γ ∧
    (Loc.fr oDb, Kd.cw) ∈ S.Γ ∧ (Loc.fr oI, Kd.cw) ∈ S.Γ := by
  decide +kernel

/-- A digit as a word: the byte at `ptr r + i`, sign-extended. -/
def sw (b : BitVec 8) : Word := (b.setWidth 32 <<< 24).sshiftRight 24
def dv (m0 : Mem) (c : Ctx) (r i : Nat) : Word := sw (m0 (c.ptr r + BitVec.ofNat 32 i))

theorem dv_toInt (m0 : Mem) (c : Ctx) (r i : Nat) : (dv m0 c r i).toInt = digOf m0 (c.ptr r) i := sext_toInt _

/-- The pointer words' regions and values. -/
def wsT : List SR := [⟨.fr oEp, .k 4⟩, ⟨.fr oEa, .k 4⟩, ⟨.fr oEb, .k 4⟩, ⟨.fr oTz, .k 4⟩, ⟨.fr oTt, .k 4⟩]
def ptrWg : List (SExpr × Nat) := [(spW oEp, 4), (spW oEa, 4), (spW oEb, 4), (spW oTz, 4), (spW oTt, 4)]
def nones : List V := [.none, .none, .none, .none, .none]

theorem ptrA_ok : sglueOk dsGeo.cs (headA ++ tailG 2) dsm_a_index dsGeo.top dsGeo.N [(.reg0 13, 4)] ptrWg
      [(spW oDa, 4), (spW oEp, 4)] = true ∧ traceOkE (headA ++ tailG 2) [.reg0 13] = true ∧
    (∀ w ∈ wsT, w.ok dsGeo = true ∧ w.acc dsGeo true = true) ∧
    (∀ k < 2, ∀ s < 2, (∀ p ∈ ptrΓ (aiP k) s, (Kd.sr p.1 p.2).ok dsGeo = true) ∧
      ((ptrΓ (aiP k) s).map (·.1)).Nodup ∧ wkB (glueSt E3 wsT (ptrΓ (aiP k) s) σsp) (ext (saSt k s)) = true) := by
  decide +kernel

/-- The state after `headB1`: `r0 = 96 k`; after the table's load: `r1 = odd_b`. -/
def B1 (k : Nat) : St := glueSt E3 [] [] [(0, .k (96 * k)), (13, .sp 0)]
def B2 (k : Nat) : St := { B1 k with σ := (1, .ext 5 0) :: (B1 k).σ.filter (·.1 != 1) }

def eAdd : Eff := { regs := [(0, .add (.reg0 0) (.reg0 1))] }

theorem ptrB_ok : sglueOk dsGeo.cs headB1 dsm_b_index dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW oDb, 4)] = true ∧
    traceOkE headB1 [.reg0 13] = true ∧
    sglueOk dsGeo.cs tailB dsm_b_entry dsGeo.top dsGeo.N [(.reg0 13, 4)] ptrWg [(spW oDb, 4), (spW oEp, 4)] = true ∧
    traceOkE tailB [.reg0 13] = true ∧ effOk [.addReg 0 0 1] eAdd = true ∧ ldB.size dsS dbS = 4 ∧
    (∀ k < 8, ∀ s < 2, (∀ p ∈ ptrΓ (obP k) s, (Kd.sr p.1 p.2).ok dsGeo = true) ∧
      ((ptrΓ (obP k) s).map (·.1)).Nodup ∧ wkB (glueSt (B2 k) wsT (ptrΓ (obP k) s) σsp) (ext (sbSt k s)) = true) := by
  decide +kernel

theorem dec_ok : sglueOk dsGeo.cs decG dsm_dec_index dsGeo.top dsGeo.N [(.reg0 13, 4)] [(spW oI, 4)] [(spW oI, 4)] = true ∧
    traceOkE decG [.reg0 13] = true ∧ (⟨.fr oI, .k 4⟩ : SR).ok dsGeo = true ∧ (⟨.fr oI, .k 4⟩ : SR).acc dsGeo true = true ∧
    (Kd.sr (.fr oI) .cw).ok dsGeo = true ∧
    wkB (glueSt E1 [⟨.fr oI, .k 4⟩] [(.fr oI, .cw)] σsp) LH = true := by
  decide +kernel

theorem add2 (a : Word) (x y : Nat) : a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sub2 (a : Word) (x y : Nat) (h : y ≤ x) (_hx : x < 2 ^ 32) :
    a + BitVec.ofNat 32 x - BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow] at *
  omega

theorem sg_eq (w : Word) : sg w = 32 * sgn w.toInt := by
  unfold sg sgn; split <;> rfl

theorem cond_lt (s : State) : condPassed 11#4 s = (s.n != s.v) := rfl
theorem cond_eq (s : State) : condPassed 0#4 s = s.z := rfl

section run
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {Wc Rc : List Rgn} (m0 : Mem)

/-- A counter view's word. -/
theorem cw_view {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c dsGeo m0 st E m) {o : Nat} {x : Word}
    (h : (Loc.fr o, Kd.cw) ∈ st.Γ) (hx : E (.fr o) = .w x) : read32 m (dsGeo.fsp c + BitVec.ofNat 32 o) = x := by
  have := (hi.1 _ h).2; rw [hx] at this; simpa [Rel, Loc.addr] using this

/-- A frame word lies in the window. -/
theorem fr_win (g : GeoOk c dsGeo Wc Rc) {o : Nat} (h : o < dsGeo.top) :
    Has [dsGeo.win c] (dsGeo.fsp c + BitVec.ofNat 32 o) := by
  have ht := g.top; have hr := g.room; have := c.sp0.isLt
  refine ⟨_, List.mem_singleton_self _, dsGeo.N - dsGeo.top + o, by simp only [Geo.win]; omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [g.fr_toNat (Nat.le_of_lt h), BitVec.toNat_add, g.win_toNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  omega

/-- A buffer byte is no frame byte. -/
theorem ex_ne_fr (g : GeoOk c dsGeo Wc Rc) {i j o : Nat} (ho : SR.ok dsGeo ⟨.ex i j, .k 1⟩ = true)
    (h : o < dsGeo.top) : c.ptr i + BitVec.ofNat 32 j ≠ dsGeo.fsp c + BitVec.ofNat 32 o := by
  intro he
  have hs := g.ex_win ho rfl
  have hr : SR.rgns dsGeo c ⟨.ex i j, .k 1⟩ = [⟨c.ptr i + BitVec.ofNat 32 j, 1⟩] := by
    simp [SR.rgns, XLen.v, Loc.addr]
  rw [hr] at hs
  exact Sep.not_has hs ⟨_, List.mem_singleton_self _, 0, Nat.one_pos, by simp⟩ (he ▸ fr_win g h)

/-- Back from a glue block that writes nothing to a state with fewer views and registers. -/
theorem at_g0 {o : Nat} {S S' : St} {σ : List (Reg × SV)} {E : Loc → V} {t : State}
    (h : At Rs B c dsGeo m0 o (glueSt S [] [] σ) E t) (hΓ : ∀ p ∈ S'.Γ, p ∈ S.Γ) (hX : ∀ r ∈ S.X, r ∈ S'.X)
    (hσ : ∀ p ∈ S'.σ, p ∈ σ) (hρ : S'.ρ = []) : At Rs B c dsGeo m0 o S' E t :=
  at_weak Rs m0 h (by simpa [glueSt, keep_nil] using hΓ) (by simpa [glueSt] using hX) hσ (by simp [hρ])

/-- The loop test's trace: on `d` on to the digits, else to `segEnd`. -/
def loopTr (c : Ctx) (d : Bool) (Ψc Ψx : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE loopG (c.base + BitVec.ofNat 32 dsm_loop) [.reg0 13] [dsGeo.fsp c]))
    (Tr.cat (Tr.is [bcEv c (11#4 ^^^ 1) dsm_loop_branch (dsm_loop_branch + 4)])
      (Tr.cond d Ψc (Tr.cat (Tr.is [bEv c (dsm_loop_branch + 2) dsm_output]) Ψx)))

/-- **The loop test** at `dsm_loop` with `I = x`: for `0 ≤ x` to the digits with `r0 = x`, else to
`segEnd`. -/
theorem loop_tst (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψc Ψx : TrP} {x : Word} {t : State}
    (hat : At Rs B c dsGeo m0 dsm_loop LH E t) (hx : E (.fr oI) = .w x)
    (kc : 0 ≤ x.toInt → ∀ u, At Rs B c dsGeo m0 dsm_load_digits (LHr x.toNat) E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψc)
    (kx : x.toInt < 0 → ∀ u, At Rs B c dsGeo m0 dsm_output LH E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (loopTr c (decide (0 ≤ x.toInt)) Ψc Ψx) := by
  have h13 := hat.2.1
  have hI : read32 t.mem (t.regs 13 + BitVec.ofNat 32 oI) = x := by
    rw [h13]; exact cw_view Rs m0 hat.2.2.2.2.1 (List.mem_cons_self ..) hx
  have h0 : (execAll loopG t).regs 0 = x := by
    rw [(eff_run glue_ok.2.2.1 t).reg 0 (by decide) (by decide)]; exact hI
  have hAs : [SExpr.reg0 13].map (·.denote t) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  unfold loopTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := []) (outs := []) (vs := []) (σ := (LHr x.toNat).σ) glue_ok.1 glue_ok.2.1
    cl.loop hat ?_ ?_ (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu hp2 => ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · have e : sregions t [(spW oI, 4)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 oI, 4⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil
  · intro h13' p hp
    simp only [LHr, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨show (0 : Nat) < 14 by decide, by rw [h0]; simp [SV.val]⟩
    · exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : dsm_loop + seqSize loopG = dsm_loop_branch := by decide
    rw [e] at hu hp2
    refine br_run Rs m0 g F (d := decide (0 ≤ x.toInt)) (by decide) cl.brL hp2 hu ?_
      (fun hd hS _ => kc (by simpa using hd) _ (at_g0 Rs m0 hS (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (by simp [LHr, LH, rs, s1_facts.2.1])))
      (fun hd hX => kx (by simpa using hd) _ (at_g0 Rs m0 hX (fun _ h => h) (fun _ h => h)
        (fun p hp => by simp only [LH, rs, σsp, List.mem_singleton] at hp; simp [LHr, hp]) (by simp [LH, rs, s1_facts.2.1])))
    have hg := loop_ge t
    rw [hI] at hg
    rw [cond_lt, bne]
    by_cases h : 0 ≤ x.toInt
    · rw [decide_eq_true h, hg.mpr h]
    · rw [decide_eq_false h]
      cases e : ((execAll loopG t).n == (execAll loopG t).v)
      · rfl
      · exact absurd (hg.mp e) h

/-- The digit loads' trace at index `i`. -/
def digTr (c : Ctx) (i : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE digG (c.base + BitVec.ofNat 32 dsm_load_digits) scanAs
    [dsGeo.fsp c, c.ptr 2 + BitVec.ofNat 32 i, c.ptr 1 + BitVec.ofNat 32 i])) Ψ

/-- **The digits** at `dsm_load_digits` with `r0 = i`: `DA` and `DB` become the digits of `h` and `s` at
`i`, as words. -/
theorem dig_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : TrP} {i : Nat} (hi : i < 256) {t : State}
    (hat : At Rs B c dsGeo m0 dsm_load_digits (LHr i) E t)
    (k : ∀ u, At Rs B c dsGeo m0 dsm_double E1 (updOuts E Wd [.w (dv m0 c 2 i), .w (dv m0 c 1 i)]) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (digTr c i Ψ) := by
  have h13 := hat.2.1
  have h0 : t.regs 0 = BitVec.ofNat 32 i := (hat.2.2.2.1 (0, .k i) (by simp [LHr])).2
  have hi' := hat.2.2.2.2.1
  have ph : read32 t.mem (dsGeo.fsp c + BitVec.ofNat 32 24) = c.ptr 2 + BitVec.ofNat 32 0 :=
    pw_view Rs m0 hi' (List.mem_cons_of_mem _ s1_facts.2.2.1)
  have ps : read32 t.mem (dsGeo.fsp c + BitVec.ofNat 32 20) = c.ptr 1 + BitVec.ofNat 32 0 :=
    pw_view Rs m0 hi' (List.mem_cons_of_mem _ s1_facts.2.2.2)
  have hX : (LHr i).X = [] := s1_facts.1
  have hok : ∀ r, r = 1 ∨ r = 2 → SR.ok dsGeo ⟨.ex r i, .k 1⟩ = true := fun r hr => by
    rcases hr with rfl | rfl <;> simp [SR.ok, dsGeo] <;> omega
  have hs : ∀ k < 4, read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0 ≠
      t.regs 13 + BitVec.ofNat 32 oDa + BitVec.ofNat 32 k := fun k hk => by
    rw [h13, h0, show oSp = 20 from rfl, ps, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ex_ne_fr g (hok 1 (.inl rfl)) (by simp only [oDa, dsGeo, oTop]; omega)
  have hd := dig_spec t i h0 hs
  rw [h13, show oHp = 24 from rfl, show oSp = 20 from rfl, ph, ps, BitVec.add_zero, BitVec.add_zero,
    dig_m0 Rs m0 g hi' hX (.inr rfl) hi, dig_m0 Rs m0 g hi' hX (.inl rfl) hi] at hd
  have hAs : scanAs.map (·.denote t) = [dsGeo.fsp c, c.ptr 2 + BitVec.ofNat 32 i, c.ptr 1 + BitVec.ofNat 32 i] := by
    simp only [scanAs, bA, dW, spW, List.map, M0Crypto.Sym.SExpr.denote, M0Crypto.Sym.SMem.denote, oHp, oSp, h13, h0,
      ph, ps, BitVec.add_zero]
  have hfr : ∀ o, o + 4 ≤ dsGeo.top → (dsGeo.fsp c + BitVec.ofNat 32 o).toNat + 4 ≤ 2 ^ 32 := fun o ho => by
    have := g.fr_toNat (Nat.le_of_add_right_le ho); have := c.sp0.isLt; have := g.room; have := g.top
    omega
  unfold digTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := wsD) (outs := Wd) (vs := [.w (dv m0 c 2 i), .w (dv m0 c 1 i)]) (σ := σsp)
    dig_ok.1 dig_ok.2.1 cl.dig hat ?_ ?_ dig_ok.2.2.1 ?_ dig_ok.2.2.2.1 dig_ok.2.2.2.2.1 ?_ ?_
    (fun hu _ => k _ (at_wk Rs m0 hu (by simpa [glueSt, LHr] using dig_ok.2.2.2.2.2)))
  · intro r hr
    simp only [scanAl, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
    · exact Nat.mod_one _
    · exact Nat.mod_one _
  · have e : sregions t scanRg = [⟨dsGeo.fsp c + BitVec.ofNat 32 20, 8⟩, ⟨c.ptr 2 + BitVec.ofNat 32 i, 1⟩,
        ⟨c.ptr 1 + BitVec.ofNat 32 i, 1⟩] := by
      simp only [sregions, scanRg, bA, dW, spW, List.map, M0Crypto.Sym.SExpr.denote, M0Crypto.Sym.SMem.denote, oHp, oSp,
        h13, h0, ph, ps, BitVec.add_zero]
    have hb : ∀ r, r = 1 ∨ r = 2 → Sub [⟨c.ptr r + BitVec.ofNat 32 i, 1⟩] Rc := fun r hr => by
      have := g.sub (r := ⟨.ex r i, .k 1⟩) (hok r hr) false (by rcases hr with rfl | rfl <;> simp [SR.acc, dsGeo])
      simpa [SR.rgns, XLen.v, Loc.addr] using this
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) (sub_cons' (hb 2 (.inr rfl)) (sub_cons' (hb 1 (.inl rfl))
      fun _ h => absurd h List.not_mem_nil))
  · have e1 : sregions t digWg = [⟨dsGeo.fsp c + BitVec.ofNat 32 oDa, 4⟩, ⟨dsGeo.fsp c + BitVec.ofNat 32 oDb, 4⟩] := by
      simp only [sregions, digWg, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    have e2 : wsD.flatMap (SR.rgns dsGeo c) =
        [⟨dsGeo.fsp c + BitVec.ofNat 32 oDa, 4⟩, ⟨dsGeo.fsp c + BitVec.ofNat 32 oDb, 4⟩] := by
      simp [wsD, SR.rgns, XLen.v, Loc.addr]
    rw [e1, e2]
    refine Sub.refl _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hfr _ (by decide)
  · have ea : (read32 (execAll digG t).mem (dsGeo.fsp c + BitVec.ofNat 32 oDa)) = dv m0 c 2 i :=
      BitVec.eq_of_toInt_eq (by rw [hd.1, dv_toInt])
    have eb : (read32 (execAll digG t).mem (dsGeo.fsp c + BitVec.ofNat 32 oDb)) = dv m0 c 1 i :=
      BitVec.eq_of_toInt_eq (by rw [hd.2, dv_toInt])
    exact ⟨by simpa [Rel, Loc.addr] using ea, by simpa [Rel, Loc.addr] using eb, trivial⟩
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩

/-- A digit test's trace: on `d` on after the branch, else to `T`. -/
def tstTr (c : Ctx) (o ds ob T : Nat) (d : Bool) (Ψc Ψx : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE (tstG ds) (c.base + BitVec.ofNat 32 o) [.reg0 13] [dsGeo.fsp c]))
    (Tr.cat (Tr.is [bcEv c (0#4 ^^^ 1) ob (ob + 4)]) (Tr.cond d Ψc (Tr.cat (Tr.is [bEv c (ob + 2) T]) Ψx)))

/-- **A digit test** at `o` of the word `w` at `sp + 4 ds`: for `w ≠ 0` on after the branch at `ob`,
else to `T`. -/
theorem tst_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) {o ob T ds : Nat} {S : St}
    {E : Loc → V} {Q : State → Prop} {Ψc Ψx : TrP} {w : Word} {t : State}
    (hok : sglueOk dsGeo.cs (tstG ds) o dsGeo.top dsGeo.N [(.reg0 13, 4)] [] [(spW (4 * ds), 4)] = true)
    (htr : traceOkE (tstG ds) [.reg0 13] = true) (hef : effOk [.ldrSp 0 (BitVec.ofNat 8 ds)] (eLd (4 * ds)) = true)
    (hds : 4 * ds + 4 ≤ dsGeo.top) (hp : piecesAt B o (.seq (tstG ds) :: (xitBr 0#4 false ob T ++ [])) = true)
    (hob : o + 4 = ob) (hbr : brOk (B := B) dsGeo false ob T = true) (hS : S.σ = σsp ∧ S.ρ = [])
    (hv : (Loc.fr (4 * ds), Kd.cw) ∈ S.Γ) (hw : E (.fr (4 * ds)) = .w w) (hat : At Rs B c dsGeo m0 o S E t)
    (kc : w.toInt ≠ 0 → ∀ u, At Rs B c dsGeo m0 (ob + 4) S E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψc)
    (kx : w.toInt = 0 → ∀ u, At Rs B c dsGeo m0 T S E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (tstTr c o ds ob T (w.toInt != 0) Ψc Ψx) := by
  have h13 := hat.2.1
  have hI : read32 t.mem (t.regs 13 + BitVec.ofNat 32 (4 * ds)) = w := by
    rw [h13]; exact cw_view Rs m0 hat.2.2.2.2.1 hv hw
  have hz : (execAll (tstG ds) t).z = true ↔ w.toInt = 0 := by
    refine one_spec (execAll [.ldrSp 0 (BitVec.ofNat 8 ds)] t) w.toInt ?_
    rw [(eff_run hef t).reg 0 (by decide) (by simp [eLd])]
    show (read32 t.mem (t.regs 13 + BitVec.ofNat 32 (4 * ds))).toInt = _
    rw [hI]
  have hAs : [SExpr.reg0 13].map (·.denote t) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  unfold tstTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := []) (outs := []) (vs := []) (σ := σsp) hok htr hp hat ?_ ?_
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu hp2 => ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · have e : sregions t [(spW (4 * ds), 4)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 (4 * ds), 4⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    rw [e]
    exact sub_cons' (g.frame_sub hds) fun _ h => absurd h List.not_mem_nil
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : o + seqSize (tstG ds) = ob := hob
    rw [e] at hu hp2
    have hσ : ∀ p ∈ S.σ, p ∈ σsp := fun p hp => by rw [hS.1] at hp; exact hp
    refine br_run Rs m0 g F (d := w.toInt != 0) (by decide) hbr hp2 hu ?_
      (fun hd hS' _ => kc (by simpa using hd) _ (at_g0 Rs m0 hS' (fun _ h => h) (fun _ h => h) hσ hS.2))
      (fun hd hX => kx (by simpa using hd) _ (at_g0 Rs m0 hX (fun _ h => h) (fun _ h => h) hσ hS.2))
    rw [cond_eq]
    by_cases h : w.toInt = 0
    · rw [hz.mpr h, h]; rfl
    · have : (execAll (tstG ds) t).z = false := by
        cases e : (execAll (tstG ds) t).z
        · rfl
        · exact absurd (hz.mp e) h
      rw [this]; simp [h]

/-- The test of both digits' trace: on `d` to the conversion with `T`, else to the one without. -/
def orTr (c : Ctx) (d : Bool) (Ψc Ψx : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE orG (c.base + BitVec.ofNat 32 dsm_test_digits) [.reg0 13] [dsGeo.fsp c]))
    (Tr.cat (Tr.is [bcEv c (0#4 ^^^ 1) dsm_digits_branch (dsm_digits_branch + 4)])
      (Tr.cond d Ψc (Tr.cat (Tr.is [bEv c (dsm_digits_branch + 2) dsm_dbl_p2]) Ψx)))

/-- **The test of both digits** at `dsm_test_digits`, after the doubling: unless both are `0` to the
conversion with `T` at `dsm_dbl_p3`, else to the one without at `dsm_dbl_p2`. -/
theorem or_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψc Ψx : TrP} {wa wb : Word} {t : State}
    (ha : E (.fr oDa) = .w wa) (hb : E (.fr oDb) = .w wb) (hat : At Rs B c dsGeo m0 dsm_test_digits E2 E t)
    (kc : (wa.toInt != 0 || wb.toInt != 0) = true → ∀ u, At Rs B c dsGeo m0 dsm_dbl_p3 E2 E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψc)
    (kx : wa.toInt = 0 ∧ wb.toInt = 0 → ∀ u, At Rs B c dsGeo m0 dsm_dbl_p2 E2 E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (orTr c (wa.toInt != 0 || wb.toInt != 0) Ψc Ψx) := by
  have h13 := hat.2.1
  have hf := ext_facts E2 (by simp)
  have hz := or_spec t wa.toInt wb.toInt (by rw [h13, cw_view Rs m0 hat.2.2.2.2.1 hf.2.2.1 ha])
    (by rw [h13, cw_view Rs m0 hat.2.2.2.2.1 hf.2.2.2.1 hb])
  have hAs : [SExpr.reg0 13].map (·.denote t) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  unfold orTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := []) (outs := []) (vs := []) (σ := σsp) tst_ok.1 tst_ok.2.1 cl.or hat ?_ ?_
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu hp2 => ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · have e : sregions t [(spW oDa, 8)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 oDa, 8⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : dsm_test_digits + seqSize orG = dsm_digits_branch := by decide
    rw [e] at hu hp2
    have hσ : ∀ p ∈ E2.σ, p ∈ σsp := fun p hp => by rw [hf.1] at hp; exact hp
    refine br_run Rs m0 g F (d := wa.toInt != 0 || wb.toInt != 0) (by decide) cl.brO hp2 hu ?_
      (fun hd hS' _ => kc hd _ (at_g0 Rs m0 hS' (fun _ h => h) (fun _ h => h) hσ hf.2.1))
      (fun hd hX => kx (by simpa using hd) _ (at_g0 Rs m0 hX (fun _ h => h) (fun _ h => h) hσ hf.2.1))
    rw [cond_eq]
    by_cases h : wa.toInt = 0 ∧ wb.toInt = 0
    · rw [hz.mpr h, h.1, h.2]; rfl
    · have : (execAll orG t).z = false := by
        cases e : (execAll orG t).z
        · rfl
        · exact absurd (hz.mp e) h
      rw [this]
      by_cases ha0 : wa.toInt = 0
      · have hb0 : wb.toInt ≠ 0 := fun hb0 => h ⟨ha0, hb0⟩
        simp [ha0, hb0]
      · simp [ha0]

/-- **The pointer words** after `tailG ds` from `r0 = bw + P`: the views `ptrΓ ep s` with `s` the sign
of the digit word at `sp + 4 ds`, for `ep e = bw + P + e`. -/
theorem ptr_all {u : State} {ds : Nat} (hds : ds = 2 ∨ ds = 3) {ep : Nat → SV} {bw : Word} {P : Nat}
    (hep : ∀ e, (ep e).val c (dsGeo.fsp c) = bw + BitVec.ofNat 32 (P + e)) (hP : P + 32 < 2 ^ 32)
    (h13 : u.regs 13 = dsGeo.fsp c) (h0 : u.regs 0 = bw + BitVec.ofNat 32 P) :
    All2 (fun p v => Rel Rs c (dsGeo.fsp c) p.2 (execAll (tailG ds) u).mem (p.1.addr c (dsGeo.fsp c)) v)
      (ptrΓ ep (sgn (read32 u.mem (u.regs 13 + BitVec.ofNat 32 (4 * ds))).toInt)) nones := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := tail_run u ds hds
  generalize read32 u.mem (u.regs 13 + BitVec.ofNat 32 (4 * ds)) = w at r0 r1 r2 r3 r4 ⊢
  rw [sg_eq] at r1 r2 r3 r4
  have hs := sgn_lt w.toInt
  generalize sgn w.toInt = s at hs r1 r2 r3 r4 ⊢
  rw [h13, h0] at *
  simp only [ptrΓ, nones, All2, Rel, Loc.addr, hep, and_true]
  refine ⟨by rw [r1, add2], ?_, by rw [r0, Nat.add_zero], by rw [r3, add2]; rfl, ?_⟩
  · rw [r2, show (32#32 : Word) = BitVec.ofNat 32 32 from rfl, add2, sub2 _ _ _ (by omega) (by omega)]
    congr 2; omega
  · rw [r4, sub2 _ _ _ (by simp only [oT]; omega) (by simp only [oT]; omega)]; rfl

/-- **`DA`'s pointers** at `dsm_a_index` from the digit word `wa`: the views of `signed_add` over
`AI[|δ| / 2]` with `δ`'s sign. -/
theorem ptrA_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : TrP} {wa : Word} {t : State} (hk : wa.toInt.natAbs / 2 < 2)
    (ha : E (.fr oDa) = .w wa) (hat : At Rs B c dsGeo m0 dsm_a_index E3 E t)
    (k : ∀ u, At Rs B c dsGeo m0 dsm_a_add (ext (saSt (wa.toInt.natAbs / 2) (sgn wa.toInt)))
      (updOuts E (ptrΓ (aiP (wa.toInt.natAbs / 2)) (sgn wa.toInt)) nones) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (Tr.cat (Tr.is (blockTrE (headA ++ tailG 2) (c.base + BitVec.ofNat 32 dsm_a_index) [.reg0 13] [dsGeo.fsp c])) Ψ) := by
  have h13 := hat.2.1
  have hf := ext_facts E3 (by simp)
  have hI : read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDa) = wa := by
    rw [h13]; exact cw_view Rs m0 hat.2.2.2.2.1 hf.2.2.1 ha
  have hP := ptrA_ok.2.2.2 _ hk _ (sgn_lt wa.toInt)
  have hAs : [SExpr.reg0 13].map (·.denote t) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  have hfr : ∀ o, o + 4 ≤ dsGeo.top → (dsGeo.fsp c + BitVec.ofNat 32 o).toNat + 4 ≤ 2 ^ 32 := fun o ho => by
    have := g.fr_toNat (Nat.le_of_add_right_le ho); have := c.sp0.isLt; have := g.room; have := g.top
    omega
  obtain ⟨hA0, hAm⟩ := headA_run t
  have H := eff_run effs_ok.2.2.2.1 t
  have hA13 : (execAll headA t).regs 13 = t.regs 13 := H.reg 13 (by decide) (by decide)
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := wsT) (outs := ptrΓ (aiP (wa.toInt.natAbs / 2)) (sgn wa.toInt)) (vs := nones)
    (σ := σsp) ptrA_ok.1 ptrA_ok.2.1 cl.ha hat ?_ ?_ ptrA_ok.2.2.1 ?_ hP.1 hP.2.1 ?_ ?_
    (fun hu _ => k _ (at_wk Rs m0 hu hP.2.2))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · have e : sregions t [(spW oDa, 4), (spW oEp, 4)] =
        [⟨dsGeo.fsp c + BitVec.ofNat 32 oDa, 4⟩, ⟨dsGeo.fsp c + BitVec.ofNat 32 oEp, 4⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) (sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil)
  · have e1 : sregions t ptrWg = wsT.flatMap (SR.rgns dsGeo c) := by
      simp [sregions, ptrWg, spW, M0Crypto.Sym.SExpr.denote, h13, wsT, SR.rgns, XLen.v, Loc.addr]
    rw [e1]
    refine Sub.refl _ fun r hr => ?_
    simp only [wsT, List.flatMap_cons, List.flatMap_nil, SR.rgns, XLen.v, Loc.addr] at hr
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hfr _ (by decide)
  · rw [execAll_append]
    have := ptr_all Rs (c := c) (u := execAll headA t) (ds := 2) (.inl rfl) (ep := aiP (wa.toInt.natAbs / 2))
      (bw := dsGeo.fsp c) (P := oAI + 128 * (wa.toInt.natAbs / 2)) (fun e => by simp [aiP, SV.val])
      (by simp only [oAI]; omega) (by rw [hA13, h13]) (by rw [hA0, hI, h13])
    rwa [hAm, hA13, show 4 * 2 = oDa from rfl, hI] at this
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩

/-- `DB`'s pointers' trace. -/
def pbTr (c : Ctx) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE headB1 (c.base + BitVec.ofNat 32 dsm_b_index) [.reg0 13] [dsGeo.fsp c]))
    (Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 dsm_b_table, .ldrLit 1 (BitVec.ofNat 8 48),
        [⟨.read, c.base + BitVec.ofNat 32 (litOff dsm_b_table (BitVec.ofNat 8 48)), 4⟩]⟩])
      (Tr.cat (Tr.is (blockTr [.addPc 1] (c.base + BitVec.ofNat 32 (dsm_b_table + 2)) [13] [dsGeo.fsp c]))
        (Tr.cat (Tr.is (blockTrE tailB (c.base + BitVec.ofNat 32 dsm_b_entry) [.reg0 13] [dsGeo.fsp c])) Ψ)))

/-- **`DB`'s pointers** at `dsm_b_index` from the digit word `wb`: the views of `signed_add` over
`odd_b[|δ| / 2]` with `δ`'s sign. -/
theorem ptrB_go (ads : ∀ a, Ad Rs B BS (dsS a)) (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc)
    (hcR : Sub [codeR c.base] Rc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : TrP} {wb : Word} {t : State} (hk : wb.toInt.natAbs / 2 < 8)
    (hb : E (.fr oDb) = .w wb) (hat : At Rs B c dsGeo m0 dsm_b_index E3 E t)
    (k : ∀ u, At Rs B c dsGeo m0 dsm_b_add (ext (sbSt (wb.toInt.natAbs / 2) (sgn wb.toInt)))
      (updOuts E (ptrΓ (obP (wb.toInt.natAbs / 2)) (sgn wb.toInt)) nones) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (pbTr c Ψ) := by
  have h13 := hat.2.1
  have hf := ext_facts E3 (by simp)
  have hI : read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDb) = wb := by
    rw [h13]; exact cw_view Rs m0 hat.2.2.2.2.1 hf.2.2.2.1 hb
  have hP := ptrB_ok.2.2.2.2.2.2 _ hk _ (sgn_lt wb.toInt)
  have hAs : ∀ v : State, v.regs 13 = dsGeo.fsp c → [SExpr.reg0 13].map (·.denote v) = [dsGeo.fsp c] :=
    fun v h => by simp only [List.map, M0Crypto.Sym.SExpr.denote, h]
  have hfr : ∀ o, o + 4 ≤ dsGeo.top → (dsGeo.fsp c + BitVec.ofNat 32 o).toNat + 4 ≤ 2 ^ 32 := fun o ho => by
    have := g.fr_toNat (Nat.le_of_add_right_le ho); have := c.sp0.isLt; have := g.room; have := g.top
    omega
  have hal : ∀ v : State, v.regs 13 = dsGeo.fsp c → ∀ r ∈ [(SExpr.reg0 13, 4)], (r.1.denote v).toNat % r.2 = 0 :=
    fun v h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      show (v.regs 13).toNat % 4 = 0; rw [h]; exact g.fsp4
  obtain ⟨hB0, -⟩ := headB1_run t
  have hB13 : (execAll headB1 t).regs 13 = t.regs 13 := (eff_run effs_ok.2.2.2.2.1 t).reg 13 (by decide) (by decide)
  unfold pbTr
  rw [← hAs t h13]
  refine wglue_run Rs m0 g F (ws := []) (outs := []) (vs := []) (σ := [(0, .k (96 * (wb.toInt.natAbs / 2))), (13, .sp 0)])
    ptrB_ok.1 ptrB_ok.2.1 cl.hb hat (hal t h13) ?_ (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => by simp [sregions] at h) (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_
    (fun hu hp2 => ?_)
  · have e : sregions t [(spW oDb, 4)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 oDb, 4⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil
  · intro h13' p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨show (0 : Nat) < 14 by decide, by rw [hB0, hI]; rfl⟩
    · exact ⟨by decide, by simpa [SV.val] using h13'⟩
  have e : dsm_b_index + seqSize headB1 = dsm_b_table := by decide
  rw [e] at hu hp2
  refine ld_run Rs ads m0 g F hcR (r := 1) (l := .C 5 0 48) (st := B1 (wb.toInt.natAbs / 2))
    (st' := B2 (wb.toInt.natAbs / 2)) rfl cl.lb hp2 hu (fun u hu' hp3 => ?_)
  have e2 : dsm_b_table + (Op.ld 1 (.C 5 0 48) : Op DS DB).size dsS dbS = dsm_b_entry := by decide
  rw [e2] at hu' hp3
  have hu13 := hu'.2.1
  have hσ := hu'.2.2.2.1
  have hr0 : u.regs 0 = BitVec.ofNat 32 (96 * (wb.toInt.natAbs / 2)) := (hσ (0, .k _) (by simp [B2, B1, glueSt])).2
  have hr1 : u.regs 1 = c.ptr 5 + BitVec.ofNat 32 0 := (hσ (1, .ext 5 0) (by simp [B2])).2
  have hIu : read32 u.mem (u.regs 13 + BitVec.ofNat 32 oDb) = wb := by
    rw [hu13]
    exact cw_view Rs m0 hu'.2.2.2.2.1 (by simpa [B2, B1, glueSt, keep_nil] using hf.2.2.2.1) hb
  have HA := eff_run ptrB_ok.2.2.2.2.1 u
  have hv0 : (execAll [.addReg 0 0 1] u).regs 0 = c.ptr 5 + BitVec.ofNat 32 (96 * (wb.toInt.natAbs / 2)) := by
    rw [HA.reg 0 (by decide) (by decide)]
    show u.regs 0 + u.regs 1 = _
    rw [hr0, hr1, BitVec.add_zero, BitVec.add_comm]
  have hv13 : (execAll [.addReg 0 0 1] u).regs 13 = u.regs 13 := HA.reg 13 (by decide) (by decide)
  have hvm : (execAll [.addReg 0 0 1] u).mem = u.mem := HA.mem _ rfl
  rw [hAs t h13, ← hAs u hu13]
  refine wglue_run Rs m0 g F (ws := wsT) (outs := ptrΓ (obP (wb.toInt.natAbs / 2)) (sgn wb.toInt)) (vs := nones)
    (σ := σsp) ptrB_ok.2.2.1 ptrB_ok.2.2.2.1 hp3 hu' (hal u hu13) ?_ ptrA_ok.2.2.1 ?_ hP.1 hP.2.1 ?_ ?_
    (fun hu2 _ => k _ (at_wk Rs m0 hu2 hP.2.2))
  · have e : sregions u [(spW oDb, 4), (spW oEp, 4)] =
        [⟨dsGeo.fsp c + BitVec.ofNat 32 oDb, 4⟩, ⟨dsGeo.fsp c + BitVec.ofNat 32 oEp, 4⟩] := by
      simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, hu13]
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) (sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil)
  · have e1 : sregions u ptrWg = wsT.flatMap (SR.rgns dsGeo c) := by
      simp [sregions, ptrWg, spW, M0Crypto.Sym.SExpr.denote, hu13, wsT, SR.rgns, XLen.v, Loc.addr]
    rw [e1]
    refine Sub.refl _ fun r hr => ?_
    simp only [wsT, List.flatMap_cons, List.flatMap_nil, SR.rgns, XLen.v, Loc.addr] at hr
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hfr _ (by decide)
  · rw [show tailB = [.addReg 0 0 1] ++ tailG 3 from rfl, execAll_append]
    have := ptr_all Rs (c := c) (u := execAll [.addReg 0 0 1] u) (ds := 3) (.inr rfl) (ep := obP (wb.toInt.natAbs / 2))
      (bw := c.ptr 5) (P := 96 * (wb.toInt.natAbs / 2)) (fun e => by simp [obP, SV.val])
      (by omega) (by rw [hv13, hu13]) hv0
    rwa [hvm, hv13, show 4 * 3 = oDb from rfl, hIu] at this
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩

/-- The index step's trace. -/
def decTr (c : Ctx) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE decG (c.base + BitVec.ofNat 32 dsm_dec_index) [.reg0 13] [dsGeo.fsp c]))
    (Tr.cat (Tr.is [bEv c dsm_jump_loop dsm_loop]) Ψ)

/-- **The index step** at `dsm_dec_index` with `I = x`, and back to the loop's test with `I = x − 1`. -/
theorem dec_go (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cl : CodeL B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : TrP} {x : Word} {t : State}
    (hx : E (.fr oI) = .w x) (hat : At Rs B c dsGeo m0 dsm_dec_index E1 E t)
    (k : ∀ u, At Rs B c dsGeo m0 dsm_loop LH (updOuts E [(.fr oI, .cw)] [.w (x - 1#32)]) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (decTr c Ψ) := by
  have h13 := hat.2.1
  have hf := ext_facts E1 (by simp)
  have hI : read32 t.mem (t.regs 13 + BitVec.ofNat 32 oI) = x := by
    rw [h13]; exact cw_view Rs m0 hat.2.2.2.2.1 hf.2.2.2.2 hx
  have hAs : [SExpr.reg0 13].map (·.denote t) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  have e1 : sregions t [(spW oI, 4)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 oI, 4⟩] := by
    simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
  unfold decTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := [⟨.fr oI, .k 4⟩]) (outs := [(.fr oI, .cw)]) (vs := [.w (x - 1#32)]) (σ := σsp)
    dec_ok.1 dec_ok.2.1 cl.dec hat ?_ ?_ ?_ ?_ ?_ (by simp) ?_ ?_ (fun hu hp2 => ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · rw [e1]; exact sub_cons' (g.frame_sub (by decide)) fun _ h => absurd h List.not_mem_nil
  · intro w hw
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨dec_ok.2.2.1, dec_ok.2.2.2.1⟩
  · rw [e1]
    have e2 : [(⟨.fr oI, .k 4⟩ : SR)].flatMap (SR.rgns dsGeo c) = [⟨dsGeo.fsp c + BitVec.ofNat 32 oI, 4⟩] := by
      simp [SR.rgns, XLen.v, Loc.addr]
    rw [e2]
    refine Sub.refl _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := g.fr_toNat (o := oI) (by decide); have := c.sp0.isLt; have := g.room; have := g.top
    simp only [dsGeo, oTop, oI] at *
    omega
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp
    exact dec_ok.2.2.2.2.1
  · refine ⟨?_, trivial⟩
    show read32 (execAll decG t).mem (dsGeo.fsp c + BitVec.ofNat 32 oI) = x - 1#32
    rw [dec_run, hI, h13, M0Crypto.Armv6M.read32_write32_same]
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : dsm_dec_index + seqSize decG = dsm_jump_loop := by decide
    rw [e] at hu hp2
    exact jmp_run Rs m0 g F cl.bj3 hp2 hu fun hX => k _ (at_wk Rs m0 hX dec_ok.2.2.2.2.2)

end run

end M0Crypto.Release.Ed25519DsmPass
