import M0Crypto.Release.Ed25519DsmLoop

/-!
# The body of `m0c_ge_dsm`

From the body's start at `0x2832` with the frame's state `stE` to the epilogue at `0x2d00`:
`segPre`, `movs r0, #255`, the top-digit scan, the store of `I`, `segId`, the loop and `segEnd`.
`body_go` ends with the views agreeing off the glue's words with the reference run
`preR ++ idR ++ runsR ++ endR`; its trace `bodyTr` is a function of the context, the digits'
zero tests and the digit words.
-/

namespace M0Crypto.Release.Ed25519DsmBody

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
open M0Crypto.Release.Ed25519DsmLoop
open M0Crypto.Release.Ed25519DsmVal (preR idR endR runsR)
open M0Crypto.Release.Ed25519DecompressOut (keeps run_keep)
open M0Crypto.Sym (SExpr)
open M0Crypto.Release.BlockEffect (Eff effOk eff_run)

/-! ## The glue around the scan -/

/-- The body's glue at its offsets, decided per build. -/
structure CodeB (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop where
  mv : piecesAt B 0x2a1e [.seq [.movImm 0 255]] = true
  st : piecesAt B 0x2a34 [.seq [.strSp 0 1]] = true

open M0Crypto.Release.Ed25519 (Build) in
theorem codeB_c : @CodeB _ _ Build.compact.codeBytes := by
  refine @CodeB.mk _ _ (Build.codeBytes _) ?_ ?_ <;>
    (try simp only [Build.bytes, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem codeB_f : @CodeB _ _ Build.fast.codeBytes := by
  refine @CodeB.mk _ _ (Build.codeBytes _) ?_ ?_ <;>
    (try simp only [Build.bytes, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem codeB_b : ∀ b : Build, @CodeB _ _ b.codeBytes
  | .compact => codeB_c
  | .fast => codeB_f

/-- The store of `I`. -/
def eSt : Eff := { mem := some (.w32 .mem0 (spW oI) (.reg0 0)), reads := [(spW oI, .reg0 0)] }

/-- After the store of `I`: the views of `s0` and `I`. -/
def SI : St := { rs s0 with Γ := (.fr oI, .cw) :: s0.Γ }

/-- The state after `segEnd`. -/
def Send : St := ((segEnd.lin dsS dbS dsGeo LH).map (·.2)).getD stE

theorem body_ok : sglueOk dsGeo.cs [.movImm 0 255] 0x2a1e dsGeo.top dsGeo.N [] [] [] = true ∧
    traceOkE [.movImm 0 255] [] = true ∧
    sglueOk dsGeo.cs [.strSp 0 1] 0x2a34 dsGeo.top dsGeo.N [(.reg0 13, 4)] [(spW oI, 4)] [] = true ∧
    traceOkE [.strSp 0 1] [.reg0 13] = true ∧ effOk [.strSp 0 1] eSt = true ∧
    (⟨.fr oI, .k 4⟩ : SR).ok dsGeo = true ∧ (⟨.fr oI, .k 4⟩ : SR).acc dsGeo true = true ∧
    (Kd.sr (.fr oI) .cw).ok dsGeo = true ∧ wkB (glueSt (stS 0) [⟨.fr oI, .k 4⟩] [(.fr oI, .cw)] σsp) SI = true ∧
    segOk segPre stE preR s0 = true ∧ segOk segId SI idR LH = true ∧ segOk segEnd LH endR Send = true ∧
    goodL idR = true ∧ goodL endR = true ∧ (0x2832, segPre) ∈ segs ∧ (0x2a36, segId) ∈ segs ∧
    (0x2cf6, segEnd) ∈ segs ∧ 0x2832 + segPre.size dsS dbS = 0x2a1e ∧ 0x2a36 + segId.size dsS dbS = 0x2a46 ∧
    0x2cf6 + segEnd.size dsS dbS = 0x2d00 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [segs], by simp [segs], by simp [segs],
    ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The loop's count -/

/-- The passes after the scan's result `j` (`I = j`, `−1` for none). -/
def nOf (j : Nat) : Nat := if j = 2 ^ 32 - 1 then 0 else j + 1

theorem topI_le (z : Nat → Bool) : ∀ j, topI z j ≤ j ∨ topI z j = 2 ^ 32 - 1
  | 0 => by unfold topI; split <;> simp
  | j + 1 => by
    unfold topI
    split
    · rcases topI_le z j with h | h
      · exact .inl (by omega)
      · exact .inr h
    · exact .inl (Nat.le_refl _)

theorem nOf_spec {j : Nat} (h : j ≤ 255 ∨ j = 2 ^ 32 - 1) :
    nOf j ≤ 256 ∧ BitVec.ofNat 32 j = BitVec.ofNat 32 (nOf j) - 1#32 := by
  unfold nOf
  split
  · rename_i hj; subst hj; exact ⟨by omega, by decide⟩
  · rename_i hj
    have := (small j (by omega)).1
    exact ⟨by omega, this.symm⟩

/-! ## The body's trace -/

section tr
variable (T : DS → Word → (Nat → Word) → List Event) (c : Ctx)

/-- `movs r0, #255`. -/
def mvTr (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE [.movImm 0 255] (c.base + BitVec.ofNat 32 0x2a1e) [] [])) Ψ

/-- The store of `I`. -/
def stTr (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE [.strSp 0 1] (c.base + BitVec.ofNat 32 0x2a34) [.reg0 13] [dsGeo.fsp c])) Ψ

/-- **The body's trace** with the digits' zero tests `z` and digit words `da`, `db`, then `Ψ` at
the epilogue. -/
def bodyTr (z : Nat → Bool) (da db : Nat → Word) (Ψ : TrP) : TrP :=
  pt T c segPre 0x2832 stE (mvTr c (scanTr (c := c) z
    (fun j => stTr c (pt T c segId 0x2a36 SI (lpTr T c da db (pt T c segEnd 0x2cf6 LH Ψ) (nOf j)))) 255))

end tr

/-! ## The body's run -/

section run
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {Wc Rc : List Rgn} (m0 : Mem)
variable (ads : ∀ a, Ad Rs B BS (dsS a)) (bds : ∀ b, Bd Rs (dbS b))
variable (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (hcR : Sub [codeR c.base] Rc)
  (cd : Code B BS) (cl : CodeL B BS) (cb : CodeB B BS)
include g F hcR cd cl cb

omit cl cb in
/-- **A straight line** from `S` with exact values: its end with the values of `L`. -/
theorem seg_ex {P : Prog DS DB} {o : Nat} (hP : (o, P) ∈ segs) {S S' : St} {L : List (ROp DS DB)}
    (hs : segOk P S L S' = true) {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hat : At Rs B c dsGeo m0 o S E t)
    (k : ∀ u, At Rs B c dsGeo m0 (o + P.size dsS dbS) S' (runA ads bds c m0 L E) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q (pt (TA ads) c P o S Ψ) := by
  unfold segOk at hs
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
  obtain ⟨hex, hs⟩ := hs
  split at hs
  · rename_i L' S1 hlin
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hs
    obtain ⟨⟨rfl, hex1⟩, hw⟩ := hs
    exact seg_run Rs m0 ads bds g F hcR cd hP hlin hex hex1 hw hat k
  · exact absurd hs (by simp)

/-- **The body** from `0x2832` with `stE` and the values `E`: to the epilogue at `0x2d00` with
views that agree off the glue's words with the reference run. -/
theorem body_go (hka : ∀ i < 256, (dv m0 c 2 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dv m0 c 2 i) < 2)
    (hkb : ∀ i < 256, (dv m0 c 1 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dv m0 c 1 i) < 8)
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP} (hat : At Rs B c dsGeo m0 0x2832 stE E t)
    (k : ∀ E' u, Agree N E' (runA ads bds c m0 (preR ++ idR ++
        runsR (fun i => (dv m0 c 2 i).toInt) (fun i => (dv m0 c 1 i).toInt) (nOf (topI (zd m0 c) 255)) ++ endR) E) →
      At Rs B c dsGeo m0 0x2d00 Send E' u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (bodyTr (TA ads) c (zd m0 c) (dv m0 c 2) (dv m0 c 1) Ψ) := by
  have bo := body_ok
  unfold bodyTr
  refine seg_ex Rs m0 ads bds g F hcR cd bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 bo.2.2.2.2.2.2.2.2.2.1 hat
    (fun u hu => ?_)
  rw [bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hu
  have hs0 := s0_ptrs
  -- `movs r0, #255`
  unfold mvTr
  refine wglue_run Rs m0 g F (al := []) (wg := []) (rg := []) (As := []) (ws := []) (outs := []) (vs := [])
    (σ := (stS 255).σ) bo.1 bo.2.1 cb.mv hu (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => by simp [sregions] at h) (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu2 _ => ?_)
  · intro h13' p hp
    simp only [stS, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨show (0 : Nat) < 14 by decide, by
        show (execAll [.movImm 0 255] u).regs 0 = BitVec.ofNat 32 255
        have e0 : LowReg.toReg 0 = 0 := rfl
        simp [execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, e0]⟩
    · exact ⟨by decide, by simpa [SV.val] using h13'⟩
  have e1 : 0x2a1e + seqSize [Instr.movImm 0 255] = 0x2a20 := by decide
  rw [e1] at hu2
  have hu3 : At Rs B c dsGeo m0 0x2a20 (stS 255) (runA ads bds c m0 preR E) (execAll [.movImm 0 255] u) :=
    at_weak Rs m0 hu2 (by simp [glueSt, keep_nil, stS, rs]) (by simp [glueSt, stS, rs]) (fun _ h => h)
      (by simp [stS, rs, hs0.2.2.2])
  -- the scan
  refine scan_loop Rs m0 g F cd 255 (by decide) _ hu3 (fun u4 hu4 => ?_)
  -- the store of `I`
  have hjr := nOf_spec ((topI_le (zd m0 c) 255).imp_left fun h => h)
  generalize topI (zd m0 c) 255 = j at hu4 hjr k ⊢
  have h13 := hu4.2.1
  have h0 : u4.regs 0 = BitVec.ofNat 32 j := (hu4.2.2.2.1 (0, .k j) (by simp [stS])).2
  have hAs : [SExpr.reg0 13].map (·.denote u4) = [dsGeo.fsp c] := by
    simp only [List.map, M0Crypto.Sym.SExpr.denote, h13]
  have e2 : sregions u4 [(spW oI, 4)] = [⟨dsGeo.fsp c + BitVec.ofNat 32 oI, 4⟩] := by
    simp only [sregions, spW, List.map, M0Crypto.Sym.SExpr.denote, h13]
  unfold stTr
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := [⟨.fr oI, .k 4⟩]) (outs := [(.fr oI, .cw)]) (vs := [.w (BitVec.ofNat 32 j)])
    (σ := σsp) bo.2.2.1 bo.2.2.2.1 cb.st hu4 ?_ (fun _ h => by simp [sregions] at h) ?_ ?_ ?_ (by simp) ?_ ?_
    (fun hu5 _ => ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show (u4.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
  · intro w hw
    simp only [List.mem_singleton] at hw; subst hw
    exact ⟨bo.2.2.2.2.2.1, bo.2.2.2.2.2.2.1⟩
  · rw [e2]
    have e3 : [(⟨.fr oI, .k 4⟩ : SR)].flatMap (SR.rgns dsGeo c) = [⟨dsGeo.fsp c + BitVec.ofNat 32 oI, 4⟩] := by
      simp [SR.rgns, XLen.v, Loc.addr]
    rw [e3]
    refine Sub.refl _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := g.fr_toNat (o := oI) (by decide); have := c.sp0.isLt; have := g.room; have := g.top
    simp only [dsGeo, oTop, oI] at *
    omega
  · intro p hp
    simp only [List.mem_singleton] at hp; subst hp
    exact bo.2.2.2.2.2.2.2.1
  · refine ⟨?_, trivial⟩
    have H := eff_run bo.2.2.2.2.1 u4
    have hr := H.rd (spW oI) (.reg0 0) (List.mem_cons_self ..)
    simp only [M0Crypto.Sym.SExpr.denote, spW, h13, h0] at hr
    simpa [Rel, Loc.addr] using hr
  · intro h13' p hp
    simp only [σsp, List.mem_singleton] at hp; subst hp
    exact ⟨by decide, by simpa [SV.val] using h13'⟩
  have e4 : 0x2a34 + seqSize [Instr.strSp 0 1] = 0x2a36 := by decide
  rw [e4] at hu5
  have hu6 := at_wk Rs m0 hu5 (by rw [show glueSt (stS j) [⟨.fr oI, .k 4⟩] [(.fr oI, .cw)] σsp =
    glueSt (stS 0) [⟨.fr oI, .k 4⟩] [(.fr oI, .cw)] σsp from rfl]; exact bo.2.2.2.2.2.2.2.2.1)
  -- `segId`
  refine seg_ex Rs m0 ads bds g F hcR cd bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 bo.2.2.2.2.2.2.2.2.2.2.1 hu6
    (fun u7 hu7 => ?_)
  rw [bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hu7
  -- the loop
  have hI : runA ads bds c m0 idR (updOuts (runA ads bds c m0 preR E) [(.fr oI, .cw)] [.w (BitVec.ofNat 32 j)])
      (.fr oI) = .w (BitVec.ofNat 32 (nOf j) - 1#32) := by
    have hk : ∀ r ∈ idR, keeps (.fr oI) r = true := by
      have := bo.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [goodL, Bool.and_eq_true, List.all_eq_true] at this
      exact this.2 _ (by simp [N])
    refine (run_keep _ _ hk).trans ?_
    rw [← hjr.2]; simp [updOuts]
  have hA : Agree N (runA ads bds c m0 idR (updOuts (runA ads bds c m0 preR E) [(.fr oI, .cw)] [.w (BitVec.ofNat 32 j)]))
      (runA ads bds c m0 idR (runA ads bds c m0 preR E)) := by
    have := bo.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [goodL, Bool.and_eq_true, List.all_eq_true] at this
    exact run_agree _ (agree_upd _ _ (by simp [N])) this.1
  refine loop_go Rs m0 ads bds g F hcR cd cl hka hkb (nOf j) hjr.1 _ _ u7 hA hI hu7 (fun E8 u8 hA8 hu8 => ?_)
  -- `segEnd`
  refine seg_ex Rs m0 ads bds g F hcR cd bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 bo.2.2.2.2.2.2.2.2.2.2.2.1 hu8
    (fun u9 hu9 => ?_)
  rw [bo.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at hu9
  refine k _ u9 ?_ hu9
  have hgE := bo.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [goodL, Bool.and_eq_true, List.all_eq_true] at hgE
  rw [runA_app, runA_app, runA_app]
  exact run_agree _ hA8 hgE.1

end run

end M0Crypto.Release.Ed25519DsmBody
