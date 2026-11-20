import M0Crypto.Release.Ed25519VerifyStitch

/-!
# `m0c_ed25519_verify`'s body from its sites

The decided code checks of the sites, in both builds, and the run of the body from the
spills to the leave through the sites' rules.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519VerifyBlocks (okG failG loadSD)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_verify)

/-- The condition of the `lt` test's exit: carry set, `s ≥ L`. -/
def CS : BitVec 4 := 2

/-! ## The layout -/

/-- **The sites follow each other**: each starts where the previous one and its test end. -/
theorem sites_at :
    oP0 + p0.size vpS vbS = oC0 ∧
    oC0 + (c0 : Op VX VB).size vxS vbS + seqSize [.cmpImm 0 0] + 4 = oR ∧
    oR + (checkR : Op VX VB).size vxS vbS + seqSize [.cmpImm 0 0] + 4 = oP2 ∧
    oP2 + p2.size vpS vbS = oB2 ∧
    oB2 + (b2 : Op VX VB).size vxS vbS + seqSize [] + 4 = oP3 ∧
    oP3 + p3.size vpS vbS = oW5 ∧
    oW5 + (w5 : Op VX VB).size vxS vbS = oW3 ∧
    oW3 + (w3 : Op VX VB).size vxS vbS = oDm ∧
    oDm + (dm : Op VX VB).size vxS vbS = oEncode ∧
    oEncode + encode.size vpS vbS = oCompare ∧
    oCompare + (compare : Op VX VB).size vxS vbS + seqSize [.cmpImm 0 0] + 4 = oOk ∧
    oOk + seqSize okG + 2 = oFail ∧ oFail + seqSize failG = oLeave ∧
    bodyAt verifyGeo ed25519_verify = oP0 ∧ oP0 + verifyBodyBytes = oLeave := by
  decide +kernel

/-! ## The code checks, both builds -/

section
variable (b : Build)

/-- The checks of the straight lines. -/
def linesChk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop :=
  (p0.bok vpS vbS verifyGeo [] oP0 = true ∧ piecesAt B oP0 (Prog.emit vpS vbS [] oP0 p0 ++ []) = true) ∧
  (p2.bok vpS vbS verifyGeo [] oP2 = true ∧ piecesAt B oP2 (Prog.emit vpS vbS [] oP2 p2 ++ []) = true) ∧
  (p3.bok vpS vbS verifyGeo [] oP3 = true ∧ piecesAt B oP3 (Prog.emit vpS vbS [] oP3 p3 ++ []) = true) ∧
  (encode.bok vpS vbS verifyGeo [] oEncode = true ∧ piecesAt B oEncode (Prog.emit vpS vbS [] oEncode encode ++ []) = true)

theorem lines_code : @linesChk b.bytes b.size b.codeBytes := by
  cases b <;> (simp only [linesChk, piecesAt_eq_scan]; decide +kernel)

/-- The checks of a status site `x` at `o`: the call, `cmp r0, #0` and the exit to `oFail`. -/
def zChk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] (x : Op VX VB) (o : Nat) : Prop :=
  x.bok vxS vbS verifyGeo o = true ∧
  (Op.pub [.cmpImm 0 0] : Op VX VB).bok vxS vbS verifyGeo (o + x.size vxS vbS) = true ∧
  brOk (B := B) verifyGeo false (o + x.size vxS vbS + seqSize [.cmpImm 0 0]) oFail = true ∧
  piecesAt B o (x.pieces vxS vbS ++ (.seq [.cmpImm 0 0] ::
    xitBr NE false (o + x.size vxS vbS + seqSize [.cmpImm 0 0]) oFail ++ [])) = true

theorem sites_code : @zChk b.bytes b.size b.codeBytes c0 oC0 ∧
    @zChk b.bytes b.size b.codeBytes checkR oR ∧
    @zChk b.bytes b.size b.codeBytes compare oCompare := by
  cases b <;> (simp only [zChk, piecesAt_eq_scan]; decide +kernel)

/-- The checks of the `lt` block at `oB2`, its test and the exit to `oFail`. -/
def ltChk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop :=
  (b2 : Op VX VB).bok vxS vbS verifyGeo oB2 = true ∧
  (Op.pub [] : Op VX VB).bok vxS vbS verifyGeo (oB2 + b2.size vxS vbS) = true ∧
  brOk (B := B) verifyGeo false (oB2 + b2.size vxS vbS + seqSize []) oFail = true ∧
  piecesAt B oB2 (b2.pieces vxS vbS ++ (.seq [] ::
    xitBr CS false (oB2 + b2.size vxS vbS + seqSize []) oFail ++ [])) = true

/-- The checks of a call whose trace depends on memory. -/
def xChk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] (x : Op VX VB) (o : Nat) : Prop :=
  x.bok vxS vbS verifyGeo o = true ∧ piecesAt B o (x.pieces vxS vbS ++ []) = true

/-- The checks of the verdict blocks, the `b` to the leave, the leave and the entry. -/
def tailChk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop :=
  (Op.pub okG : Op VX VB).bok vxS vbS verifyGeo oOk = true ∧ piecesAt B oOk [.seq okG] = true ∧
  bOk (B := B) verifyGeo.cs (oOk + seqSize okG) oLeave = true ∧
  seqAt B (oOk + seqSize okG) [.b (brImm11 (oOk + seqSize okG) oLeave)] = true ∧
  (Op.pub failG : Op VX VB).bok vxS vbS verifyGeo oFail = true ∧ piecesAt B oFail [.seq failG] = true ∧
  piecesAt B oLeave (abiLeaveP verifyGeo.top) = true

theorem lt_code : @ltChk b.bytes b.size b.codeBytes := by
  cases b <;> (simp only [ltChk, piecesAt_eq_scan]; decide +kernel)

theorem xsites_code : @xChk b.bytes b.size b.codeBytes w5 oW5 ∧ @xChk b.bytes b.size b.codeBytes w3 oW3 ∧
    @xChk b.bytes b.size b.codeBytes dm oDm := by
  cases b <;> (simp only [xChk, piecesAt_eq_scan]; decide +kernel)

theorem tail_code : @tailChk b.bytes b.size b.codeBytes := by
  cases b <;> (simp only [tailChk, piecesAt_eq_scan, seqAt_eq_scan]; decide +kernel)

theorem verify_entryOk : entryOkP verifyGeo verifyBodyBytes ed25519_verify = true := by decide +kernel

end

/-! ## The static facts the run uses -/

theorem starts_ex : vR.ex = none ∧ (addViews v4 l2).ex = none ∧ v8.ex = none := by decide +kernel

theorem ends_X : v1.X = [] ∧ vR.X = [] ∧ v4.X = [] ∧ v10.X = [] := by decide +kernel

/-! ## The adapters -/

section
variable (Rs : Rels) (B : List (BitVec 8)) (BS : Nat) [cb : CodeBytes B BS]

/-- **The adapters of the body**: the straight lines' callees, the `lt` block with its test,
`ge_decompress` and exact byte comparison with their status, `sc_wnaf` at both widths and `ge_dsm`. -/
structure VAd where
  ap : ∀ a, Ad Rs B BS (vpS a)
  apE : ∀ a base p, (vpS a).Eff p base ((ap a).T base p)
  lt : Bd Rs (vbS .lt)
  zl : ZB Rs lt
  zl_cc : zl.cc = CS
  zl_co : zl.co = ltCo
  dc : AdX Rs (cb := cb) (vxS .dec)
  zd : ZSt Rs dc
  zd_co : zd.co = decCo
  rc : AdX Rs (cb := cb) (vxS .checkR)
  zr : ZSt Rs rc
  zr_co : zr.co = []
  w5 : AdX Rs (cb := cb) (vxS (.wnaf 5))
  w3 : AdX Rs (cb := cb) (vxS (.wnaf 3))
  dm : AdX Rs (cb := cb) (vxS .dsm)
  cmp : AdX Rs (cb := cb) (vxS .compare)
  zc : ZSt Rs cmp
  zc_co : zc.co = []

variable {Rs B BS}

/-- The blocks' adapters. -/
def VAd.bds (D : VAd Rs B BS) : ∀ b, Bd Rs (vbS b)
  | .loadS => loadSD Rs
  | .lt => D.lt

/-! ## The values along the body -/

namespace VAd
variable (D : VAd Rs B BS) (c : Ctx) (m0 : Mem)

/-- The values after the spills. -/
def E1 : Loc → V := Prog.ev vpS vbS verifyGeo (fun a => (D.ap a).sem) (fun b => (D.bds b).sem) c m0 p0 stE
  fun _ => .none
/-- `A`'s input values, its status, and the values after it. -/
def i0 : List V := ioVs verifyGeo c m0 v0 (regsOf v0.Γ v0.σ aC0) (vxS .dec).io (D.E1 c m0)
def d0 : Bool := D.zd.ok (D.i0 c m0)
def E2 : Loc → V := updOuts (xcallEv verifyGeo c m0 v0 (regsOf v0.Γ v0.σ aC0) (vxS .dec).io D.dc.sem (D.E1 c m0))
  l0 (D.zd.csem (D.i0 c m0))
/-- The early R check reads the signature's first 32 bytes. -/
def iR : List V := ioVs verifyGeo c m0 (addViews v1 l0)
  (regsOf (addViews v1 l0).Γ (addViews v1 l0).σ aR) (vxS .checkR).io (D.E2 c m0)
def dR : Bool := D.zr.ok (D.iR c m0)
def ER : Loc → V := updOuts (xcallEv verifyGeo c m0 (addViews v1 l0)
  (regsOf (addViews v1 l0).Γ (addViews v1 l0).σ aR) (vxS .checkR).io D.rc.sem (D.E2 c m0))
  [] (D.zr.csem (D.iR c m0))
/-- `s` and the operands of `lt`, its status and the values after it. -/
def E4 : Loc → V := Prog.ev vpS vbS verifyGeo (fun a => (D.ap a).sem) (fun b => (D.bds b).sem) c m0 p2
  vR (D.ER c m0)
def i2 : List V := ioVs verifyGeo c m0 v3 (regsOf v3.Γ v3.σ []) (vbS .lt).io (D.E4 c m0)
def d2 : Bool := D.zl.ok (D.i2 c m0)
def E5 : Loc → V := updOuts ((b2 : Op VX VB).ev vxS vbS verifyGeo (fun _ _ => []) (fun _ => D.lt.sem) c m0 v3
  (D.E4 c m0)) l2 (D.zl.csem (D.i2 c m0))
/-- `h`, then the digits and the double multiplication. -/
def E6 : Loc → V := Prog.ev vpS vbS verifyGeo (fun a => (D.ap a).sem) (fun b => (D.bds b).sem) c m0 p3
  (addViews v4 l2) (D.E5 c m0)
def i5 : List V := ioVs verifyGeo c m0 v5 (regsOf v5.Γ v5.σ aW5) (vxS (.wnaf 5)).io (D.E6 c m0)
def E7 : Loc → V := xcallEv verifyGeo c m0 v5 (regsOf v5.Γ v5.σ aW5) (vxS (.wnaf 5)).io D.w5.sem (D.E6 c m0)
def i6 : List V := ioVs verifyGeo c m0 v6 (regsOf v6.Γ v6.σ aW3) (vxS (.wnaf 3)).io (D.E7 c m0)
def E8 : Loc → V := xcallEv verifyGeo c m0 v6 (regsOf v6.Γ v6.σ aW3) (vxS (.wnaf 3)).io D.w3.sem (D.E7 c m0)
def i7 : List V := ioVs verifyGeo c m0 v7 (regsOf v7.Γ v7.σ aDm) (vxS .dsm).io (D.E8 c m0)
def E9 : Loc → V := xcallEv verifyGeo c m0 v7 (regsOf v7.Γ v7.σ aDm) (vxS .dsm).io D.dm.sem (D.E8 c m0)
/-- Compress the projective result and compare its encoding with raw R. -/
def E10 : Loc → V := Prog.ev vpS vbS verifyGeo (fun a => (D.ap a).sem) (fun b => (D.bds b).sem) c m0 encode v8
  (D.E9 c m0)
def i9 : List V := ioVs verifyGeo c m0 v9 (regsOf v9.Γ v9.σ aCompare) (vxS .compare).io (D.E10 c m0)
def d3 : Bool := D.zc.ok (D.i9 c m0)

/-- **The verdict of the tests**. -/
def ok : Bool := D.d0 c m0 && D.dR c m0 && D.d2 c m0 && D.d3 c m0

/-! ## The public values of the stitched calls -/

def P0 : Nat → Word := xcallPub verifyGeo c v0 aC0 (vxS .dec) (D.dc.xpv (D.i0 c m0))
def PR : Nat → Word := xcallPub verifyGeo c (addViews v1 l0) aR (vxS .checkR) (D.rc.xpv (D.iR c m0))
def P5 : Nat → Word := xcallPub verifyGeo c v5 aW5 (vxS (.wnaf 5)) (D.w5.xpv (D.i5 c m0))
def P6 : Nat → Word := xcallPub verifyGeo c v6 aW3 (vxS (.wnaf 3)) (D.w3.xpv (D.i6 c m0))
def P7 : Nat → Word := xcallPub verifyGeo c v7 aDm (vxS .dsm) (D.dm.xpv (D.i7 c m0))
def P9 : Nat → Word := xcallPub verifyGeo c v9 aCompare (vxS .compare) (D.cmp.xpv (D.i9 c m0))

/-- **The premises of the callees' effects** at the calls the passing tests reach, and the status
tests as functions of the public values. -/
def pubOk : Prop :=
  (D.dc.ppre (D.P0 c m0) ∧ D.zd.okp (D.P0 c m0) = D.d0 c m0) ∧
  (D.d0 c m0 = true →
    (D.rc.ppre (D.PR c m0) ∧ D.zr.okp (D.PR c m0) = D.dR c m0) ∧
    (D.dR c m0 = true → D.d2 c m0 = true →
    D.w5.ppre (D.P5 c m0) ∧ D.w3.ppre (D.P6 c m0) ∧ D.dm.ppre (D.P7 c m0) ∧
    (D.cmp.ppre (D.P9 c m0) ∧ D.zc.okp (D.P9 c m0) = D.d3 c m0)))

/-! ## The trace of the body -/

/-- After a failed test: `failG`. -/
def tFail : TrP := Tr.cat (Tr.is (blockTr failG (c.base + BitVec.ofNat 32 oFail) [13] [verifyGeo.fsp c])) (Tr.is [])

/-- After the last test passes: `okG`, then `b` to the leave. -/
def tOk : TrP := Tr.cat (Tr.is (blockTr okG (c.base + BitVec.ofNat 32 oOk) [13] [verifyGeo.fsp c]))
  (Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 (oOk + seqSize okG), .b (brImm11 (oOk + seqSize okG) oLeave), []⟩])
    (Tr.is []))

def tCompare : TrP := xcallTr verifyGeo c oCompare aCompare (vxS .compare).entry
  (D.cmp.T c.base (D.P9 c m0))
  (tstTr verifyGeo c (oCompare + (compare : Op VX VB).size vxS vbS) [.cmpImm 0 0] NE oFail (D.d3 c m0) (tOk c) (tFail c))
def tEncode : TrP := Prog.tr vpS vbS verifyGeo (fun a => (D.ap a).T) c encode oEncode v8 (D.tCompare c m0) [] []
def tDm : TrP := xcallTr verifyGeo c oDm aDm (vxS .dsm).entry
  (D.dm.T c.base (D.P7 c m0)) (D.tEncode c m0)
def tW3 : TrP := xcallTr verifyGeo c oW3 aW3 (vxS (.wnaf 3)).entry
  (D.w3.T c.base (D.P6 c m0)) (D.tDm c m0)
def tW5 : TrP := xcallTr verifyGeo c oW5 aW5 (vxS (.wnaf 5)).entry
  (D.w5.T c.base (D.P5 c m0)) (D.tW3 c m0)
def tP3 : TrP := Prog.tr vpS vbS verifyGeo (fun a => (D.ap a).T) c p3 oP3 (addViews v4 l2) (D.tW5 c m0) [] []
def tB2 : TrP := (b2 : Op VX VB).tr vxS vbS verifyGeo (fun _ _ _ => []) c oB2 v3
  (tstTr verifyGeo c (oB2 + (b2 : Op VX VB).size vxS vbS) [] D.zl.cc oFail (D.d2 c m0) (D.tP3 c m0) (tFail c))
def tP2 : TrP := Prog.tr vpS vbS verifyGeo (fun a => (D.ap a).T) c p2 oP2 vR (D.tB2 c m0) [] []
def tR : TrP := xcallTr verifyGeo c oR aR (vxS .checkR).entry
  (D.rc.T c.base (D.PR c m0))
  (tstTr verifyGeo c (oR + (checkR : Op VX VB).size vxS vbS) [.cmpImm 0 0] NE oFail (D.dR c m0) (D.tP2 c m0) (tFail c))
def tC0 : TrP := xcallTr verifyGeo c oC0 aC0 (vxS .dec).entry
  (D.dc.T c.base (D.P0 c m0))
  (tstTr verifyGeo c (oC0 + (c0 : Op VX VB).size vxS vbS) [.cmpImm 0 0] NE oFail (D.d0 c m0) (D.tR c m0) (tFail c))
/-- **The trace of the body**. -/
def bodyTr : TrP := Prog.tr vpS vbS verifyGeo (fun a => (D.ap a).T) c p0 oP0 stE (D.tC0 c m0) [] []

end VAd

end

/-! ## The run -/

/-- **The body's end**: at the leave, `sp` at the frame, the memory outside the window as on
entry, the verdict `ok` in `r0`, and the facts `H` the run establishes. -/
def QB (c : Ctx) (m0 : Mem) (ok : Bool) (H : Prop) (u : State) : Prop :=
  u.pc = c.base + BitVec.ofNat 32 oLeave ∧ u.regs 13 = verifyGeo.fsp c ∧
  (∀ y, ¬ (verifyGeo.win c).Has y → u.mem y = m0 y) ∧ (u.regs 0 = if ok then 0#32 else 0xffffffff#32) ∧ H

section run
variable {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {Wc Rc : List Rgn} {m0 : Mem}

theorem addViews_X (st : St) (cl : List (Loc × Kd)) : (addViews st cl).X = st.X := rfl

theorem atMv {o o' : Nat} {st : St} {E : Loc → V} {t : State} (h : o = o') (hu : At Rs B c verifyGeo m0 o st E t) :
    At Rs B c verifyGeo m0 o' st E t := h ▸ hu

/-- **A register-only block** of the body: its run leaves the memory. -/
theorem vglue_run (g : GeoOk c verifyGeo Wc Rc) (F : Caller c.base c.sp0 verifyGeo.N Wc) {gs : List Instr}
    {o : Nat} {st : St} {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hbok : (Op.pub gs : Op VX VB).bok vxS vbS verifyGeo o = true) (hp : piecesAt B o [.seq gs] = true)
    (hat : At Rs B c verifyGeo m0 o st E t)
    (k : (execAll gs t).pc = c.base + BitVec.ofNat 32 (o + seqSize gs) → (execAll gs t).regs 13 = verifyGeo.fsp c →
      (execAll gs t).mem = t.mem →
      ReachFT c.base (PcIn c.base verifyGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 verifyGeo.N) (execAll gs t) Q Ψ) :
    ReachFT c.base (PcIn c.base verifyGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 verifyGeo.N) t Q
      (Tr.cat (Tr.is (blockTr gs (c.base + BitVec.ofNat 32 o) [13] [verifyGeo.fsp c])) Ψ) :=
  pubB_run Rs m0 g F hbok hp hat fun hpc h13 hm _ => k hpc h13 hm

/-- **A failed test's end**: `failG` falls into the leave with `r0 = −1`. -/
theorem fail_tail (g : GeoOk c verifyGeo Wc Rc) (F : Caller c.base c.sp0 verifyGeo.N Wc) (htl : tailChk B BS)
    {st : St} {E : Loc → V} {t : State} {ok : Bool} {H : Prop} (hat : At Rs B c verifyGeo m0 oFail st E t)
    (hX : st.X = []) (hok : ok = false) (hH : H) :
    ReachFT c.base (PcIn c.base verifyGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 verifyGeo.N) t
      (QB c m0 ok H) (VAd.tFail c) := by
  have hi := hat.2.2.2.2.1
  refine vglue_run g F htl.2.2.2.2.1 htl.2.2.2.2.2.1 hat fun hpc h13 hm => ReachT.done ⟨?_, h13, fun y hy => ?_, ?_, hH⟩
  · rw [hpc]; rfl
  · rw [hm]; exact hi.2.1 y hy (by simp [hX])
  · rw [hok, Ed25519VerifyBlocks.fail_r0]; rfl

/-- **The passing end**: `okG`, then `b` to the leave, with `r0 = 0`. -/
theorem ok_tail (g : GeoOk c verifyGeo Wc Rc) (F : Caller c.base c.sp0 verifyGeo.N Wc) (htl : tailChk B BS)
    {st : St} {E : Loc → V} {t : State} {ok : Bool} {H : Prop} (hat : At Rs B c verifyGeo m0 oOk st E t)
    (hX : st.X = []) (hok : ok = true) (hH : H) :
    ReachFT c.base (PcIn c.base verifyGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 verifyGeo.N) t
      (QB c m0 ok H) (VAd.tOk c) := by
  have hi := hat.2.2.2.2.1
  refine vglue_run g F htl.1 htl.2.1 hat fun hpc h13 hm => ?_
  refine b_run F htl.2.2.1 htl.2.2.2.1 hpc h13 g.top (ReachT.done ⟨?_, ?_, fun y hy => ?_, ?_, hH⟩)
  · simp [State.pc, State.setReg]
  · simpa [State.setReg] using h13
  · simp only [State.setReg]; rw [hm]; exact hi.2.1 y hy (by simp [hX])
  · simp only [State.setReg, hok]; exact Ed25519VerifyBlocks.ok_r0 t

/-- **The body runs** from the spills to the leave with the verdict of its tests, given the
callees' premises on the input values of each site that the passing tests reach. -/
theorem body_run (D : VAd Rs B BS) (g : GeoOk c verifyGeo Wc Rc) (F : Caller c.base c.sp0 verifyGeo.N Wc)
    (hcR : Sub [codeR c.base] Rc) (hln : linesChk B BS)
    (hs : zChk B BS c0 oC0 ∧ zChk B BS checkR oR ∧ zChk B BS compare oCompare) (hlt : ltChk B BS)
    (hx : xChk B BS w5 oW5 ∧ xChk B BS w3 oW3 ∧ xChk B BS dm oDm) (htl : tailChk B BS)
    (hv0 : D.dc.vpre (D.i0 c m0))
    (hvR : D.d0 c m0 = true → D.rc.vpre (D.iR c m0))
    (hv2 : D.d0 c m0 = true → D.zl.vpre (D.i2 c m0))
    (hv5 : D.d0 c m0 = true → D.d2 c m0 = true → D.w5.vpre (D.i5 c m0))
    (hv6 : D.d0 c m0 = true → D.d2 c m0 = true → D.w3.vpre (D.i6 c m0))
    (hv7 : D.d0 c m0 = true → D.d2 c m0 = true → D.dm.vpre (D.i7 c m0))
    (hv9 : D.d0 c m0 = true → D.d2 c m0 = true → D.cmp.vpre (D.i9 c m0))
    {t : State} (hat : At Rs B c verifyGeo m0 oP0 stE (fun _ => .none) t) :
    ReachFT c.base (PcIn c.base verifyGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 verifyGeo.N) t
      (QB c m0 (D.ok c m0) (D.pubOk c m0)) (D.bodyTr c m0) := by
  obtain ⟨⟨hb0, hp0⟩, ⟨hb2, hp2⟩, ⟨hb3, hp3⟩, ⟨hbEnc, hpEnc⟩⟩ := hln
  obtain ⟨zc0, zr, zcmp⟩ := hs
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hlt
  obtain ⟨⟨hw5b, hw5p⟩, ⟨hw3b, hw3p⟩, ⟨hdmb, hdmp⟩⟩ := hx
  obtain ⟨t0, t0x, -, t1, -, t1r, t1o, -, t3, t3x, -, t4, -, t4r, t4o, -, t5, t5x, -,
    t6, -, t7, -, t8, -, t9, t9x, -, t10, -⟩ := sites_ty
  obtain ⟨sx2, sx4, sx8⟩ := starts_ex
  obtain ⟨X1, XR, X4, X10⟩ := ends_X
  refine prog_run Rs D.ap D.bds m0 g F hcR p0 t0 rfl hb0 hp0 hat (fun _ u0 hu0 _ => ?_)
    (fun l hl => by rw [t0x] at hl; cases hl)
  refine zcall_run Rs m0 g F hcR D.zd (cl := l0) (d := D.d0 c m0) t1 zc0.1 zc0.2.1 zc0.2.2.1 zc0.2.2.2
    (atMv (by decide +kernel) hu0) hv0 (by rw [D.zd_co]; exact t1r) t1o rfl (fun hd0 hk0 u1 hu1 _ => ?_)
    (fun hd0 hk0 u hu => fail_tail g F htl hu (by dsimp only; exact X1) (by simp [VAd.ok, hd0])
      ⟨hk0, fun h => absurd h (by simp [hd0])⟩)
  refine zcall_run Rs m0 g F hcR D.zr (cl := []) (d := D.dR c m0) checkR_ty.1
    zr.1 zr.2.1 zr.2.2.1 zr.2.2.2 (atMv (by decide +kernel) hu1) (hvR hd0)
    (by rw [D.zr_co]; rfl) (by decide) rfl
    (fun hdR hkR uR huR _ => ?_)
    (fun hdR hkR _ hu => fail_tail g F htl hu (by dsimp only; exact XR) (by simp [VAd.ok, hdR])
      ⟨hk0, fun _ => ⟨hkR, fun h _ => absurd h (by simp [hdR])⟩⟩)
  refine prog_run Rs D.ap D.bds m0 g F hcR p2 t3 sx2 hb2 hp2 (atMv (by decide +kernel) huR) (fun _ u3 hu3 _ => ?_)
    (fun l hl => by rw [t3x] at hl; cases hl)
  refine zblk_run Rs m0 g F (semA := fun _ _ => []) (T' := fun _ _ _ => []) D.zl (cl := l2) (d := D.d2 c m0)
    (by rw [D.zl_cc]; decide) t4 hl1 hl2 hl3 (by rw [D.zl_cc]; exact hl4) (atMv (by decide +kernel) hu3)
    (by rw [D.zl_co]; exact t4r) t4o rfl (hv2 hd0) (fun hd2 u4 hu4 _ => ?_)
    (fun hd2 u hu => fail_tail g F htl hu (by dsimp only; exact X4) (by simp [VAd.ok, hd2])
      ⟨hk0, fun _ => ⟨hkR, fun _ h => absurd h (by simp [hd2])⟩⟩)
  refine prog_run Rs D.ap D.bds m0 g F hcR p3 t5 sx4 hb3 hp3 (atMv (by decide +kernel) hu4) (fun _ u5 hu5 _ => ?_)
    (fun l hl => by rw [t5x] at hl; cases hl)
  refine xcall_run Rs m0 g F hcR D.w5 t6 hw5b hw5p (atMv (by decide +kernel) hu5) (hv5 hd0 hd2)
    (fun u6 hu6 ⟨s5, _, hpr5, hpv5, hin5, _, hpx5⟩ _ => ?_)
  have f5 : D.w5.ppre (D.P5 c m0) := by
    have h := D.w5.ppre_of c _ s5 _ hpr5 hpv5 hin5 (hv5 hd0 hd2); rw [hpx5] at h; exact h
  refine xcall_run Rs m0 g F hcR D.w3 t7 hw3b hw3p (atMv (by decide +kernel) hu6) (hv6 hd0 hd2)
    (fun u7 hu7 ⟨s6, _, hpr6, hpv6, hin6, _, hpx6⟩ _ => ?_)
  have f6 : D.w3.ppre (D.P6 c m0) := by
    have h := D.w3.ppre_of c _ s6 _ hpr6 hpv6 hin6 (hv6 hd0 hd2); rw [hpx6] at h; exact h
  refine xcall_run Rs m0 g F hcR D.dm t8 hdmb hdmp (atMv (by decide +kernel) hu7) (hv7 hd0 hd2)
    (fun u8 hu8 ⟨s7, _, hpr7, hpv7, hin7, _, hpx7⟩ _ => ?_)
  have f7 : D.dm.ppre (D.P7 c m0) := by
    have h := D.dm.ppre_of c _ s7 _ hpr7 hpv7 hin7 (hv7 hd0 hd2); rw [hpx7] at h; exact h
  refine prog_run Rs D.ap D.bds m0 g F hcR encode t9 sx8 hbEnc hpEnc
    (atMv (by decide +kernel) hu8) (fun _ u9 hu9 _ => ?_) (fun l hl => by rw [t9x] at hl; cases hl)
  exact zcall_run Rs m0 g F hcR D.zc (cl := []) (d := D.d3 c m0) t10
    zcmp.1 zcmp.2.1 zcmp.2.2.1 zcmp.2.2.2 (atMv (by decide +kernel) hu9) (hv9 hd0 hd2)
    (by rw [D.zc_co]; rfl) (by decide) rfl
    (fun hd3 hk3 u10 hu10 _ => ok_tail g F htl (atMv (by decide +kernel) hu10) (by rw [addViews_X]; exact X10)
      (by simp [VAd.ok, hd0, hdR, hd2, hd3]) ⟨hk0, fun _ => ⟨hkR, fun _ _ => ⟨f5, f6, f7, hk3⟩⟩⟩)
    (fun hd3 hk3 _ hu => fail_tail g F htl hu (by dsimp only; exact X10) (by simp [VAd.ok, hd3])
      ⟨hk0, fun _ => ⟨hkR, fun _ _ => ⟨f5, f6, f7, hk3⟩⟩⟩)

end run

/-! ## The effect -/

theorem withViews_nil (st : St) : withViews st [] = st := by
  cases st; simp [withViews]

section good
variable {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {m0 : Mem} {sp0 : Word} {n : Nat}
  {X0 : Word → Prop}

theorem fail_gp (fm : Frm c verifyGeo sp0 n X0) {st : St} (hk : blkChk (pwIni st.Γ) [] [frR verifyGeo] failG = true) :
    GP sp0 n (BI c verifyGeo sp0 n X0 st) (VAd.tFail c) (SIR sp0 (verifyGeo.fsp c) X0) :=
  GP.cat (pubBlk_gp fm hk _) (GP.nil fun _ h => ⟨h.sp, h.sv, h.ab⟩)

theorem ok_gp (fm : Frm c verifyGeo sp0 n X0) {st : St} (hk : blkChk (pwIni st.Γ) [] [frR verifyGeo] okG = true) :
    GP sp0 n (BI c verifyGeo sp0 n X0 st) (VAd.tOk c) (SIR sp0 (verifyGeo.fsp c) X0) :=
  GP.cat (pubBlk_gp fm hk _) (GP.cat (quiet_gp rfl rfl rfl) (GP.nil fun _ h => ⟨h.sp, h.sv, h.ab⟩))

/-- **The body's trace keeps its invariant** to the leave, given the premises of the callees'
effects that the run establishes. -/
theorem body_good (D : VAd Rs B BS) (fm : Frm c verifyGeo sp0 n X0)
    (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (verifyGeo.fsp c) y ∧ X0 y)
    (hln : linesChk B BS) (hP : D.pubOk c m0) :
    GP sp0 n (BI c verifyGeo sp0 n X0 stE) (D.bodyTr c m0) (SIR sp0 (verifyGeo.fsp c) X0) := by
  obtain ⟨⟨hb0, -⟩, ⟨hb2, -⟩, ⟨hb3, -⟩, ⟨hbEnc, -⟩⟩ := hln
  obtain ⟨t0, t0x, e0, t1, e1, t1r, -, ce, t3, t3x, e3, t4, e4, -, -, hcov, t5, t5x, e5,
    t6, e6, t7, e7, t8, e8, t9, t9x, e9, t10, e10⟩ := sites_ty
  obtain ⟨sx2, sx4, sx8⟩ := starts_ex
  obtain ⟨⟨hpp0, hok0⟩, hP⟩ := hP
  refine prog_good fm D.apE hcode p0 oP0 stE v0 _ _ [] [] t0 rfl e0 hb0 (fun _ => ?_)
    (fun l hl => by rw [t0x] at hl; cases hl)
  refine zcall_gp fm hcode D.zd t1 e1 (by rw [D.zd_co]; exact t1r) (by rw [D.zd_co]; exact ce) hpp0 hok0
    (fun hd0 => ?_) (fun _ => fail_gp fm (by decide +kernel))
  obtain ⟨⟨hppR, hokR⟩, hP'⟩ := hP hd0
  refine zcall_gp fm hcode D.zr checkR_ty.1 checkR_ty.2
    (by rw [D.zr_co]; rfl) (by rw [D.zr_co]; rfl) hppR hokR
    (fun hdR => ?_) (fun _ => fail_gp fm (by decide +kernel))
  refine prog_good fm D.apE hcode p2 oP2 vR v3 _ _ [] [] t3 sx2 e3 hb2 (fun _ => ?_)
    (fun l hl => by rw [t3x] at hl; cases hl)
  refine zblk_gp fm t4 e4 hcov (fun hd2 => ?_) (fun _ => fail_gp fm (by decide +kernel))
  obtain ⟨f5, f6, f7, hpp9, hok9⟩ := hP' hdR hd2
  refine prog_good fm D.apE hcode p3 oP3 (addViews v4 l2) v5 _ _ [] [] t5 sx4 e5 hb3 (fun _ => ?_)
    (fun l hl => by rw [t5x] at hl; cases hl)
  refine xcall_gp fm hcode t6 e6 (co := []) (cl := []) rfl rfl (CalleeS.eff_withCo_nil (D.w5.ef c.base _ f5)) ?_
  rw [withViews_nil]
  refine xcall_gp fm hcode t7 e7 (co := []) (cl := []) rfl rfl (CalleeS.eff_withCo_nil (D.w3.ef c.base _ f6)) ?_
  rw [withViews_nil]
  refine xcall_gp fm hcode t8 e8 (co := []) (cl := []) rfl rfl (CalleeS.eff_withCo_nil (D.dm.ef c.base _ f7)) ?_
  rw [withViews_nil]
  refine prog_good fm D.apE hcode encode oEncode v8 v9 _ _ [] [] t9 sx8 e9 hbEnc (fun _ => ?_)
    (fun l hl => by rw [t9x] at hl; cases hl)
  exact zcall_gp fm hcode D.zc t10 e10 (by rw [D.zc_co]; rfl) (by rw [D.zc_co]; rfl) hpp9 hok9
    (fun _ => ok_gp fm (by decide +kernel)) (fun _ => fail_gp fm (by decide +kernel))

end good

end M0Crypto.Release.Ed25519VerifyProg
