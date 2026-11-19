import M0Crypto.Release.Ed25519DsmVal
import M0Crypto.Release.Ed25519GlueRun

/-!
# The run of `m0c_ge_dsm`'s body

The body of `m0c_ge_dsm` between its frame steps: `segPre`, the top-digit scan, `segId`, the
double-scalar loop and `segEnd` (`Ed25519DsmProg`), stitched by its public blocks
(`Ed25519DsmBlocks`) through `wglue_run` and `br_run`.

* `scan_loop`: the scan from index `j` down, to the highest index whose digits are not both
  zero, or `−1`; its trace `scanTr` is a function of the digits and the context.
-/

namespace M0Crypto.Release.Ed25519DsmRun

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
open M0Crypto.Sym (SExpr)
open M0Crypto.Release.BlockEffect (eff_run)

/-! ## The scan's blocks -/

/-- The digit byte at index `r0` of the array whose pointer is at `sp + o`. -/
def bA (o : Nat) : SExpr := .add (dW o) (.reg0 0)

def scanAl : List (SExpr × Nat) := [(.reg0 13, 4), (bA oHp, 1), (bA oSp, 1)]
def scanRg : List (SExpr × Nat) := [(spW 20, 8), (bA oHp, 1), (bA oSp, 1)]
def scanAs : List SExpr := [.reg0 13, bA oHp, bA oSp]

theorem scan_ok : sglueOk dsGeo.cs scanG 0x2a20 dsGeo.top dsGeo.N scanAl [] scanRg = true ∧
    traceOkE scanG scanAs = true ∧
    sglueOk dsGeo.cs [.subImm8 0 1] 0x2a2e dsGeo.top dsGeo.N [] [] [] = true ∧
    traceOkE [.subImm8 0 1] [] = true := by
  decide +kernel

/-- The code of the body at its offsets, decided per build. -/
structure Code (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Prop where
  scan : piecesAt B 0x2a20 (.seq scanG :: (xitBr 1#4 false 0x2a2a 0x2a34 ++ [])) = true
  dec : piecesAt B 0x2a2e (.seq [.subImm8 0 1] :: (xitBr 5#4 false 0x2a30 0x2a20 ++ [])) = true
  br1 : brOk (B := B) dsGeo false 0x2a2a 0x2a34 = true
  br2 : brOk (B := B) dsGeo false 0x2a30 0x2a20 = true
  pieces : segs.all (fun p => piecesAt B p.1 (Prog.emit dsS dbS [] p.1 p.2)) = true
  bok : segs.all (fun p => Prog.bok (B := B) dsS dbS dsGeo [] p.2 p.1) = true

open M0Crypto.Release.Ed25519 (Build) in
theorem code_c : @Code _ _ Build.compact.codeBytes := by
  refine @Code.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ (seg_pieces .compact) (seg_bok .compact) <;>
    (try simp only [Build.bytes, Build.size, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem code_f : @Code _ _ Build.fast.codeBytes := by
  refine @Code.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ (seg_pieces .fast) (seg_bok .fast) <;>
    (try simp only [Build.bytes, Build.size, piecesAt_eq_scan]) <;> decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem code_b : ∀ b : Build, @Code _ _ b.codeBytes
  | .compact => code_c
  | .fast => code_f


/-! ## Views and buffers -/

section facts
variable (Rs : Rels) {c : Ctx} {Wc Rc : List Rgn} (m0 : Mem)

/-- A pointer view's word. -/
theorem pw_view {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c dsGeo m0 st E m) {o : Nat} {v : SV}
    (h : (Loc.fr o, Kd.pw v) ∈ st.Γ) : read32 m (dsGeo.fsp c + BitVec.ofNat 32 o) = v.val c (dsGeo.fsp c) := by
  have := (hi.1 _ h).2; simpa [Rel, Loc.addr] using this

/-- A byte of an external buffer, when no external region is written, is the entry's. -/
theorem buf_m0 (g : GeoOk c dsGeo Wc Rc) {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c dsGeo m0 st E m)
    (hX : st.X = []) {i j : Nat} (ho : SR.ok dsGeo ⟨.ex i j, .k 1⟩ = true) :
    m (c.ptr i + BitVec.ofNat 32 j) = m0 (c.ptr i + BitVec.ofNat 32 j) := by
  refine hi.2.1 _ (fun hw => ?_) (by rw [hX]; exact fun _ h => absurd h List.not_mem_nil)
  have hs := g.ex_win ho rfl
  have hr : SR.rgns dsGeo c ⟨.ex i j, .k 1⟩ = [⟨c.ptr i + BitVec.ofNat 32 j, 1⟩] := by
    simp [SR.rgns, XLen.v, Loc.addr]
  rw [hr] at hs
  exact Sep.not_has hs ⟨_, List.mem_singleton_self _, 0, Nat.one_pos, by simp⟩ ⟨_, List.mem_singleton_self _, hw⟩

/-- The digit bytes `ge_dsm` reads, in a state with no external writes, are the entry's. -/
theorem dig_m0 (g : GeoOk c dsGeo Wc Rc) {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c dsGeo m0 st E m)
    (hX : st.X = []) {i j : Nat} (hi12 : i = 1 ∨ i = 2) (hj : j < 256) : digOf m (c.ptr i) j = digOf m0 (c.ptr i) j := by
  unfold digOf
  rw [buf_m0 Rs m0 g hi hX (by rcases hi12 with rfl | rfl <;> simp [SR.ok, dsGeo] <;> omega)]

end facts

/-! ## Static states with the loop's words -/

/-- The views of the loop's words: the index `I` and the digits `DA`, `DB`. -/
def W : List (Loc × Kd) := [(.fr oI, .cw), (.fr oDa, .cw), (.fr oDb, .cw)]

/-- A state with the loop's words. -/
def ext (st : St) : St := { st with Γ := W ++ st.Γ }

/-- `st` has the views, registers, outputs of `st'` and no more written regions: `At` at `st`
gives `At` at `st'` (`at_wk`). -/
def wkB (st st' : St) : Bool :=
  st'.Γ.all (st.Γ.contains ·) && st.X.all (st'.X.contains ·) && st'.σ.all (st.σ.contains ·) &&
    st'.ρ.all (st.ρ.contains ·)

section wk
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} (m0 : Mem)

theorem at_wk {o : Nat} {st st' : St} {E : Loc → V} {t : State} (h : At Rs B c dsGeo m0 o st E t)
    (hw : wkB st st' = true) : At Rs B c dsGeo m0 o st' E t := by
  simp only [wkB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hw
  exact at_weak Rs m0 h hw.1.1.1 hw.1.1.2 hw.1.2 hw.2

end wk

/-! ## A straight line -/

section seg
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {Wc Rc : List Rgn} (m0 : Mem)
variable (ads : ∀ a, Ad Rs B BS (dsS a)) (bds : ∀ b, Bd Rs (dbS b))

/-- **A straight line** `P` of `segs` at `o`, from the static state `S`, whose static run `L` ends
in a state that weakens to `S'`: at its end `At` with `S'` and the values of `L`. -/
theorem seg_run (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (hcR : Sub [codeR c.base] Rc)
    (cd : Code B BS) {P : Prog DS DB} {o : Nat} (hP : (o, P) ∈ segs) {S S1 S' : St} {L : List (ROp DS DB)}
    (hlin : P.lin dsS dbS dsGeo S = some (L, S1)) (hex : S.ex = none) (hex1 : S1.ex = none) (hw : wkB S1 S' = true)
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP} (hat : At Rs B c dsGeo m0 o S E t)
    (k : ∀ u, At Rs B c dsGeo m0 (o + P.size dsS dbS) S'
      (runR dbS dsGeo (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 L E) u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (Prog.tr dsS dbS dsGeo (fun a => (ads a).T) c P o S Ψ [] []) := by
  have hl := Prog.lin_ev dsS dbS dsGeo (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 P S L S1 hlin
  refine prog_run Rs ads bds m0 g F hcR P hl.1 hex (List.all_eq_true.mp cd.bok _ hP)
    (by rw [List.append_nil]; exact List.all_eq_true.mp cd.pieces _ hP) hat (fun _ u hu _ => k u ?_)
    (fun l hl' => by rw [hex1] at hl'; cases hl')
  rw [hl.2] at hu
  exact at_wk Rs m0 hu hw

end seg

/-! ## The scan -/

/-- Both digits zero at index `i`. -/
def zd (m0 : Mem) (c : Ctx) (i : Nat) : Bool :=
  decide (digOf m0 (c.ptr 2) i = 0 ∧ digOf m0 (c.ptr 1) i = 0)

/-- The scan's result from index `j` down: the highest index whose digits are not both zero, or
`2 ^ 32 − 1` (`−1`). -/
def topI (z : Nat → Bool) : Nat → Nat
  | 0 => if z 0 then 2 ^ 32 - 1 else 0
  | j + 1 => if z (j + 1) then topI z j else j + 1

/-- The state of the scan at index `j`: `r0 = j`. -/
def stS (j : Nat) : St := { rs s0 with σ := [(0, .k j), (13, .sp 0)] }

section run
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} (m0 : Mem)

/-- One pass of the scan at index `j`, with the trace `k` after the decrement's test. -/
def scanHd (z : Nat → Bool) (Ψ : Nat → TrP) (j : Nat) (k : TrP) : TrP :=
  Tr.cat (Tr.is (blockTrE scanG (c.base + BitVec.ofNat 32 0x2a20) scanAs
      [dsGeo.fsp c, c.ptr 2 + BitVec.ofNat 32 j, c.ptr 1 + BitVec.ofNat 32 j]))
    (Tr.cat (Tr.is [bcEv c (1#4 ^^^ 1) 0x2a2a (0x2a2a + 4)]) (Tr.cond (z j)
      (Tr.cat (Tr.is (blockTrE [.subImm8 0 1] (c.base + BitVec.ofNat 32 0x2a2e) [] []))
        (Tr.cat (Tr.is [bcEv c (5#4 ^^^ 1) 0x2a30 (0x2a30 + 4)]) k))
      (Tr.cat (Tr.is [bEv c (0x2a2a + 2) 0x2a34]) (Ψ j))))

/-- **The scan's trace** from index `j`, then `Ψ` of the result. -/
def scanTr (z : Nat → Bool) (Ψ : Nat → TrP) : Nat → TrP
  | 0 => scanHd (c := c) z Ψ 0 (Tr.cond true (Ψ (2 ^ 32 - 1)) (Tr.cat (Tr.is [bEv c (0x2a30 + 2) 0x2a20]) (Tr.is [])))
  | j + 1 => scanHd (c := c) z Ψ (j + 1)
      (Tr.cond false (Ψ 0) (Tr.cat (Tr.is [bEv c (0x2a30 + 2) 0x2a20]) (scanTr z Ψ j)))

/-- The views of `s0` at the digit pointers. -/
theorem s0_ptrs : (Loc.fr 24, Kd.pw (.ext 2 0)) ∈ s0.Γ ∧ (Loc.fr 20, Kd.pw (.ext 1 0)) ∈ s0.Γ ∧ s0.X = [] ∧
    s0.ρ = [] := by
  decide +kernel

theorem keep_nil (Γ : List (Loc × Kd)) : keepViews Γ [] [] = Γ := by simp [keepViews]

variable {Wc Rc : List Rgn}

/-- Back to a scan state after a glue block that writes nothing. -/
theorem at_stS {o i j : Nat} {σ : List (Reg × SV)} {E : Loc → V} {t : State}
    (h : At Rs B c dsGeo m0 o (glueSt (stS i) [] [] σ) E t) (hσ : ∀ p ∈ (stS j).σ, p ∈ σ) :
    At Rs B c dsGeo m0 o (stS j) E t :=
  at_weak Rs m0 h (by simp [glueSt, keep_nil, stS, rs]) (by simp [glueSt, stS, rs])
    hσ (by simp [stS, rs, s0_ptrs.2.2.2])

/-- **One scan test** at index `j`: on both digits zero to the decrement at `0x2a2e` with the trace
`K` after it, else to `0x2a34`. -/
theorem scan_hd (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cd : Code B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : Nat → TrP} {K : TrP} {j : Nat} (hj : j < 256) {t : State}
    (hat : At Rs B c dsGeo m0 0x2a20 (stS j) E t)
    (kz : zd m0 c j = true → ∀ u, At Rs B c dsGeo m0 0x2a2e (stS j) E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q
        (Tr.cat (Tr.is (blockTrE [.subImm8 0 1] (c.base + BitVec.ofNat 32 0x2a2e) [] []))
          (Tr.cat (Tr.is [bcEv c (5#4 ^^^ 1) 0x2a30 (0x2a30 + 4)]) K)))
    (kn : zd m0 c j = false → ∀ u, At Rs B c dsGeo m0 0x2a34 (stS j) E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q (Ψ j)) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (scanHd (c := c) (zd m0 c) Ψ j K) := by
  have h13 := hat.2.1
  have h0 : t.regs 0 = BitVec.ofNat 32 j := (hat.2.2.2.1 (0, .k j) (by simp [stS])).2
  have hi := hat.2.2.2.2.1
  have ph : read32 t.mem (dsGeo.fsp c + BitVec.ofNat 32 24) = c.ptr 2 + BitVec.ofNat 32 0 :=
    pw_view Rs m0 hi (by simp only [stS, rs]; exact s0_ptrs.1)
  have ps : read32 t.mem (dsGeo.fsp c + BitVec.ofNat 32 20) = c.ptr 1 + BitVec.ofNat 32 0 :=
    pw_view Rs m0 hi (by simp only [stS, rs]; exact s0_ptrs.2.1)
  have hX : (stS j).X = [] := by simp [stS, rs, s0_ptrs.2.2.1]
  have hAs : scanAs.map (·.denote t) = [dsGeo.fsp c, c.ptr 2 + BitVec.ofNat 32 j, c.ptr 1 + BitVec.ofNat 32 j] := by
    simp only [scanAs, bA, dW, spW, List.map, M0Crypto.Sym.SExpr.denote, M0Crypto.Sym.SMem.denote, oHp, oSp, h13, h0,
      ph, ps, BitVec.add_zero]
  unfold scanHd
  rw [← hAs]
  refine wglue_run Rs m0 g F (ws := []) (outs := []) (vs := []) (σ := (stS j).σ) scan_ok.1 scan_ok.2.1 cd.scan hat
    ?_ ?_ (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu hp2 => ?_)
  · intro r hr
    simp only [scanAl, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · show (t.regs 13).toNat % 4 = 0; rw [h13]; exact g.fsp4
    · exact Nat.mod_one _
    · exact Nat.mod_one _
  · have e : sregions t scanRg = [⟨dsGeo.fsp c + BitVec.ofNat 32 20, 8⟩, ⟨c.ptr 2 + BitVec.ofNat 32 j, 1⟩,
        ⟨c.ptr 1 + BitVec.ofNat 32 j, 1⟩] := by
      simp only [sregions, scanRg, bA, dW, spW, List.map, M0Crypto.Sym.SExpr.denote, M0Crypto.Sym.SMem.denote, oHp, oSp,
        h13, h0, ph, ps, BitVec.add_zero]
    have hb : ∀ i, i = 1 ∨ i = 2 → Sub [⟨c.ptr i + BitVec.ofNat 32 j, 1⟩] Rc := fun i hi12 => by
      have := g.sub (r := ⟨.ex i j, .k 1⟩) (by rcases hi12 with rfl | rfl <;> simp [SR.ok, dsGeo] <;> omega) false
        (by rcases hi12 with rfl | rfl <;> simp [SR.acc, dsGeo])
      simpa [SR.rgns, XLen.v, Loc.addr] using this
    rw [e]
    exact sub_cons' (g.frame_sub (by decide)) (sub_cons' (hb 2 (.inr rfl)) (sub_cons' (hb 1 (.inl rfl))
      fun _ h => absurd h List.not_mem_nil))
  · intro h13' p hp
    simp only [stS, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ⟨show (0 : Nat) < 14 by decide, ?_⟩
      show (execAll scanG t).regs 0 = BitVec.ofNat 32 j
      rw [(eff_run effs_ok.1 t).reg 0 (by decide) (by decide)]; exact h0
    · exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : 0x2a20 + seqSize scanG = 0x2a2a := by decide
    rw [e] at hu hp2
    refine br_run Rs m0 g F (d := zd m0 c j) (by decide) cd.br1 hp2 hu ?_
      (fun hz hS _ => kz hz _ (at_stS Rs m0 hS (by simp [stS])))
      (fun hz hX => kn hz _ (at_stS Rs m0 hX (by simp [stS])))
    have hz := scan_spec t j h0
    rw [h13, show oHp = 24 from rfl, show oSp = 20 from rfl, ph, ps, BitVec.add_zero, BitVec.add_zero,
      dig_m0 Rs m0 g hi hX (.inr rfl) hj, dig_m0 Rs m0 g hi hX (.inl rfl) hj] at hz
    show (!(execAll scanG t).z) = _
    unfold zd
    by_cases hzz : digOf m0 (c.ptr 2) j = 0 ∧ digOf m0 (c.ptr 1) j = 0
    · rw [decide_eq_true hzz, hz.mpr hzz]
    · rw [decide_eq_false hzz]
      cases h : (execAll scanG t).z
      · rfl
      · exact absurd (hz.mp h) hzz

/-- **The decrement** at `0x2a2e` and `bpl` back to the scan: at `j = 0` to `0x2a34` with `r0 = −1`,
else back to `0x2a20` at `j − 1`. -/
theorem scan_dec (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cd : Code B BS)
    {E : Loc → V} {Q : State → Prop} {Ψk Ψx : TrP} {j : Nat} (hj : j < 256) {t : State}
    (hat : At Rs B c dsGeo m0 0x2a2e (stS j) E t)
    (k0 : j = 0 → ∀ u, At Rs B c dsGeo m0 0x2a34 (stS (2 ^ 32 - 1)) E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψk)
    (k1 : ∀ i, j = i + 1 → ∀ u, At Rs B c dsGeo m0 0x2a20 (stS i) E u →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
      (Tr.cat (Tr.is (blockTrE [.subImm8 0 1] (c.base + BitVec.ofNat 32 0x2a2e) [] []))
        (Tr.cat (Tr.is [bcEv c (5#4 ^^^ 1) 0x2a30 (0x2a30 + 4)])
          (Tr.cond (j == 0) Ψk (Tr.cat (Tr.is [bEv c (0x2a30 + 2) 0x2a20]) Ψx)))) := by
  have h0 : t.regs 0 = BitVec.ofNat 32 j := (hat.2.2.2.1 (0, .k j) (by simp [stS])).2
  have hd := dec_n t (by rw [h0, BitVec.toNat_ofNat]; omega)
  let n : Nat := if j = 0 then 2 ^ 32 - 1 else j - 1
  have hn : t.regs 0 - 1#32 = BitVec.ofNat 32 n := by
    rw [h0]; apply BitVec.eq_of_toNat_eq
    simp only [n, BitVec.toNat_sub, BitVec.toNat_ofNat]
    split <;> omega
  refine wglue_run Rs m0 g F (al := []) (wg := []) (rg := []) (As := []) (ws := []) (outs := []) (vs := [])
    (σ := [(0, .k n), (13, .sp 0)]) scan_ok.2.2.1 scan_ok.2.2.2 cd.dec hat
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => by simp [sregions] at h)
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil trivial ?_ (fun hu hp2 => ?_)
  · intro h13' p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨show (0 : Nat) < 14 by decide, hd.2.trans hn⟩
    · exact ⟨by decide, by simpa [SV.val] using h13'⟩
  · have e : 0x2a2e + seqSize [Instr.subImm8 0 1] = 0x2a30 := by decide
    rw [e] at hu hp2
    refine br_run Rs m0 g F (d := j == 0) (by decide) cd.br2 hp2 hu ?_ (fun hz hS _ => ?_) (fun hz hX => ?_)
    · show (!((Instr.subImm8 0 1).next t).n) = !(j == 0)
      congr 1
      have := hd.1; rw [h0] at this
      cases hj0 : j == 0
      · cases h : ((Instr.subImm8 0 1).next t).n
        · rfl
        · have := (this.mp h); simp only [beq_eq_false_iff_ne] at hj0
          have := congrArg BitVec.toNat this; simp only [BitVec.toNat_ofNat] at this; omega
      · simp only [beq_iff_eq] at hj0; subst hj0; exact this.mpr rfl
    · have hj0 : j = 0 := by simpa using hz
      subst hj0
      exact k0 rfl _ (at_stS Rs m0 hS (by simp [stS, n]))
    · have hj0 : j ≠ 0 := by simpa using hz
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact k1 i rfl _ (at_stS Rs m0 hX (by simp [stS, n]))

/-- **The scan** from index `j`: to `0x2a34` with `r0` the highest index up to `j` whose digits are
not both zero, or `2 ^ 32 − 1` (`topI`). -/
theorem scan_loop (g : GeoOk c dsGeo Wc Rc) (F : Caller c.base c.sp0 dsGeo.N Wc) (cd : Code B BS)
    {E : Loc → V} {Q : State → Prop} {Ψ : Nat → TrP} :
    ∀ j, j < 256 → ∀ t, At Rs B c dsGeo m0 0x2a20 (stS j) E t →
      (∀ u, At Rs B c dsGeo m0 0x2a34 (stS (topI (zd m0 c) j)) E u →
        ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) u Q
          (Ψ (topI (zd m0 c) j))) →
      ReachFT c.base (PcIn c.base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dsGeo.N) t Q
        (scanTr (c := c) (zd m0 c) Ψ j)
  | 0, hj, t, hat, k => by
    rw [scanTr]
    refine scan_hd Rs m0 g F cd hj hat (fun hz u hu => scan_dec Rs m0 g F cd hj hu (fun _ u' hu' => ?_)
      (fun i hi => absurd hi (by omega))) (fun hz u hu => ?_)
    · have e : topI (zd m0 c) 0 = 2 ^ 32 - 1 := by simp [topI, hz]
      rw [e] at k; exact k u' hu'
    · have e : topI (zd m0 c) 0 = 0 := by simp [topI, hz]
      rw [e] at k; exact k u hu
  | j + 1, hj, t, hat, k => by
    rw [scanTr]
    refine scan_hd Rs m0 g F cd hj hat (fun hz u hu => scan_dec Rs m0 g F cd hj hu (fun h => absurd h (by omega))
      (fun i hi u' hu' => ?_)) (fun hz u hu => ?_)
    · obtain rfl : i = j := by omega
      have e : topI (zd m0 c) (i + 1) = topI (zd m0 c) i := by simp [topI, hz]
      rw [e] at k
      exact scan_loop g F cd i (by omega) u' hu' k
    · have e : topI (zd m0 c) (j + 1) = j + 1 := by simp [topI, hz]
      rw [e] at k; exact k u hu

end run

end M0Crypto.Release.Ed25519DsmRun
