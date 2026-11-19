import M0Crypto.Release.Ed25519DecompressAd
import M0Crypto.Release.Ed25519GlueRun

/-!
# `m0c_ge_decompress`'s body runs

`body_run`: from the body's start, the stitched sites run to the epilogue with the status of the
tests in `r0`, and on success the views of `seg6`'s state with the values of the updates
`Ed25519DecompressOut.dcR` along the path the tests take. The values are `rC`'s runs of the
updates (`E1` … `E7`); `lin` decides that each straight line's values are those updates.
-/

namespace M0Crypto.Release.Ed25519DecompressStitch

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint (bytesAt Rgn Has Sub)
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519DecompressOut (seg0R seg3R seg4R seg5R seg6R powR L3 inB yN sgN)
open M0Crypto.Release.Ed25519MulBaseVal (frR)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519FeEq (eqS eqAd eqZ okE)
open M0Crypto.Release.Ed25519GeProg (fI fI_nat)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519PrimeCert (p)

/-! ## The static facts the run uses -/

/-- The arguments of `fe_eq` at `TMP`, `T` and `o`. -/
def aE (o : Nat) : List (LowReg × Ld) := [(0, .S TMP), (1, .S T), (2, .S o)]

def oR : List (ROp DA DX) := [.blk .loadT [(.fr Y, .fe), (.fr SIGN, .bytes 4)] [.ext ⟨.ex 1 0, .k 32⟩]]
def q1R : List (ROp DA DB) := frR DA.f L1 ++ [powR] ++ frR DA.f L2

theorem lines_lin : (p0.lin daS dbS dcGeo stE).map Prod.fst = some [] ∧ (Op.blk DX.loadT [] : Op DA DX).rops daS dxS dcGeo t0 = oR ∧
    (q1.lin daS dbS dcGeo (addViews t1 [])).map Prod.fst = some q1R ∧
    (q2.lin daS dbS dcGeo (addViews t3 [])).map Prod.fst = some (frR DA.f L3) ∧
    (seg3.lin daS dbS dcGeo (addViews t5 [])).map Prod.fst = some seg3R ∧
    (seg4.lin daS dbS dcGeo tJ).map Prod.fst = some seg4R ∧ (seg5.lin daS dbS dcGeo tT).map Prod.fst = some seg5R ∧
    (seg6.lin daS dbS dcGeo tK).map Prod.fst = some seg6R := by
  decide +kernel

theorem sites_io :
    (ioRes dcGeo t0 (regsOf t0.Γ t0.σ []) ioLoad).map (·.srcs) = some [.ext ⟨.ex 1 0, .k 32⟩] ∧
    (ioRes dcGeo t2 (regsOf t2.Γ t2.σ (aE U)) eqS.io).map (·.srcs) = some [.view (.fr T), .view (.fr U)] ∧
    (ioRes dcGeo t4 (regsOf t4.Γ t4.σ (aE X2)) eqS.io).map (·.srcs) = some [.view (.fr T), .view (.fr X2)] := by
  decide +kernel

theorem starts_ex : (addViews t1 []).ex = none ∧ (addViews t3 []).ex = none ∧ (addViews t5 []).ex = none ∧
    tJ.ex = none ∧ tT.ex = none ∧ tK.ex = none := by
  decide +kernel

/-- `X` canonical and `SIGN` at the tests. -/
theorem tests_views : (Loc.fr X, Kd.fc) ∈ t7.Γ ∧ (Loc.fr SIGN, Kd.bytes 4) ∈ t7.Γ := by decide +kernel

/-- The joins' registers: `sp`. -/
theorem joins_σ : (∀ q ∈ σsp, q ∈ t6.σ) ∧ (∀ q ∈ σsp, q ∈ t8.σ) := by decide +kernel

/-- `SIGN` is kept by the updates after the load. -/
theorem sign_keep : ∀ r ∈ q1R ++ frR DA.f L3 ++ seg3R ++ seg4R, Ed25519DecompressOut.keeps (.fr SIGN) r = true := by
  decide +kernel

/-- After a status call and its test, `q2` starts from the call's views. -/
theorem e1_views : ∀ q ∈ (addViews t3 []).Γ, q ∈ t3.Γ := by decide +kernel

/-! ## Generic steps -/

section gen
variable {Rs : Rels} {B : List (BitVec 8)} {c : Ctx} {G : Geo} {m0 : Mem}

theorem atMv {o o' : Nat} {st : St} {E : Loc → V} {t : State} (h : o = o') (hu : At Rs B c G m0 o st E t) :
    At Rs B c G m0 o' st E t := h ▸ hu

theorem atE {o : Nat} {st : St} {E E' : Loc → V} {t : State} (h : E = E') (hu : At Rs B c G m0 o st E t) :
    At Rs B c G m0 o st E' t := h ▸ hu

/-- **The joins**: either path's state, with only `sp` known, weakens to the join. -/
theorem at_joinL {o : Nat} {s₀ s₁ : St} {E : Loc → V} {t : State}
    (h : At Rs B c G m0 o { s₀ with σ := σsp, ρ := [] } E t) :
    At Rs B c G m0 o (joinSt { s₀ with σ := σsp, ρ := [] } s₁) E t :=
  Ed25519GlueRun.at_weak Rs m0 h (fun _ hq => (List.mem_filter.mp hq).1) (fun _ hr => List.mem_append_left _ hr)
    (fun _ hq => hq) (fun _ hr => by simp [joinSt] at hr)

theorem at_joinR {o : Nat} {s₀ s₁ : St} {E : Loc → V} {t : State} (h : At Rs B c G m0 o s₁ E t)
    (hσ : ∀ q ∈ σsp, q ∈ s₁.σ) : At Rs B c G m0 o (joinSt s₀ s₁) E t :=
  Ed25519GlueRun.at_weak Rs m0 h (fun _ hq => by simpa using (List.mem_filter.mp hq).2)
    (fun _ hr => List.mem_append_right _ hr) hσ (fun _ hr => by simp [joinSt] at hr)

variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {semA : A → List V → List V}
  {semB : Bk → List V → List V}

/-- A straight line's values are those of its `lin` updates. -/
theorem lin_run {P : Prog A Bk} {st : St} {L : List (ROp A Bk)} (h : (P.lin cE bE G st).map Prod.fst = some L)
    (E : Loc → V) : P.ev cE bE G semA semB c m0 st E = runR bE G semA semB c m0 L E := by
  obtain ⟨⟨L', s'⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (Prog.lin_ev cE bE G semA semB c m0 P st L' s' h1).2 E

theorem ioVs_of {st : St} {σ : List (Reg × SV)} {io : Iface} {E : Loc → V} {ss : List Src}
    (h : (ioRes G st σ io).map (·.srcs) = some ss) : ioVs G c m0 st σ io E = ss.map (Src.val G c m0 E) := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [ioVs, hr]

theorem updOuts_nil (E : Loc → V) : ∀ o : List (Loc × Kd), updOuts E o [] = E
  | [] => rfl
  | _ :: _ => rfl

theorem updOuts_none (E : Loc → V) (vs : List V) : updOuts E [] vs = E := by
  cases vs <;> rfl

/-- A call without values keeps them. -/
theorem xcallEv_nil {st : St} {σ : List (Reg × SV)} {io : Iface} (E : Loc → V) :
    xcallEv G c m0 st σ io (fun _ => []) E = E := by
  simp only [xcallEv]
  split
  · exact updOuts_nil E _
  · rfl

end gen

/-! ## The tests on the values -/

/-- `x = 0`. -/
def isZ : V → Bool
  | .f x => decide (fI x = 0)
  | _ => false

/-- The parity of `x` is the sign `s`. -/
def pOf (s : Nat) : V → Bool
  | .f x => decide ((fI x).val % 2 = s)
  | _ => false

/-- A canonical value's field value is the number. -/
theorem fc_val {n : Nat} {x : Int} (hx : (n : Int) = x) (hl : x < Field25519Congr.p) : (fI x).val = n := by
  have e : Field25519Congr.p = ((p : Nat) : Int) := by decide
  rw [← hx, fI_nat, Ed25519Decode.val_toF_of_lt (by omega)]

section tests
variable {Rs : Rels} {c : Ctx} {sp : Word}

theorem z_dec {t : State} {v : V} (h13 : t.regs 13 = sp)
    (h : Rel Rs c sp .fc t.mem (sp + BitVec.ofNat 32 X) v) : condPassed NE (execAll zG t) = !isZ v := by
  cases v <;> simp only [Rel] at h
  rename_i x
  obtain ⟨hx, hl⟩ := h
  have hv := fc_val hx hl
  have hz := (z_run t).1
  rw [h13] at hz
  have e : (execAll zG t).z = isZ (.f x) := by
    rw [Bool.eq_iff_iff, hz, isZ, decide_eq_true_iff]
    exact ⟨fun h => Ed25519Field.Fp.ext (by rw [hv, h]; rfl), fun h => by rw [← hv, h]; rfl⟩
  show (!(execAll zG t).z) = _
  rw [e]

theorem s_dec {u : State} {m : M0Crypto.Armv6M.Mem} {l : List (BitVec 8)} (hl : l.length = 32)
    (h2 : u.regs 2 = read32 m (sp + BitVec.ofNat 32 SIGN)) (hb : bytesAt m (sp + BitVec.ofNat 32 SIGN) 4 = signB l) :
    condPassed NE (execAll sG u) = !decide (decodeInt l / 2 ^ 255 = 0) := by
  have hw := (sign_word hl hb).1
  have e : (execAll sG u).z = decide (decodeInt l / 2 ^ 255 = 0) := by
    rw [Bool.eq_iff_iff, show execAll sG u = (Instr.cmpImm 2 0).next u from rfl, s_spec, h2, decide_eq_true_iff,
      ← BitVec.toNat_inj, hw]
    rfl
  show (!(execAll sG u).z) = _
  rw [e]

theorem p_dec {t : State} {v : V} {l : List (BitVec 8)} (hl : l.length = 32) (h13 : t.regs 13 = sp)
    (h : Rel Rs c sp .fc t.mem (sp + BitVec.ofNat 32 X) v) (hb : bytesAt t.mem (sp + BitVec.ofNat 32 SIGN) 4 = signB l) :
    condPassed EQ (execAll pG t) = pOf (decodeInt l / 2 ^ 255) v := by
  cases v <;> simp only [Rel] at h
  obtain ⟨hx, hl'⟩ := h
  have hw := (sign_word hl hb).1
  have hz := (p_run t).1
  rw [h13, hw] at hz
  show (execAll pG t).z = _
  rw [Bool.eq_iff_iff, hz, pOf, decide_eq_true_iff, fc_val hx hl']

end tests

/-! ## The values along the body -/

noncomputable section vals
variable (Rs : Rels) (b : Build) (c : Ctx) (m0 : Mem)

/-- The callees' and the blocks' values, and the runs of updates. -/
abbrev sA : DA → List V → List V := fun a => @Ad.sem Rs b.bytes b.size b.codeBytes _ (daAd Rs b a).ad
abbrev sB : DB → List V → List V := fun x => (dbAd Rs x).sem
abbrev rC (L : List (ROp DA DB)) (E : Loc → V) : Loc → V := Ed25519DecompressOut.runC (sA Rs b) (sB Rs) c m0 L E

/-- The load, `F1` to `F2`, `F3`, `F4`; the join at `ok1` (`bb`: the second candidate); `x`
canonical; the negation (`n`); the output. -/
def E1 : Loc → V := rC Rs b c m0 seg0R fun _ => .none
def E2 : Loc → V := rC Rs b c m0 q1R (E1 Rs b c m0)
def E3 : Loc → V := rC Rs b c m0 (frR DA.f L3) (E2 Rs b c m0)
def E4 : Loc → V := rC Rs b c m0 seg3R (E3 Rs b c m0)
def EJ (bb : Bool) : Loc → V := if bb then E4 Rs b c m0 else E2 Rs b c m0
def E5 (bb : Bool) : Loc → V := rC Rs b c m0 seg4R (EJ Rs b c m0 bb)
def E6 (bb n : Bool) : Loc → V := if n then rC Rs b c m0 seg5R (E5 Rs b c m0 bb) else E5 Rs b c m0 bb
def E7 (bb n : Bool) : Loc → V := rC Rs b c m0 seg6R (E6 Rs b c m0 bb n)

/-- The inputs of the two `fe_eq` calls. -/
def iE1 : List V := ioVs dcGeo c m0 t2 (regsOf t2.Γ t2.σ (aE U)) eqS.io (E2 Rs b c m0)
def iE2 : List V := ioVs dcGeo c m0 t4 (regsOf t4.Γ t4.σ (aE X2)) eqS.io (E3 Rs b c m0)

/-- **The tests**: `y < p`, the two candidates, `x = 0`, the sign `0`, the negation. -/
def k0 : Bool := decide (yN c m0 < p)
def k1 : Bool := okE (iE1 Rs b c m0)
def k2 : Bool := okE (iE2 Rs b c m0)
def kz (bb : Bool) : Bool := isZ (E5 Rs b c m0 bb (.fr X))
def ks : Bool := decide (sgN c m0 = 0)
def kn (bb : Bool) : Bool := !pOf (sgN c m0) (E5 Rs b c m0 bb (.fr X))

/-- **The status**. -/
def okD : Bool := k0 c m0 && (k1 Rs b c m0 || k2 Rs b c m0) && (!kz Rs b c m0 (!k1 Rs b c m0) || ks c m0)

theorem sign_val (bb : Bool) : E5 Rs b c m0 bb (.fr SIGN) = .b (signB (inB c m0)) := by
  have k : ∀ L E, (∀ r ∈ L, r ∈ q1R ++ frR DA.f L3 ++ seg3R ++ seg4R) → rC Rs b c m0 L E (.fr SIGN) = E (.fr SIGN) :=
    fun L E h => Ed25519DecompressOut.runC_keep L E fun r hr => sign_keep r (h r hr)
  have h1 : E1 Rs b c m0 (.fr SIGN) = .b (signB (inB c m0)) := by
    simp only [E1, rC, Ed25519DecompressOut.runC, runR, ROp.ev, seg0R, List.map_cons, List.map_nil, Src.val]
    rfl
  have h2 : E2 Rs b c m0 (.fr SIGN) = .b (signB (inB c m0)) :=
    (k _ _ fun _ hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))).trans h1
  rw [E5, k _ _ fun _ hr => List.mem_append_right _ hr, EJ]
  cases bb
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact h2
  · simp only [↓reduceIte]
    rw [E4, E3, k _ _ fun _ hr => List.mem_append_left _ (List.mem_append_right _ hr),
      k _ _ fun _ hr => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))]
    exact h2

end vals

/-! ## The trace of the body -/

noncomputable section tr
variable (Rs : Rels) (b : Build) (c : Ctx)

abbrev dT : DA → Word → (Nat → Word) → List Event := fun a => @Ad.T Rs b.bytes b.size b.codeBytes _ (daAd Rs b a).ad

/-- `fe_eq`'s status word. -/
def stW (ok : Bool) : List Word := [if ok = true then 0 else 1]

def tFail : TrP := Tr.cat (Tr.is (blockTr [.movImm 0 1] (c.base + BitVec.ofNat 32 oFail) [13] [dcGeo.fsp c])) (Tr.is [])
def tOk : TrP := Tr.cat (Tr.is (blockTr [.movImm 0 0] (c.base + BitVec.ofNat 32 oOk) [13] [dcGeo.fsp c]))
  (Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 (oOk + seqSize [.movImm 0 0]),
    .b (brImm11 (oOk + seqSize [.movImm 0 0]) oDone), []⟩]) (Tr.is []))
def tS6 : TrP := Prog.tr daS dbS dcGeo (dT Rs b) c seg6 oSame tK (tOk c) [] []
def tS5 : TrP := Prog.tr daS dbS dcGeo (dT Rs b) c seg5 oS5 tT (tS6 Rs b c) [] []
def tP (n : Bool) : TrP := tstSTr dcGeo c oOkz pG EQ oSame n (tS5 Rs b c) (tS6 Rs b c)
def tSg (s n : Bool) : TrP := tstTr dcGeo c oSg sG NE oFail s (tP Rs b c n) (tFail c)
def tZ (z s n : Bool) : TrP := tstTr dcGeo c oZ zG NE oOkz z (tSg Rs b c s n) (tP Rs b c n)
def tS4 (z s n : Bool) : TrP := Prog.tr daS dbS dcGeo (dT Rs b) c seg4 oOk1 tJ (tZ Rs b c z s n) [] []
def tS3 (z s n : Bool) : TrP := Prog.tr daS dbS dcGeo (dT Rs b) c seg3 oS3 (addViews t5 []) (tS4 Rs b c z s n) [] []
def tE2 (k2 z s n : Bool) : TrP :=
  xcallTr dcGeo c oE2 (aE X2) eqS.entry ((eqAd Rs b).T c.base (xcallPub dcGeo c t4 (aE X2) eqS (stW k2)))
    (tstTr dcGeo c (oE2 + (e2 : Op DA DB).size daS dbS) [.cmpImm 0 0] NE oFail k2 (tS3 Rs b c z s n) (tFail c))
def tQ2 (k2 z s n : Bool) : TrP := Prog.tr daS dbS dcGeo (dT Rs b) c q2 oQ2 (addViews t3 []) (tE2 Rs b c k2 z s n) [] []
def tE1 (k1 k2 z s n : Bool) : TrP :=
  xcallTr dcGeo c oE1 (aE U) eqS.entry ((eqAd Rs b).T c.base (xcallPub dcGeo c t2 (aE U) eqS (stW k1)))
    (tstTr dcGeo c (oE1 + (e1 : Op DA DB).size daS dbS) [.cmpImm 0 0] EQ oOk1 (!k1) (tQ2 Rs b c k2 z s n)
      (tS4 Rs b c z s n))
def tQ1 (k1 k2 z s n : Bool) : TrP :=
  Prog.tr daS dbS dcGeo (dT Rs b) c q1 oQ1 (addViews t1 []) (tE1 Rs b c k1 k2 z s n) [] []
def tL (k0 k1 k2 z s n : Bool) : TrP :=
  (bL : Op DA DX).tr daS dxS dcGeo (fun _ _ _ => []) c oL t0
    (tstTr dcGeo c (oL + (bL : Op DA DX).size daS dxS) [] NE oFail k0 (tQ1 Rs b c k1 k2 z s n) (tFail c))
/-- **The trace of the body** with the tests' decisions. -/
def bodyTr (k0 k1 k2 z s n : Bool) : TrP :=
  Prog.tr daS dbS dcGeo (dT Rs b) c p0 oP0 stE (tL Rs b c k0 k1 k2 z s n) [] []

end tr

/-! ## The run -/

/-- **The body's end**: at the epilogue, `sp` at the frame, the status `ok` in `r0`, and on
success `H` of the memory. -/
def QD (c : Ctx) (ok : Bool) (H : Mem → Prop) (u : State) : Prop :=
  u.pc = c.base + BitVec.ofNat 32 oDone ∧ u.regs 13 = dcGeo.fsp c ∧ u.regs 0 = (if ok then 0#32 else 1#32) ∧
    (ok = true → H u.mem)

/-- A run of the body in build `b`. -/
abbrev RD (b : Build) (c : Ctx) (Wc Rc : List Rgn) (t : State) (Q : State → Prop) (Ψ : TrP) : Prop :=
  @ReachFT b.bytes b.size b.codeBytes c.base (PcIn c.base dcGeo.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 dcGeo.N) t Q Ψ

section run
variable {Rs : Rels} {b : Build} {c : Ctx} {Wc Rc : List Rgn} {m0 : Mem}

theorem fail_tail (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc) {st : St} {E : Loc → V} {u : State}
    {ok : Bool} {H : Mem → Prop} (hat : At Rs b.bytes c dcGeo m0 oFail st E u) (hok : ok = false) :
    RD b c Wc Rc u (QD c ok H) (tFail c) := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, h5, h6⟩ := tail_code b
  refine pubB_run (B := b.bytes) (BS := b.size) Rs m0 g F h5 h6 hat fun hpc h13 _ _ => ReachT.done ⟨?_, h13, ?_, fun h => absurd (hok ▸ h) (by simp)⟩
  · rw [hpc]; rfl
  · rw [hok, execAll, execAll, movImm_r0]; rfl

theorem ok_tail (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc) {st : St} {E : Loc → V} {u : State}
    {ok : Bool} (hat : At Rs b.bytes c dcGeo m0 oOk st E u) (hok : ok = true) :
    RD b c Wc Rc u (QD c ok (Inv Rs c dcGeo m0 st E)) (tOk c) := by
  letI := b.codeBytes
  obtain ⟨h1, h2, h3, h4, -, -⟩ := tail_code b
  have hi := hat.2.2.2.2.1
  refine pubB_run (B := b.bytes) (BS := b.size) Rs m0 g F h1 h2 hat fun hpc h13 hm _ => ?_
  refine b_run F h3 h4 hpc h13 g.top (ReachT.done ⟨?_, ?_, ?_, fun _ => ?_⟩)
  · simp [State.pc, State.setReg]
  · simpa [State.setReg] using h13
  · simp only [State.setReg, hok, execAll]; rw [movImm_r0]; rfl
  · simp only [State.setReg]; rw [hm]; exact hi

/-- **The output** from `same`: `seg6`, then the success status. -/
theorem s6_run (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc)
    (hcR : Sub [@codeR b.bytes b.size b.codeBytes c.base] Rc) {bb n : Bool} {u : State} {ok : Bool} (hok : ok = true)
    (hat : At Rs b.bytes c dcGeo m0 oSame tK (E6 Rs b c m0 bb n) u) :
    RD b c Wc Rc u (QD c ok (Inv Rs c dcGeo m0 t9 (E7 Rs b c m0 bb n))) (tS6 Rs b c) := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, -, -, ⟨hb6, hp6⟩⟩ := lines_code b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h9, h9x, -⟩ := sites_ty
  exact prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR seg6 h9
    starts_ex.2.2.2.2.2 hb6 hp6 hat
    (fun _ u9 hu9 _ => ok_tail g F (atMv (by decide +kernel) (atE (lin_run lines_lin.2.2.2.2.2.2.2 _) hu9)) hok)
    (fun l hl => by rw [h9x] at hl; cases hl)

/-- **The parity test** at `okz`: on the negation `seg5`, then the output. -/
theorem par_run (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc)
    (hcR : Sub [@codeR b.bytes b.size b.codeBytes c.base] Rc) {bb : Bool} {u : State} {ok : Bool} (hok : ok = true)
    (hat : At Rs b.bytes c dcGeo m0 oOkz tT (E5 Rs b c m0 bb) u) :
    RD b c Wc Rc u (QD c ok (Inv Rs c dcGeo m0 t9 (E7 Rs b c m0 bb (kn Rs b c m0 bb)))) (tP Rs b c (kn Rs b c m0 bb)) := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, -, ⟨hb5, hp5⟩, -⟩ := lines_code b
  obtain ⟨-, -, ⟨tpa, tpb, tpc⟩⟩ := tests_code b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h8, h8x, -, -, -, -⟩ := sites_ty
  have hb : bytesAt u.mem (dcGeo.fsp c + BitVec.ofNat 32 SIGN) 4 = signB (inB c m0) := by
    have h := (hat.2.2.2.2.1.1 _ tests_views.2).2
    rw [sign_val] at h
    exact h
  refine tstS_run (B := b.bytes) (BS := b.size) Rs m0 g F tpa tpb tpc hat ?_ (fun hn u8 hu8 _ _ => ?_)
    (fun hn u8 hu8 _ => s6_run g F hcR hok (atE ?_ (at_joinL hu8)))
  · rw [kn, Bool.not_not]
    exact p_dec (Footprint.bytesAt_length _ _ _) hat.2.1 (hat.2.2.2.2.1.1 _ tests_views.1).2 hb
  · exact prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR seg5 h8
      starts_ex.2.2.2.2.1 hb5 hp5 (atMv (by decide +kernel) hu8)
      (fun _ u9 hu9 _ => s6_run g F hcR hok (at_joinR (atMv (by decide +kernel)
        (atE ((lin_run lines_lin.2.2.2.2.2.2.1 _).trans (by simp only [E6, hn, ↓reduceIte])) hu9)) joins_σ.2))
      (fun l hl => by rw [h8x] at hl; cases hl)
  · simp only [E6, hn, Bool.false_eq_true, ↓reduceIte]

/-- **From `ok1`**: `x` canonical, the zero and sign tests, then the parity. -/
theorem tail_run (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc)
    (hcR : Sub [@codeR b.bytes b.size b.codeBytes c.base] Rc) (bb : Bool) {u : State} {ok : Bool} (hok : ok = (!kz Rs b c m0 bb || ks c m0))
    (hat : At Rs b.bytes c dcGeo m0 oOk1 tJ (EJ Rs b c m0 bb) u) :
    RD b c Wc Rc u (QD c ok (Inv Rs c dcGeo m0 t9 (E7 Rs b c m0 bb (kn Rs b c m0 bb))))
      (tS4 Rs b c (kz Rs b c m0 bb) (ks c m0) (kn Rs b c m0 bb)) := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, ⟨hb4, hp4⟩, -, -⟩ := lines_code b
  obtain ⟨⟨tza, tzb, tzc⟩, ⟨tsa, tsb, tsc⟩, -⟩ := tests_code b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h7, h7x, -, -, -, -, -, -, -⟩ := sites_ty
  refine prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR seg4 h7
    starts_ex.2.2.2.1 hb4 hp4 hat (fun _ u5 hu5 _ => ?_) (fun l hl => by rw [h7x] at hl; cases hl)
  have hu : At Rs b.bytes c dcGeo m0 oZ t7 (E5 Rs b c m0 bb) u5 :=
    atMv (by decide +kernel) (atE (lin_run lines_lin.2.2.2.2.2.1 _) hu5)
  refine tst_run (B := b.bytes) (BS := b.size) Rs m0 g F (by decide) tza tzb tzc hu
    (z_dec hu.2.1 (hu.2.2.2.2.1.1 _ tests_views.1).2) (fun hz u6 hu6 _ hr _ => ?_)
    (fun hz u6 hu6 _ => par_run g F hcR (by rw [hok, hz]; rfl) hu6)
  have hb : bytesAt u5.mem (dcGeo.fsp c + BitVec.ofNat 32 SIGN) 4 = signB (inB c m0) := by
    have h := (hu.2.2.2.2.1.1 _ tests_views.2).2
    rw [sign_val] at h
    exact h
  have h2 : u6.regs 2 = read32 u5.mem (dcGeo.fsp c + BitVec.ofNat 32 SIGN) := by
    rw [hr 2 (by decide), (z_run u5).2.1, hu.2.1]
  exact tst_run (B := b.bytes) (BS := b.size) Rs m0 g F (by decide) tsa tsb tsc (atMv (by decide +kernel) hu6)
    (s_dec (Footprint.bytesAt_length _ _ _) h2 hb)
    (fun hs u7 hu7 _ _ _ => par_run g F hcR (by rw [hok, hz, hs]; rfl) (atMv (by decide +kernel) hu7))
    (fun hs u7 hu7 _ => fail_tail g F hu7 (by rw [hok, hz, hs]; rfl))

/-- **The body runs** from the spill to the epilogue with the status of its tests in `r0`, and on
success `seg6`'s views with the values of the updates along the path the tests take. -/
theorem body_run (g : GeoOk c dcGeo Wc Rc) (F : @Caller b.bytes b.size b.codeBytes c.base c.sp0 dcGeo.N Wc)
    (hcR : Sub [@codeR b.bytes b.size b.codeBytes c.base] Rc) {t : State} (hat : At Rs b.bytes c dcGeo m0 oP0 stE (fun _ => .none) t) :
    RD b c Wc Rc t (QD c (okD Rs b c m0)
        (Inv Rs c dcGeo m0 t9 (E7 Rs b c m0 (!k1 Rs b c m0) (kn Rs b c m0 (!k1 Rs b c m0)))))
      (bodyTr Rs b c (k0 c m0) (k1 Rs b c m0) (k2 Rs b c m0) (kz Rs b c m0 (!k1 Rs b c m0)) (ks c m0)
        (kn Rs b c m0 (!k1 Rs b c m0))) := by
  letI := b.codeBytes
  obtain ⟨⟨hb0, hp0⟩, ⟨hbq1, hpq1⟩, ⟨hbq2, hpq2⟩, ⟨hb3, hp3⟩, -, -, -⟩ := lines_code b
  obtain ⟨hl1, hl2, hl3, hl4⟩ := load_code b
  obtain ⟨⟨z1a, z1b, z1c, z1d⟩, ⟨z2a, z2b, z2c, z2d⟩⟩ := sites_code b
  obtain ⟨h0, h0x, -, h1, -, -, h2, h2x, -, h3, -, h4, h4x, -, h5, -, h6, h6x, -, -, -, -, -, -, -, -, -, -⟩ :=
    sites_ty
  obtain ⟨sx1, sx3, sx5, -, -, -⟩ := starts_ex
  refine prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR p0 h0 rfl hb0
    hp0 hat (fun _ u0 hu0 _ => ?_) (fun l hl => by rw [h0x] at hl; cases hl)
  refine zblk_run (B := b.bytes) (BS := b.size) Rs m0 g F (semA := fun _ _ => []) (T' := fun _ _ _ => [])
    (ldTZ Rs) (cl := []) (d := k0 c m0) (show NE.toNat < 14 by decide) h1 hl1 hl2 hl3 hl4 (atMv (by decide +kernel) hu0) rfl rfl ?_
    trivial (fun hd0 u1 hu1 _ => ?_) (fun hd0 u hu => fail_tail g F hu (by simp [okD, hd0]))
  · rw [show (dxS DX.loadT).io = ioLoad from rfl, ioVs_of sites_io.1]
    rfl
  have hu1' : At Rs b.bytes c dcGeo m0 oQ1 (addViews t1 []) (E1 Rs b c m0) u1 :=
    atMv (by decide +kernel) (atE (by rw [Op.ev_rops, lines_lin.2.1, lin_run lines_lin.1]; rfl) hu1)
  refine prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR q1 h2 sx1 hbq1
    hpq1 hu1' (fun _ u2 hu2 _ => ?_) (fun l hl => by rw [h2x] at hl; cases hl)
  have hu2' : At Rs b.bytes c dcGeo m0 oE1 t2 (E2 Rs b c m0) u2 :=
    atMv (by decide +kernel) (atE (lin_run lines_lin.2.2.1 _) hu2)
  refine xcall_run (B := b.bytes) (BS := b.size) (cE := daS) (bE := dbS) (a := .eq) Rs m0 g F hcR (eqAd Rs b) h3 z1a z1d hu2' trivial
    (fun u3 hu3 ⟨s, _, _, hpv, hins, hpost, _⟩ hr => ?_)
  have hz := (eqZ Rs b).okr c (dcGeo.fsp c) s u3.mem (u3.regs 0) _ hpv hins trivial hpost
  refine tst_run (B := b.bytes) (BS := b.size) Rs m0 g F (by decide) z1b z1c hr (atE (xcallEv_nil _) hu3) ?_
    (fun hd u4 hu4 _ _ _ => ?_) (fun hd u4 hu4 _ => ?_)
  · have e : LowReg.toReg 0 = 0 := rfl
    rw [Bool.not_not]
    show (execAll [.cmpImm 0 0] u3).z = _
    rw [RoutinePieces.cmp0_z, e, Bool.eq_iff_iff, beq_iff_eq]
    exact hz
  · -- the second candidate
    have hk1 : k1 Rs b c m0 = false := by simpa using hd
    have hu4' : At Rs b.bytes c dcGeo m0 oQ2 (addViews t3 []) (E2 Rs b c m0) u4 :=
      atMv (by decide +kernel) (Ed25519GlueRun.at_weak Rs m0 hu4 e1_views (fun _ h => h) (fun _ h => h) (fun _ h => h))
    refine prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR q2 h4 sx3
      hbq2 hpq2 hu4' (fun _ u5 hu5 _ => ?_) (fun l hl => by rw [h4x] at hl; cases hl)
    have hu5' : At Rs b.bytes c dcGeo m0 oE2 t4 (E3 Rs b c m0) u5 :=
      atMv (by decide +kernel) (atE (lin_run lines_lin.2.2.2.1 _) hu5)
    refine zcall_run (B := b.bytes) (BS := b.size) (cE := daS) (bE := dbS) (a := .eq) Rs m0 g F hcR (eqZ Rs b) (cl := []) (d := k2 Rs b c m0) h5 z2a
      z2b z2c z2d hu5' trivial rfl (by decide) rfl (fun hd2 _ u6 hu6 _ => ?_)
      (fun hd2 _ u hu => fail_tail g F hu (by simp [okD, hk1, hd2]))
    refine prog_run (B := b.bytes) (BS := b.size) Rs (fun a => (daAd Rs b a).ad) (dbAd Rs) m0 g F hcR seg3 h6 sx5
      hb3 hp3 (atMv (by decide +kernel) (atE ((updOuts_none _ _).trans (xcallEv_nil _)) hu6)) (fun _ u7 hu7 _ => ?_)
      (fun l hl => by rw [h6x] at hl; cases hl)
    refine tail_run g F hcR _ (by simp only [okD, hd0, hd2, Bool.true_and, Bool.or_true]) (atE ?_
      (at_joinR (atMv (by decide +kernel) (atE (lin_run lines_lin.2.2.2.2.1 _) hu7)) joins_σ.1))
    simp only [EJ, hd, ↓reduceIte]
    rfl
  · -- the first candidate
    have hk1 : k1 Rs b c m0 = true := by simpa using hd
    refine tail_run g F hcR _ (by simp only [okD, hd0, hk1, Bool.true_and, Bool.true_or]) (atE ?_ (at_joinL hu4))
    simp only [EJ, hd, Bool.false_eq_true, ↓reduceIte]

end run

end M0Crypto.Release.Ed25519DecompressStitch
