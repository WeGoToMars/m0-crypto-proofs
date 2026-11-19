import M0Crypto.Release.Ed25519CallProgGood
import M0Crypto.Release.Ed25519CallProgAdapt
import M0Crypto.Release.Ed25519Routines
import M0Crypto.Release.Ed25519CallProgCall
import M0Crypto.Release.Ed25519CallProgFrame

set_option linter.unusedSimpArgs false

/-!
# Call programs: callees whose body is a call program

A callee of the generator's `emit_fn` form is `push {lr}; sub sp, #top`, a call program, then
`add sp, #top; pop {pc}`; a frame above 508 bytes takes two `sub sp` and two `add sp` steps. Its pointer arguments are external buffers and its public parameters
are registers. `CalleeP.adE` builds its adapter with its byte effect from the decided checks
(`CalleeP.ok`, `CalleeP.codeOk`) and the adapters of its callees. The routine's result is the
program's values (`CalleeP.post`), and the one routine-specific lemma relates them to the
interface's semantics.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry InStackWindow)
open M0Crypto.Sym (SExpr)

/-! ## Traces exist -/

section ex
open Tr
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo}
variable {T : A → Word → (Nat → Word) → List Event} {c : Ctx}

theorem loopTr_ex {bt : TrP → TrP} (hb : ∀ Ψ, Ex Ψ → Ex (bt Ψ)) {D : List Event} {bc bb : Event}
    {Ψk : TrP} (hk : Ex Ψk) : ∀ n, Ex (loopTr bt D bc bb Ψk n)
  | 0 => ex_is _
  | n + 1 => hb _ (ex_cat (ex_is _) (ex_cat (ex_is _) (ex_cond hk (ex_cat (ex_is _) (loopTr_ex hb hk n)))))

theorem getD_ex : ∀ {Ψs : List TrP}, (∀ Ψ ∈ Ψs, Ex Ψ) → ∀ l, Ex (Ψs.getD l (is []))
  | [], _, _ => ex_is _
  | _ :: _, h, 0 => h _ List.mem_cons_self
  | _ :: Ψs, h, l + 1 => getD_ex (Ψs := Ψs) (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ)) l

theorem whTr_ex {tb : St → Option St} {bt : St → TrP → List TrP → TrP} {kt : St → TrP} {back : TrP → TrP}
    {Ψs : List TrP} (hb : ∀ s Ψ Ψs', Ex Ψ → (∀ x ∈ Ψs', Ex x) → Ex (bt s Ψ Ψs'))
    (hk : ∀ s, Ex (kt s)) (hback : ∀ Ψ, Ex Ψ → Ex (back Ψ)) (hs : ∀ x ∈ Ψs, Ex x) :
    ∀ n st, Ex (whTr tb bt kt back Ψs n st)
  | 0, _ => ex_is _
  | n + 1, st => by
    simp only [whTr]
    split
    · exact hb _ _ _ (hback _ (whTr_ex hb hk hback hs n _)) fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hk _
        · exact hs x hx
    · exact ex_is _

/-- **A program's trace condition admits a trace.** -/
theorem Prog.tr_ex : ∀ (P : Prog A Bk) (o : Nat) (st : St) {Ψ : TrP} {J : List Nat} {Ψs : List TrP}, Ex Ψ →
    (∀ x ∈ Ψs, Ex x) → Ex (Prog.tr cE bE G T c P o st Ψ J Ψs)
  | .nil, _, _, _, _, _, h, _ => h
  | .op x k, o, st, _, J, _, h, hs => by
    have := Prog.tr_ex k (o + x.size cE bE) ((x.ty cE bE G st).getD st) (J := J) h hs
    cases x with
    | ld r l => cases l <;> simp only [Prog.tr, Op.tr] <;> repeat (first | assumption | exact ex_is _ | apply ex_cat)
    | _ => simp only [Prog.tr, Op.tr] <;> repeat (first | assumption | exact ex_is _ | apply ex_cat)
  | .loop cnt n b k, o, st, _, _, _, h, hs => by
    simp only [Prog.tr]
    exact ex_cat (ex_is _) (loopTr_ex (fun Ψ hΨ => Prog.tr_ex b _ _ hΨ (fun _ h => absurd h List.not_mem_nil))
      (Prog.tr_ex k _ _ h hs) n)
  | .sel w i p₀ p₁ k, o, st, _, _, _, h, hs => by
    simp only [Prog.tr]
    have hn : ∀ x ∈ ([] : List TrP), Ex x := fun _ h => absurd h List.not_mem_nil
    exact ex_cat (ex_is _) (ex_cat (ex_is _) (ex_cond
      (Prog.tr_ex p₀ _ _ (ex_cat (ex_is _) (Prog.tr_ex k _ _ h hs)) hn) (ex_cat (ex_is _)
        (Prog.tr_ex p₁ _ _ (ex_cat (ex_is _) (Prog.tr_ex k _ _ h hs)) hn))))
  | .xit g s cc sh l k, o, st, _, J, Ψs, h, hs => by
    have hk : ∀ st', Ex (Prog.tr cE bE G T c k (o + xitSz g s + xbSz sh) st' _ J Ψs) :=
      fun st' => Prog.tr_ex k _ st' h hs
    have := getD_ex hs l
    simp only [Prog.tr]
    cases s <;> cases sh <;> simp only [xitT, Op.tr, ↓reduceIte, Bool.false_eq_true] <;>
      repeat (first | assumption | exact hk _ | exact ex_is _ | apply ex_cat | apply ex_cond)
  | .hd b h k, o, st, _, J, Ψs, hΨ, hs => by
    simp only [Prog.tr]
    split
    · refine Prog.tr_ex b _ _ ?_ fun x hx => ?_
      · split
        · exact Prog.tr_ex k _ _ hΨ hs
        · exact ex_cat (ex_is _) (Prog.tr_ex k _ _ hΨ hs)
      · rcases List.mem_cons.mp hx with rfl | hx
        · split
          · exact Prog.tr_ex h _ _ (Prog.tr_ex k _ _ hΨ hs) hs
          · exact ex_is _
        · exact hs x hx
    · exact ex_is _
  | .wh n b k, o, st, _, J, Ψs, h, hs => by
    simp only [Prog.tr]
    exact whTr_ex (fun _ _ _ h1 h2 => Prog.tr_ex b _ _ h1 h2) (fun _ => Prog.tr_ex k _ _ h hs)
      (fun _ h1 => ex_cat (ex_is _) h1) hs n st

end ex

/-! ## The callee form -/

/-- **A callee whose body is a call program** `P` in a frame of `top` bytes. `xr` are its pointer
arguments with their buffers (external buffer `i` is `xr[i]`), `pr` its public parameters, `cb`
the code constants it reads (offset, length), the buffers after the arguments'. -/
structure CalleeP (A Bk : Type) where
  s : CalleeS
  P : Prog A Bk
  top : Nat
  xr : List (Reg × XInfo)
  pr : List Reg
  cb : List (Nat × Nat) := []
  /-- The bounded buffers: `(i, k)` for buffer `xr[i]`, whose entry bytes hold the refined kind `k`. -/
  sc : List (Nat × Kd) := []

namespace CalleeP
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (q : CalleeP A Bk)

/-- The body's geometry: the window below the saved `lr`, the frame, the buffers. -/
def geo : Geo :=
  { N := q.s.stack - 4, top := q.top, xs := q.xr.map (·.2) ++ q.cb.map fun x => ⟨.k x.2, false, true, true⟩,
    cs := q.s.code, cd := q.cb.mapIdx fun j x => (q.xr.length + j, x.1), xv := q.sc }

/-- The registers at the body's start. -/
def σ0 : List (Reg × SV) :=
  (q.xr.mapIdx fun i x => (x.1, SV.ext i 0)) ++ (q.pr.mapIdx fun j r => (r, SV.prm j)) ++ [(13, .sp 0)]

def st0 : St := { Γ := [], σ := q.σ0, X := [] }

/-- The run's context at public values `p`. -/
def ctx (base : Word) (p : Nat → Word) : Ctx :=
  ⟨base, q.s.reg p 13 - 4#32, fun i => if i < q.xr.length then q.s.reg p ((q.xr.map (·.1)).getD i 0) else
    base + BitVec.ofNat 32 ((q.cb.map (·.1)).getD (i - q.xr.length) 0), fun j => q.s.reg p (q.pr.getD j 0)⟩

/-- The frame's first `sub sp` step in words, at most 127. -/
def k1 : Nat := min (q.top / 4) 127
/-- The frame's second `sub sp` step in words, or none (`0`). -/
def k2 : Nat := q.top / 4 - q.k1
/-- The frame's steps. -/
def ks : List Nat := q.k1 :: if q.k2 = 0 then [] else [q.k2]
/-- The bytes of the `sub sp` steps. -/
def pro : Nat := 2 * q.ks.length

def body : Nat := q.s.entry + 2 + q.pro
def epi : Nat := q.body + q.P.size cE bE

/-- The frame's trace around the body's trace `Ψ`: the `sub sp` steps, `Ψ`, the `add sp` steps. -/
def frTr (base : Word) (Ψ : TrP) : TrP :=
  if q.k2 = 0 then
    Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 2), .subSp (BitVec.ofNat 7 q.k1), []⟩])
      (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 (q.epi cE bE), .addSp (BitVec.ofNat 7 q.k1), []⟩]))
  else
    Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 2), .subSp (BitVec.ofNat 7 q.k1), []⟩])
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 4), .subSp (BitVec.ofNat 7 q.k2), []⟩])
        (Tr.cat Ψ (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.epi cE bE), .addSp (BitVec.ofNat 7 q.k1), []⟩])
          (Tr.is [⟨base + BitVec.ofNat 32 (q.epi cE bE + 2), .addSp (BitVec.ofNat 7 q.k2), []⟩]))))

/-- **The trace** at public values `p`: the frame's events around the body's. -/
def tr (T : A → Word → (Nat → Word) → List Event) (base : Word) (p : Nat → Word) : TrP :=
  let sp := q.s.reg p 13
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 q.s.entry, .push 0 true,
      wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩])
    (Tr.cat (q.frTr cE bE base (Prog.tr cE bE q.geo T (q.ctx base p) q.P q.body q.st0 (Tr.is []) [] []))
      (Tr.is [⟨base + BitVec.ofNat 32 (q.epi cE bE + q.pro), .pop 0 true,
        wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩]))

/-- A buffer: a nonzero constant length, written or read through an interface region of its
register, aligned if the interface says so. -/
def xOk (x : Reg × XInfo) : Bool :=
  x.1.val < 13 && PubW.r x.1 ∈ q.s.pubs && (x.2.w || x.2.r) && (!x.2.al4 || x.1 ∈ q.s.io.al) &&
  match x.2.len with
  | .k L => decide (0 < L) && decide (L < 2 ^ 32) && (!x.2.w || SRgn.mk x.1 0 (.k L) ∈ q.s.io.wr) &&
      (!x.2.r || SRgn.mk x.1 0 (.k L) ∈ q.s.io.rd)
  | .p _ => false

/-- An output: a view of its byte kind, other than a context or a public word, at a buffer, live
at the end. -/
def outOk (Γ : List (Loc × Kd)) (x : Reg × Nat × Kd) : Bool :=
  x.1.val < 13 && !(x.2.2 matches .ctx _ | .pw _ | .cw) && match locOf q.σ0 x.1 x.2.1 with
  | some l => l.isEx && Γ.any fun p => decide (p.1 = l) && p.2 != .pt && decide (p.2.base = x.2.2.base)
  | none => false

/-- A buffer's bytes as a symbolic region. -/
def bufE (x : Reg × XInfo) : Option (SExpr × Nat) :=
  match x.2.len with | .k L => some (rgnE x.1 0 L) | .p _ => none

/-- The bytes the callee accesses outside its stack, those it reads first and those it writes. -/
def fpE : List (SExpr × Nat) := q.xr.filterMap bufE
def iniE : List (SExpr × Nat) := (q.xr.filter (·.2.r)).filterMap bufE
def woE : List (SExpr × Nat) := q.s.io.outs.filterMap outE

/-- A bounded buffer: a readable buffer of at least 32 bytes whose register is an input of its
refined kind. -/
def scOk (p : Nat × Kd) : Bool :=
  match q.xr[p.1]? with
  | some x => p.2.isRef && x.2.r && (match x.2.len with | .k L => decide (32 ≤ L) | .p _ => false) &&
      decide ((x.1, 0, In.view p.2) ∈ q.s.io.ins)
  | none => false

/-- **The decided checks of the callee form**, the same in both builds. -/
def ok : Bool :=
  q.sc.all q.scOk && q.top % 4 == 0 && decide (q.top / 4 < 255) && decide (4 + q.top ≤ q.s.stack) && q.s.entry % 2 == 0 &&
  PubW.r 13 ∈ q.s.pubs && q.xr.all q.xOk && q.pr.all (fun r => r.val < 13 && PubW.r r ∈ q.s.pubs) &&
  effOk q.s.io q.fpE q.iniE q.woE && subR q.woE q.fpE &&
  match q.P.ty cE bE q.geo q.st0 with
  | some st' => q.P.eok cE bE q.geo q.st0 && st'.ex == none && q.s.io.outs.all (q.outOk st'.Γ)
  | none => false

/-- **The decided checks of the callee's code** in a build with the data ranges `D`: each island
the body skips is one of them. -/
def codeOk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] (D : List (Nat × Nat)) : Bool :=
  seqAt B q.s.entry (.push 0 true :: q.ks.map fun k => .subSp (BitVec.ofNat 7 k)) &&
  seqAt B (q.epi cE bE) (q.ks.map (fun k => .addSp (BitVec.ofNat 7 k)) ++ [.pop 0 true]) &&
  q.P.bok cE bE q.geo [] q.body && piecesAt B q.body (Prog.emit cE bE [] q.body q.P) &&
  rangesSub [(q.s.entry, q.s.entry + 2 + q.pro), (q.epi cE bE, q.epi cE bE + 2 + q.pro)] q.s.code &&
  decide (q.epi cE bE + 2 + q.pro ≤ BS) && q.epi cE bE % 2 == 0 &&
  q.cb.all (fun x => x.1 % 4 == 0 && decide (0 < x.2) && decide (x.1 + x.2 ≤ BS)) &&
  (pieceDat q.body (Prog.emit cE bE [] q.body q.P)).all (· ∈ D)

/-- The values of the outputs, from the program's values `E`. -/
def outVals (E : Loc → V) : List V :=
  q.s.io.base.outs.map fun x => ((locOf q.σ0 x.1 x.2.1).map E).getD .none

variable (Rs : Rels) (semA : A → List V → List V) (semB : Bk → List V → List V)

/-- **The callee's result**: memory `m` holds the program's values at the outputs, run from a
memory `m0` that holds the code at `base` and agrees with the entry memory on the readable
buffers, with the entry registers meeting the interface. -/
def post {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (s : State) (m : Mem) (_ : Word) : Prop :=
  PreG q.s.io s.regs ∧ ∃ base m0, CodeAt m0 base B ∧ (∀ i (x : XInfo), q.geo.xs[i]? = some x → x.r = true → ∀ y, Has (x.rgns (q.ctx base (q.s.pub base s)) i) y →
      m0 y = s.mem y) ∧
    let c := q.ctx base (q.s.pub base s)
    OutsRel Rs c (q.geo.fsp c) q.s.io.base s m
      (q.outVals (Prog.ev cE bE q.geo semA semB c m0 q.P q.st0 fun _ => .none))

/-- **The callee as a routine with the result `Post`** and the premise `xpre` at entry besides the
interface's and the bounded buffers'. -/
def RW (Post : State → Mem → Word → Prop) (xpre : Word → State → Prop) : Routine where
  entry := q.s.entry
  code := q.s.code
  stack := q.s.stack
  Pre := fun base s => (PreG q.s.io s.regs ∧
    ∀ p ∈ q.sc, p.2.Bnd (bytesAt s.mem (s.regs ((q.xr.map (·.1)).getD p.1 0)) 32)) ∧ xpre base s
  wr := fun s => rgnsC s.regs q.s.io.wr
  rd := fun s => rgnsC s.regs q.s.io.rd
  Post := Post
  clob := Ed25519Routines.hiRegs

/-- The callee as a routine. -/
def R {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] : Routine :=
  q.RW (q.post cE bE Rs semA semB) fun _ _ => True

/-! ## The decided checks, unfolded -/

variable {cE bE q}

theorem xOk_parts {x : Reg × XInfo} (h : q.xOk x = true) : ∃ L, x.2.len = .k L ∧ 0 < L ∧ L < 2 ^ 32 ∧
    x.1.val < 13 ∧ PubW.r x.1 ∈ q.s.pubs ∧ (x.2.w = true ∨ x.2.r = true) ∧ (x.2.al4 = true → x.1 ∈ q.s.io.al) ∧
    (x.2.w = true → SRgn.mk x.1 0 (.k L) ∈ q.s.io.wr) ∧ (x.2.r = true → SRgn.mk x.1 0 (.k L) ∈ q.s.io.rd) := by
  unfold xOk at h
  split at h
  · rename_i L hL
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨h13, hp⟩, hwr⟩, hal⟩, ⟨⟨h0, hL32⟩, hw⟩, hr⟩ := h
    refine ⟨L, hL, h0, hL32, h13, hp, hwr, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simpa [h] using hal
    · simpa [h] using hw
    · simpa [h] using hr
  · simp at h

structure OkP (q : CalleeP A Bk) (cE : A → CalleeS) (bE : Bk → BlockS) (st' : St) : Prop where
  t4 : q.top % 4 = 0
  k : q.top / 4 < 255
  stk : 4 + q.top ≤ q.s.stack
  e2 : q.s.entry % 2 = 0
  p13 : PubW.r 13 ∈ q.s.pubs
  xs : ∀ x ∈ q.xr, q.xOk x = true
  ps : ∀ r ∈ q.pr, r.val < 13 ∧ PubW.r r ∈ q.s.pubs
  eff : effOk q.s.io q.fpE q.iniE q.woE = true
  wf : subR q.woE q.fpE = true
  ty : q.P.ty cE bE q.geo q.st0 = some st'
  eok : q.P.eok cE bE q.geo q.st0 = true
  exf : st'.ex = none
  outs : ∀ x ∈ q.s.io.outs, q.outOk st'.Γ x = true
  sc : ∀ p ∈ q.sc, q.scOk p = true

/-- The frame's decided checks. -/
structure OkF (q : CalleeP A Bk) : Prop where
  t4 : q.top % 4 = 0
  k : q.top / 4 < 255
  stk : 4 + q.top ≤ q.s.stack
  e2 : q.s.entry % 2 = 0
  p13 : PubW.r 13 ∈ q.s.pubs
  xs : ∀ x ∈ q.xr, q.xOk x = true
  ps : ∀ r ∈ q.pr, r.val < 13 ∧ PubW.r r ∈ q.s.pubs
  sc : ∀ p ∈ q.sc, q.scOk p = true

theorem OkP.toF {st' : St} (ho : OkP q cE bE st') : OkF q := ⟨ho.t4, ho.k, ho.stk, ho.e2, ho.p13, ho.xs, ho.ps, ho.sc⟩

theorem ok_parts (h : q.ok cE bE = true) : ∃ st', OkP q cE bE st' := by
  unfold ok at h
  split at h
  · rename_i st' hty
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, ⟨h10, hx⟩, h11⟩ := h
    exact ⟨st', h1, h2, h3, h4, h5, h6, fun r hr => by simpa using h7 r hr, h8, h9, hty, h10, by simpa using hx, h11, h0⟩
  · simp at h

/-! ## Registers and buffers -/

theorem reg_pub {s : CalleeS} {base : Word} {st : State} {r : Reg} (h : PubW.r r ∈ s.pubs) :
    s.reg (s.pub base st) r = st.regs r := getD_idxOf (PubW.get st) 0 h

theorem ctx_ptr {base : Word} {p : Nat → Word} {i : Nat} (h : i < q.xr.length) :
    (q.ctx base p).ptr i = q.s.reg p q.xr[i].1 := by
  simp [ctx, List.getD_eq_getElem?_getD, h]

theorem getD_fst {i : Nat} (h : i < q.xr.length) : (q.xr.map (·.1)).getD i 0 = q.xr[i].1 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem ctx_prm {base : Word} {p : Nat → Word} {j : Nat} (h : j < q.pr.length) :
    (q.ctx base p).prm j = q.s.reg p q.pr[j] := by
  simp [ctx, List.getD_eq_getElem?_getD, h]

theorem ctx_code {base : Word} {p : Nat → Word} {j : Nat} (h : j < q.cb.length) :
    (q.ctx base p).ptr (q.xr.length + j) = base + BitVec.ofNat 32 q.cb[j].1 := by
  have : ¬ q.xr.length + j < q.xr.length := by omega
  simp [ctx, List.getD_eq_getElem?_getD, h, this]

/-- A buffer of the geometry is an argument's or a code constant's. -/
theorem xs_cases {i : Nat} {x : XInfo} (hi : q.geo.xs[i]? = some x) : (q.xr.map (·.2))[i]? = some x ∨
    ∃ j, ∃ h : j < q.cb.length, i = q.xr.length + j ∧ x = ⟨.k q.cb[j].2, false, true, true⟩ := by
  simp only [geo, List.getElem?_append, List.length_map] at hi
  split at hi
  · exact .inl hi
  · simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨y, hy, rfl⟩ := hi
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    exact .inr ⟨_, h, by omega, rfl⟩

theorem cb_parts {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {D : List (Nat × Nat)} (hc : q.codeOk cE bE B BS D = true) :
    ∀ x ∈ q.cb, x.1 % 4 = 0 ∧ 0 < x.2 ∧ x.1 + x.2 ≤ BS := by
  simp only [codeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  exact fun x hx => and_assoc.1 (hc.1.2 x hx)

theorem mem_of_lookup {l : List (Nat × Nat)} {i s : Nat} (h : l.lookup i = some s) : (i, s) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases e : i = a
    · subst e; simp only [List.lookup, show (i == i) = true from beq_self_eq_true i, Option.some.injEq] at h
      simp [h]
    · simp only [List.lookup, show (i == a) = false from beq_false_of_ne e] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem code_toNat {a : Word} {s n : Nat} (h : a.toNat + n ≤ 2 ^ 32) (hs : s < n) :
    (a + BitVec.ofNat 32 s).toNat = a.toNat + s := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem region_in {a y : Word} {s m N : Nat} (h : Region (a + BitVec.ofNat 32 s) m y) (hs : s + m ≤ N)
    (hN : N < 2 ^ 32) : Region a N y := by
  simp only [Region] at h ⊢; bv_omega

/-- The registers at the body's start hold `σ0`. -/
theorem holds_σ0 {base : Word} {p : Nat → Word} {sp : Word} {regs : Reg → Word} (ho : OkF q)
    (hx : ∀ r : Reg, r.val < 13 → PubW.r r ∈ q.s.pubs → regs r = q.s.reg p r) (h13 : regs 13 = sp) :
    Holds (q.ctx base p) sp q.σ0 regs := by
  intro e he
  simp only [σ0, List.mem_append, List.mem_singleton, List.mem_mapIdx] at he
  rcases he with (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | rfl
  · obtain ⟨L, -, -, -, h1, hp, -⟩ := xOk_parts (ho.xs _ (List.getElem_mem hi))
    exact ⟨Nat.lt_of_lt_of_le h1 (by decide), by simp [SV.val, hx _ h1 hp, ctx_ptr hi]⟩
  · obtain ⟨h1, hp⟩ := ho.ps _ (List.getElem_mem hj)
    exact ⟨Nat.lt_of_lt_of_le h1 (by decide), by simp [SV.val, hx _ h1 hp, ctx_prm hj]⟩
  · exact ⟨by decide, by simp [SV.val, h13]⟩

/-- **A buffer of the geometry**: its register, its regions as the interface region's, and the
bytes of its region as the symbolic buffer's. -/
theorem buf_of (ho : OkF q) {i : Nat} {x : XInfo} (hi : (q.xr.map (·.2))[i]? = some x) :
    ∃ (h : i < q.xr.length) (L : Nat), q.xr[i].2 = x ∧ x.len = .k L ∧ 0 < L ∧ L < 2 ^ 32 ∧
      q.xr[i].1.val < 13 ∧ PubW.r q.xr[i].1 ∈ q.s.pubs ∧ (x.w = true ∨ x.r = true) ∧
      (x.al4 = true → q.xr[i].1 ∈ q.s.io.al) ∧ (x.w = true → SRgn.mk q.xr[i].1 0 (.k L) ∈ q.s.io.wr) ∧
      (x.r = true → SRgn.mk q.xr[i].1 0 (.k L) ∈ q.s.io.rd) ∧ bufE q.xr[i] = some (rgnE q.xr[i].1 0 L) := by
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨y, hy, rfl⟩ := hi
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hy
  obtain ⟨L, hL, h0, h32, h13, hp, hwr, hal, hw, hr⟩ := xOk_parts (ho.xs _ (List.getElem_mem h))
  exact ⟨h, L, rfl, hL, h0, h32, h13, hp, hwr, hal, hw, hr, by simp [bufE, hL]⟩

theorem rgns_eq {c : Ctx} {i L : Nat} {x : XInfo} {a : Word} (hL : x.len = .k L) (h0 : 0 < L) (ha : c.ptr i = a) :
    x.rgns c i = [⟨a, L⟩] := by
  simp [XInfo.rgns, hL, XLen.v, ha, show L ≠ 0 by omega]

theorem rgnC_mem {regs : Reg → Word} {l : List SRgn} {r : Reg} {L : Nat} (h : SRgn.mk r 0 (.k L) ∈ l) (h0 : 0 < L) :
    (⟨regs r, L⟩ : Rgn) ∈ rgnsC regs l :=
  List.mem_flatMap.2 ⟨_, h, by simp [SRgn.rgnC, ALen.val, show L ≠ 0 by omega]⟩

theorem inR_buf {t : State} {l : List (Reg × XInfo)} {x : Reg × XInfo} {L : Nat} {y : Word} (hx : x ∈ l)
    (he : bufE x = some (rgnE x.1 0 L)) (hy : Region (t.regs x.1) L y) : InR t (l.filterMap bufE) y :=
  ⟨_, List.mem_filterMap.2 ⟨x, hx, he⟩, (y - t.regs x.1).toNat, hy, by
    show y = t.regs x.1 + BitVec.ofNat 32 0 + _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega⟩

theorem sub_toNat {a : Word} {k : Nat} (h : k ≤ a.toNat) : (a - BitVec.ofNat 32 k).toNat = a.toNat - k := by
  bv_omega

theorem sp_sub4 (sp : Word) {k : Nat} (h : 4 ≤ k) : sp - 4#32 - BitVec.ofNat 32 (k - 4) = sp - BitVec.ofNat 32 k := by
  rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_ofNat, Nat.add_sub_cancel' h]

theorem k1_lt : q.k1 < 128 := by simp only [k1]; omega

theorem k2_lt (ho : OkF q) : q.k2 < 128 := by have := ho.k; simp only [k2, k1]; omega

theorem k12 (ho : OkF q) : 4 * q.k1 + 4 * q.k2 = q.top := by
  have := ho.t4; simp only [k2, k1]; omega

theorem ks_one (h : q.k2 = 0) : q.ks = [q.k1] := by simp [ks, h]

theorem ks_two (h : q.k2 ≠ 0) : q.ks = [q.k1, q.k2] := by simp [ks, h]

theorem fsp_eq1 (ho : OkF q) (h : q.k2 = 0) (sp : Word) :
    sp - BitVec.ofNat 32 (4 * nSaved 0) - BitVec.ofNat 32 (4 * q.k1) = sp - 4#32 - BitVec.ofNat 32 q.top := by
  rw [show 4 * q.k1 = q.top by have := k12 ho; omega]; rfl

theorem fsp_eq2 (ho : OkF q) (sp : Word) :
    sp - BitVec.ofNat 32 (4 * nSaved 0) - BitVec.ofNat 32 (4 * q.k1) - BitVec.ofNat 32 (4 * q.k2) =
      sp - 4#32 - BitVec.ofNat 32 q.top := by
  rw [sub_sub_ofNat _ (4 * q.k1), k12 ho]; rfl

theorem win_mono4 {sp y : Word} {N : Nat} (h : InStackWindow (sp - 4#32) N y) : InStackWindow sp (4 + N) y := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨4 + o, by omega, by rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_ofNat]⟩

/-! ## The run -/

section run
variable {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {D : List (Nat × Nat)}
variable {Rs : Rels} {semA : A → List V → List V} {semB : Bk → List V → List V}

/-- **The body's geometry from the entry state**: the window below the saved `lr`, the buffers
from the interface regions. -/
theorem geoOk {Post : State → Mem → Word → Prop} {xpre : Word → State → Prop} (ho : OkF q)
    (hcb : ∀ x ∈ q.cb, x.1 % 4 = 0 ∧ 0 < x.2 ∧ x.1 + x.2 ≤ BS) {base : Word} {s : State} {p : Nat → Word}
    (hpr : ∀ r, PubW.r r ∈ q.s.pubs → q.s.reg p r = s.regs r) (e : (q.RW Post xpre).Entry base s) :
    GeoOk (q.ctx base p) q.geo (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr)
      (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd) := by
  have h13 := hpr 13 ho.p13
  have hst := ho.stk; have hroom : q.s.stack ≤ (s.regs 13).toNat := e.room; have hs4 := e.sp4; have := (s.regs 13).isLt
  have e4 : (s.regs 13 - 4#32).toNat = (s.regs 13).toNat - 4 := sub_toNat (k := 4) (by omega)
  have eS : (s.regs 13 - BitVec.ofNat 32 q.s.stack).toNat = (s.regs 13).toNat - q.s.stack := sub_toNat hroom
  have hw : q.geo.win (q.ctx base p) = ⟨s.regs 13 - BitVec.ofNat 32 q.s.stack, q.s.stack - 4⟩ := by
    simp only [Geo.win, ctx, h13, geo]; rw [sp_sub4 _ (by omega)]
  have hsub : ∀ l, (⟨s.regs 13 - BitVec.ofNat 32 q.s.stack, q.s.stack⟩ : Rgn) ∈ l →
      Sub [q.geo.win (q.ctx base p)] l := fun l hl => by
    rw [hw]; intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hl, Nat.le_refl _, by dsimp only; omega, by dsimp only; omega⟩
  refine ⟨by simp only [ctx, h13]; omega, by simp only [geo, ctx, h13]; omega, by simp only [geo]; omega,
    ho.t4, ?_, hsub _ (List.mem_cons_of_mem _ List.mem_cons_self), fun i x hi => ?_, fun i x hi => by simp [geo] at hi,
    fun i o h => ?_, fun i o h x hx => ?_⟩
  · rw [hw]; refine sub_one List.mem_cons_self ?_; dsimp only; omega
  rotate_left
  · obtain ⟨j, hj, he⟩ := List.mem_mapIdx.1 (mem_of_lookup (by simpa only [geo] using h))
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact ctx_code hj
  · obtain ⟨j, hj, he⟩ := List.mem_mapIdx.1 (mem_of_lookup (by simpa only [geo] using h))
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rcases xs_cases hx with hx | ⟨j', hj', hjj, rfl⟩
    · have := (List.getElem?_eq_some_iff.mp hx).1; simp only [List.length_map] at this; omega
    obtain rfl : j = j' := by omega
    have hp := ctx_code (base := base) (p := p) hj
    obtain ⟨h4, hL0, hBS⟩ := hcb _ (List.getElem_mem hj)
    have hcd : Frame.Disj base BS (s.regs 13 - BitVec.ofNat 32 q.s.stack) q.s.stack :=
      e.sepCode _ (List.mem_singleton_self _) _ List.mem_cons_self
    have ht := code_toNat hcd.1 (show q.cb[j].1 < BS by omega)
    refine Sub.sep (g := [codeR base]) (fun r hr => ?_) (Caller.of_entry (mask := 0) e).codeW
    simp only [XInfo.rgns, XLen.v, show q.cb[j].2 ≠ 0 by omega, ↓reduceIte, List.mem_singleton] at hr; subst hr
    exact ⟨codeR base, List.mem_singleton_self _, by simp only [codeR, hp, ht]; omega,
      by simp only [codeR, hp, ht]; omega, hcd.1⟩
  rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
  rotate_left
  · have hp := ctx_code (base := base) (p := p) hj
    obtain ⟨h4, hL0, hBS⟩ := hcb _ (List.getElem_mem hj)
    have hcd : Frame.Disj base BS (s.regs 13 - BitVec.ofNat 32 q.s.stack) q.s.stack :=
      e.sepCode _ (List.mem_singleton_self _) _ List.mem_cons_self
    have ht := code_toNat hcd.1 (show q.cb[j].1 < BS by omega)
    refine ⟨.inr ?_, nofun, fun _ r hr => ?_, fun _ => ?_⟩
    · simp only [XLen.v, hp]; rw [show (q.ctx base p).sp0 - BitVec.ofNat 32 q.geo.N =
        s.regs 13 - BitVec.ofNat 32 q.s.stack from congrArg Rgn.a hw]
      exact Disj.shrink ⟨by rw [ht]; have := hcd.1; omega, hcd.2.1, by rw [ht]; have := hcd.2.2; omega⟩ (by simp [geo])
    · simp only [XInfo.rgns, XLen.v, show q.cb[j].2 ≠ 0 by omega, ↓reduceIte, List.mem_singleton] at hr; subst hr
      exact ⟨codeR base, List.mem_cons_self, by simp only [codeR, hp, ht]; omega,
        by simp only [codeR, hp, ht]; omega, hcd.1⟩
    · rw [hp, ht]; have := e.base4; omega
  obtain ⟨h, L, rfl, hL, h0, hL32, hr13, hpub, hwr, hal, hW, hR, -⟩ := buf_of ho hi
  have hp : (q.ctx base p).ptr i = s.regs q.xr[i].1 := by rw [ctx_ptr h, hpr _ hpub]
  have hd : Frame.Disj (s.regs q.xr[i].1) L (s.regs 13 - BitVec.ofNat 32 q.s.stack) q.s.stack := by
    rcases hwr with hw' | hr'
    · exact e.sepWr _ (rgnC_mem (hW hw') h0) _ (List.mem_singleton_self _)
    · exact e.sepRd _ (rgnC_mem (hR hr') h0) _ (List.mem_singleton_self _)
  refine ⟨.inr ?_, fun hw' => ?_, fun hr' => ?_, fun ha => ?_⟩
  · have := hw ▸ (rfl : (q.geo.win (q.ctx base p)).a = _)
    simp only [XLen.v, hL, hp]; rw [show (q.ctx base p).sp0 - BitVec.ofNat 32 q.geo.N =
      s.regs 13 - BitVec.ofNat 32 q.s.stack from congrArg Rgn.a hw]
    exact Disj.shrink hd (by simp [geo])
  · rw [rgns_eq hL h0 hp]; exact sub_one (List.mem_cons_of_mem _ (rgnC_mem (hW hw') h0)) hd.1
  · rw [rgns_eq hL h0 hp]
    exact sub_one (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (rgnC_mem (hR hr') h0))) hd.1
  · rw [hp]; exact e.pre.1.1.1 _ (hal ha)

theorem _root_.M0Crypto.Release.Ed25519CallProg.Kd.ini_base (c : Ctx) (sp : Word) (k : Kd) :
    k.base.ini c sp = k.ini c sp := by cases k <;> rfl

/-- A value of a refined byte kind is one of its byte kind. -/
theorem _root_.M0Crypto.Release.Ed25519CallProg.Rel.base {Rs : Rels} {c : Ctx} {sp : Word} {k : Kd} {m : Mem}
    {a : Word} {v : V} (hk : k ≠ .pt) (h : Rel Rs c sp k m a v) : Rel Rs c sp k.base m a v := by
  cases k <;> cases v <;> first | exact h | exact h.1 | exact absurd rfl hk

theorem outOk_parts {Γ : List (Loc × Kd)} {x : Reg × Nat × Kd} (h : q.outOk Γ x = true) :
    x.1.val < 13 ∧ (x.2.2 matches .ctx _ | .pw _ | .cw) = false ∧
      ∃ l k, locOf q.σ0 x.1 x.2.1 = some l ∧ (l, k) ∈ Γ ∧ k ≠ .pt ∧ k.base = x.2.2.base := by
  unfold outOk at h
  cases hl : locOf q.σ0 x.1 x.2.1 with
  | none => simp [hl] at h
  | some l =>
    simp only [hl, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_true] at h
    obtain ⟨⟨h1, h2⟩, -, ⟨l', k⟩, hm, ⟨rfl, hp⟩, hk⟩ := h
    exact ⟨h1, h2, l', k, rfl, hm, by simpa using hp, hk⟩

theorem all2_map {α β : Type} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (f x)) → All2 R l (l.map f)
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, all2_map fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- **The callee's call lemma** with the frame's trace around the program's, from the decided
checks and the adapters of its callees. -/
theorem run (ads : ∀ a, Ad Rs B BS (cE a)) (bds : ∀ b, Bd Rs (bE b)) {st' : St} (ho : OkP q cE bE st')
    (hc : q.codeOk cE bE B BS D = true) (base : Word) (s : State)
    (e : (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).Entry base s) :
    ReachFT base (PcIn base q.s.code) ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).RdP base s)
      ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).WrP s)
      ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).SpP s) s
      ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).Ret s)
      (q.tr cE bE (fun a => (ads a).T) base (q.s.pub base s)) := by
  have h13 := reg_pub (base := base) (st := s) ho.p13
  have hcb := cb_parts hc
  have g := geoOk ho.toF (cb_parts hc) (p := q.s.pub base s) (fun _ h => reg_pub h) e
  simp only [codeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hen, hep⟩, hbok⟩, hpc⟩, hrs⟩, hBS⟩, he2⟩, -⟩, -⟩ := hc
  have n0 : 4 * nSaved 0 = 4 := by decide
  have hst := ho.stk; have hroom : q.s.stack ≤ (s.regs 13).toNat := e.room; have := (s.regs 13).isLt
  have hk12 := k12 ho.toF; have hk1 := k1_lt (q := q); have hk2 := k2_lt ho.toF
  have hsz : ∀ k, Instr.size (.subSp k) = 2 ∧ Instr.size (.addSp k) = 2 := fun _ => ⟨rfl, rfl⟩
  suffices hbody : ∀ t : State, t.pc = base + BitVec.ofNat 32 q.body →
      t.regs 13 = s.regs 13 - 4#32 - BitVec.ofNat 32 q.top →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved 0 s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).PcP base) ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).RdP base s) (Has (lowWin (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)) 0 s :: (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).wr s)) ((q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 (q.epi cE bE) ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves 0 r → r ∉ (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).clob → u.regs r = s.regs r) ∧
          (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).Post s u.mem (u.regs 0))
        (Prog.tr cE bE q.geo (fun a => (ads a).T) (q.ctx base (q.s.pub base s)) q.P q.body q.st0 (Tr.is []) [] []) by
    unfold tr frTr
    by_cases hk : q.k2 = 0
    · have hpro : q.pro = 2 := by simp [pro, ks_one hk]
      rw [ks_one hk] at hen hep
      simp only [seqAt, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, (hsz _).1, (hsz _).2, show Instr.size (.push 0 true) = 2 from rfl] at hen hep
      obtain ⟨⟨hpush, -⟩, ⟨hsub, -⟩, -⟩ := hen
      obtain ⟨⟨hadd, -⟩, ⟨hpop, -⟩, -⟩ := hep
      rw [hpro] at hrs hBS
      rw [ite_eq_left hk, hpro]
      have hent : q.s.entry + 4 ≤ BS := by simp only [epi, body, hpro] at hBS; omega
      refine ReachFT.frameK (f := (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem))) (mask := 0) (k := q.k1) (by decide) hpush hsub hadd hpop ho.e2 he2 hBS hent
        hrs hk1 (by rw [n0]; show 4 + 4 * q.k1 ≤ q.s.stack; omega) e h13.symm
        fun t tpc t13 tr hm hcd => hbody t ?_ ?_ tr hm hcd
      · rw [tpc]; simp only [body, hpro]; rfl
      · rw [t13, ← sub_sub_ofNat, fsp_eq1 ho.toF hk]
    · have hpro : q.pro = 4 := by simp [pro, ks_two hk]
      rw [ks_two hk] at hen hep
      simp only [seqAt, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, (hsz _).1, (hsz _).2, show Instr.size (.push 0 true) = 2 from rfl,
        Nat.add_assoc] at hen hep
      obtain ⟨⟨hpush, -⟩, ⟨hsub, -⟩, ⟨hsub2, -⟩, -⟩ := hen
      obtain ⟨⟨hadd, -⟩, ⟨hadd2, -⟩, ⟨hpop, -⟩, -⟩ := hep
      rw [hpro] at hrs hBS
      rw [ite_eq_right hk, hpro]
      have hent : q.s.entry + 6 ≤ BS := by simp only [epi, body, hpro] at hBS; omega
      refine ReachFT.frameK2 (f := (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem))) (mask := 0) (k1 := q.k1) (k2 := q.k2) (by decide) hpush hsub hsub2 hadd hadd2
        hpop ho.e2 he2 (by omega) hent hrs hk1 hk2 (by rw [n0]; show 4 + 4 * q.k1 + 4 * q.k2 ≤ q.s.stack; omega) e
        h13.symm fun t tpc t13 tr hm hcd => hbody t ?_ ?_ tr hm hcd
      · rw [tpc]; simp only [body, hpro]; rfl
      · rw [t13, ← sub_sub_ofNat, ← sub_sub_ofNat, fsp_eq2 ho.toF]
  intro t tpc t13 tr hm hcd
  have F := Caller.of_entry (mask := 0) e
  have F' : Caller (q.ctx base (q.s.pub base s)).base (q.ctx base (q.s.pub base s)).sp0 q.geo.N
      (lowWin (q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)) 0 s :: rgnsC s.regs q.s.io.wr) :=
    ⟨F.b4, g.sp4, g.room, F.codeW, F.code32⟩
  have hf : t.regs 13 = q.geo.fsp (q.ctx base (q.s.pub base s)) := by
    rw [t13]; simp only [Geo.fsp, ctx, geo, h13]
  have hH : Holds (q.ctx base (q.s.pub base s)) (q.geo.fsp (q.ctx base (q.s.pub base s))) q.σ0 t.regs :=
    holds_σ0 ho.toF (fun r h1 hp => by rw [tr r (by omega) (by omega), reg_pub hp]) hf
  have hrd : ∀ i (x : XInfo), q.geo.xs[i]? = some x → x.r = true →
      ∀ y, Has (x.rgns (q.ctx base (q.s.pub base s)) i) y → t.mem y = s.mem y := by
    intro i x hi hr y hy
    have hsv : Sub [saved 0 s] [(q.R cE bE Rs (fun a => (ads a).sem) (fun b => (bds b).sem)).win s] := by
      have := sub_toNat (a := s.regs 13) (k := 4) (by omega)
      have := sub_toNat (a := s.regs 13) (k := q.s.stack) hroom
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by simp only [saved, Routine.win, R, RW, n0]; omega,
        by simp only [saved, Routine.win, R, RW, n0]; omega, by simp only [Routine.win, R, RW]; omega⟩
    rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
    rotate_left
    · obtain ⟨q', hq, hy⟩ := hy
      simp only [XInfo.rgns, XLen.v, show q.cb[j].2 ≠ 0 by have := (hcb _ (List.getElem_mem hj)).2.1; omega, ↓reduceIte,
        List.mem_singleton] at hq; subst hq
      have hN := CodeBytes.lt (B := B); have := (hcb _ (List.getElem_mem hj)).2.2
      rw [ctx_code hj] at hy
      exact hm y (Sep.not_has (Sub.sep hsv fun r hr => e.sepCode.symm r (by
        rw [List.mem_singleton] at hr; exact hr ▸ List.mem_cons_self)) · ⟨_, List.mem_singleton_self _,
        Rgn.of_region (region_in (rgn_region hy (by omega)) this hN)⟩)
    obtain ⟨h, L, rfl, hL, h0, -, -, hpub, -, -, -, hR, -⟩ := buf_of ho.toF hi
    rw [rgns_eq hL h0 (by rw [ctx_ptr h, reg_pub hpub])] at hy
    exact hm y (Sep.not_has (Sub.sep hsv e.sepRd.symm) · ⟨_, rgnC_mem (hR hr) h0, by
      obtain ⟨q', hq', hy⟩ := hy; simp only [List.mem_singleton] at hq'; exact hq' ▸ hy⟩)
  have hxv : ∀ p ∈ q.geo.xv, p.2.Bnd (bytesAt t.mem ((q.ctx base (q.s.pub base s)).ptr p.1) 32) := by
    rintro ⟨i, k⟩ hi
    have hk := ho.sc _ hi
    unfold scOk at hk
    cases hxi : q.xr[i]? with
    | none => simp [hxi] at hk
    | some x =>
      simp only [hxi, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨-, hr⟩, hl⟩, -⟩ := hk
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hxi
      cases hL : q.xr[i].2.len with
      | p _ => simp [hL] at hl
      | k L =>
        simp only [hL, decide_eq_true_eq] at hl
        have hg : q.geo.xs[i]? = some q.xr[i].2 := by
          simp [geo, List.getElem?_append_left, hlt]
        rw [bytesAt_congr (m2 := s.mem) (n := 32) (a := (q.ctx base (q.s.pub base s)).ptr i) fun k hk =>
          hrd i _ hg hr _ ⟨⟨(q.ctx base (q.s.pub base s)).ptr i, L⟩,
            (by rw [rgns_eq hL (by omega) rfl]; exact List.mem_singleton_self _), ⟨k, by show k < L; omega, rfl⟩⟩]
        have hpub := (xOk_parts (ho.xs _ (List.getElem_mem hlt))).choose_spec.2.2.2.2.1
        have hb : k.Bnd (bytesAt s.mem (s.regs ((q.xr.map (·.1)).getD i 0)) 32) :=
          e.pre.1.2 (i, k) (show (i, k) ∈ q.sc from hi)
        rw [getD_fst hlt] at hb
        rw [ctx_ptr hlt, reg_pub hpub]; exact hb
  have hat : At Rs B (q.ctx base (q.s.pub base s)) q.geo t.mem q.body q.st0 (fun _ => .none) t :=
    ⟨tpc, hf, hcd, hH, ⟨fun p hp => by simp [st0] at hp, fun _ _ _ => rfl, hxv⟩, fun r h => by simp [st0] at h⟩
  refine ReachT.mono (prog_run Rs ads bds t.mem g F' (sub_one List.mem_cons_self F.code32) q.P (J := []) (Ψs := []) (rest := [])
    ho.ty rfl hbok (by simpa using hpc) hat (fun _ u hu _ => ReachT.done hu) (fun l hl => by rw [ho.exf] at hl; cases hl)) (fun x ev ⟨a1, a2, a3, a4⟩ => ⟨a1, a2, a3, ?_⟩)
    (fun u hu => ⟨hu.1, hu.2.1.trans hf.symm, fun r h4 h11 _ hK =>
      absurd (Ed25519Routines.mem_hiRegs h4 h11) hK, e.pre.1.1, base, t.mem, hcd, hrd, all2_map fun x hx => ?_⟩)
    fun _ h => h
  · have := win_mono4 (sp := s.regs 13) (by simpa [ctx, h13] using a4)
    rwa [show 4 + q.geo.N = q.s.stack by simp only [geo]; omega] at this
  · obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, -, l, k, hl, hm', hpt, hk⟩ := outOk_parts (ho.outs x0 hx0)
    simp only [hl, Option.map_some, Option.getD_some]
    rw [← tr x0.1 (by omega) (by omega), locOf_addr hH hl, ← hk]
    exact (hu.2.2.2.2.1.1 _ hm').2.base hpt

/-! ## The effect -/

/-- A state whose registers are the public values `p`. -/
def pubSt (s : CalleeS) (p : Nat → Word) : State := ⟨s.reg p, false, false, false, false, fun _ => 0⟩

theorem ini_eq {c : Ctx} {sp : Word} {s : CalleeS} {p : Nat → Word} {k : Kd}
    (h : (k matches .ctx _ | .pw _ | .cw) = false) : Kd.ini c sp k = s.iniOut p k := by
  cases k <;> simp_all [Kd.ini, CalleeS.iniOut]

/-- A byte of a buffer region of the program is a byte of its buffer. -/
theorem ex_rgn (ho : OkF q) (hcb : ∀ x ∈ q.cb, x.2 < 2 ^ 32) {c : Ctx} {r : SR}
    (hok : r.ok q.geo = true) (hx : r.loc.isEx = true) {y : Word} (hy : Has (r.rgns q.geo c) y) :
    ∃ (i : Nat) (x : XInfo) (L : Nat), q.geo.xs[i]? = some x ∧ x.len = .k L ∧ Region (c.ptr i) L y ∧
      r.acc q.geo false = x.r := by
  obtain ⟨l, len⟩ := r
  cases l with
  | fr => simp [Loc.isEx] at hx
  | rg => simp [Loc.isEx] at hx
  | ex i e =>
  cases hi : q.geo.xs[i]? with
  | none => simp [SR.ok, hi] at hok
  | some x =>
  have ⟨L, hL, h32⟩ : ∃ L, x.len = .k L ∧ L < 2 ^ 32 := by
    rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
    · obtain ⟨_, L, -, hL, -, h32, -⟩ := buf_of ho hi; exact ⟨L, hL, h32⟩
    · exact ⟨_, rfl, hcb _ (List.getElem_mem hj)⟩
  cases len with
  | p j => simp [SR.ok, hi, hL] at hok
  | k m =>
  simp only [SR.ok, hi, hL, decide_eq_true_eq] at hok
  obtain ⟨q', hq, hy⟩ := hy
  by_cases hm : m = 0
  · simp [SR.rgns, XLen.v, hm] at hq
  simp only [SR.rgns, XLen.v, hm, ↓reduceIte, List.mem_singleton] at hq; subst hq
  have := sub_off_lt (rgn_region hy (by omega)) (by omega)
  exact ⟨i, x, L, hi, hL, by simp only [Region]; omega, by simp [SR.acc, hi]⟩

/-- **The callee's effect**: at every public value, the trace of the frame around the program
has the effect of the callee, by `prog_good` with the frame's window and the callees' effects. -/
theorem eff {T : A → Word → (Nat → Word) → List Event} (hT : ∀ a base p, (cE a).Eff p base (T a base p))
    {st' : St} (ho : OkP q cE bE st') (hc : q.codeOk cE bE B BS D = true) (base : Word) (p : Nat → Word)
    {tr : List Event} (h : q.tr cE bE T base p tr) : q.s.Eff p base tr := by
  refine CalleeS.eff_of (t := pubSt q.s p) ?_ ho.eff (Nat.le_refl _) fun _ _ => rfl
  refine effT_of_gp fun sp0 n U hroom hn hF hR => GP.is_of ?_ h
  have n0 : 4 * nSaved 0 = 4 := by decide
  have hst := ho.stk; have ht4 := ho.t4
  have hfs : q.geo.fsp (q.ctx base p) = q.s.reg p 13 - BitVec.ofNat 32 (4 + q.top) := by
    simp only [Geo.fsp, ctx, geo]; rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_ofNat]
  have hab : ∀ y, AtOrAboveSp sp0 (q.s.reg p 13) y → AtOrAboveSp sp0 (q.geo.fsp (q.ctx base p)) y :=
    fun y h => by rw [hfs]; exact above_sub h (by omega)
  have hd4 : (sp0 - (q.ctx base p).sp0).toNat = (sp0 - q.s.reg p 13).toNat + 4 := by
    show (sp0 - (q.s.reg p 13 - 4#32)).toNat = _
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_add, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  have fm : Frm (q.ctx base p) q.geo sp0 n
      (fun y => U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) := by
    refine ⟨by simp only [geo]; omega, hn, by simp only [geo]; omega, fun r hok hx y hy hb => ?_⟩
    have hcb := cb_parts hc
    have hN := CodeBytes.lt (B := B)
    obtain ⟨i, x, L, hi, hL, hy', hacc⟩ := ex_rgn ho.toF (fun x hx => by have := (hcb x hx).2.2; omega) hok hx hy
    rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
    rotate_left
    · simp only [XLen.k.injEq] at hL; subst hL
      rw [ctx_code hj] at hy'
      have hy2 : Has [@codeR B BS _ base] y :=
        ⟨_, List.mem_singleton_self _, Rgn.of_region (region_in hy' (hcb _ (List.getElem_mem hj)).2.2 hN)⟩
      exact ⟨hab y (hF y (.inl hy2) hb), fun _ => .inl (hR y (.inl hy2) hb)⟩
    obtain ⟨hlt, L', rfl, hL', -, -, -, -, -, -, -, -, hbuf⟩ := buf_of ho.toF hi
    obtain rfl : L = L' := XLen.k.inj (hL.symm.trans hL')
    rw [ctx_ptr hlt] at hy'
    refine ⟨hab y (hF y (.inr (inR_buf (List.getElem_mem hlt) hbuf hy')) hb), fun ha => .inl (hR y (.inr ?_) hb)⟩
    exact inR_buf (List.mem_filter.2 ⟨List.getElem_mem hlt, by rw [← hacc, ha]⟩) hbuf hy'
  have hH : Holds (q.ctx base p) (q.geo.fsp (q.ctx base p)) q.σ0
      (fun r => if r = 13 then q.geo.fsp (q.ctx base p) else q.s.reg p r) :=
    holds_σ0 ho.toF (fun r h1 _ => by simp [show r ≠ 13 from fun e => absurd (e ▸ h1) (by decide)]) (by simp)
  have hB := prog_good fm (fun a => hT a) (fun y hy hb => ⟨hab y (hF y (.inl hy) hb), .inl (hR y (.inl hy) hb)⟩)
    q.P q.body q.st0 st' (Tr.is []) (SIR sp0 (q.geo.fsp (q.ctx base p)) fun y =>
      (U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
        InR (pubSt q.s p) q.woE y ∧ BelowEntry sp0 n y) [] [] ho.ty rfl ho.eok
      (by simp only [codeOk, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.1.2)
    (fun _ => GP.nil fun q' hq => ⟨hq.sp, fun y hy => hy.elim (hq.sv y) fun ⟨hw, hb⟩ => hq.ex y ?_ hb, hq.ab⟩)
    (fun l hl => by rw [ho.exf] at hl; cases hl)
  · have hk12 := k12 ho.toF
    unfold CalleeP.tr frTr
    by_cases hk : q.k2 = 0
    · rw [ite_eq_left hk]
      refine frameK_gp (mask := 0) (k := q.k1) (U := U)
        (R2 := fun y => (U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
          InR (pubSt q.s p) q.woE y ∧ BelowEntry sp0 n y) (k1_lt (q := q)) (by rw [n0]; omega)
        (by rw [fsp_eq1 ho.toF hk]; exact GP.pre (fun q' hq => ⟨hq.hs, hq.ab, hq.r, fun y ⟨_, hp, _⟩ _ => by simp [st0] at hp⟩) hB)
        (fun y h => .inl (.inr h)) (fun y hy => hy.elim .inl fun h => .inr ⟨hF y (.inr (inR_sub ho.wf h.1)) h.2, .inr h⟩)
        fun y h => .inl (.inl h)
    · rw [ite_eq_right hk]
      refine frameK2_gp (mask := 0) (k1 := q.k1) (k2 := q.k2) (U := U)
        (R2 := fun y => (U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
          InR (pubSt q.s p) q.woE y ∧ BelowEntry sp0 n y) (k1_lt (q := q)) (k2_lt ho.toF) (by rw [n0]; omega)
        (by rw [fsp_eq2 ho.toF]; exact GP.pre (fun q' hq => ⟨hq.hs, hq.ab, hq.r, fun y ⟨_, hp, _⟩ _ => by simp [st0] at hp⟩) hB)
        (fun y h => .inl (.inr h)) (fun y hy => hy.elim .inl fun h => .inr ⟨hF y (.inr (inR_sub ho.wf h.1)) h.2, .inr h⟩)
        fun y h => .inl (.inl h)
  · obtain ⟨a, ha, o, ho', rfl⟩ := hw
    obtain ⟨x, hx, he⟩ := List.mem_filterMap.1 ha
    obtain rfl := outE_eq q.s p he
    obtain ⟨h1, hk, l, k, hl, hm, -, hb⟩ := outOk_parts (ho.outs x hx)
    refine ⟨_, hm, ?_⟩
    rw [← locOf_addr hH hl, ← Kd.ini_base, hb, Kd.ini_base, ini_eq (s := q.s) (p := p) hk]
    simp only [show x.1 ≠ 13 from fun e => absurd (e ▸ h1) (by decide), ↓reduceIte]
    exact region_lt ho'

end run

/-! ## The adapter -/

section ad
variable {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {D : List (Nat × Nat)} {Rs : Rels}

/-- **The callee's call lemma with its effect**, from the decided checks and its callees' adapters. -/
noncomputable def te (ads : ∀ a, AdE Rs (cb := cb) (cE a)) (bds : ∀ b, Bd Rs (bE b)) {st' : St}
    (ho : OkP q cE bE st') (hc : q.codeOk cE bE B BS D = true) :
    (q.R cE bE Rs (fun a => (ads a).ad.sem) (fun b => (bds b).sem)).TE q.s.pub fun base p tr => q.s.Eff p base tr :=
  Routine.te_by (fun base s e => run (fun a => (ads a).ad) bds ho hc base s e)
    (fun b p => by
      have := Prog.tr_uniq (cE := cE) (bE := bE) (G := q.geo) (T := fun a => (ads a).ad.T) (c := q.ctx b p) q.P q.body
        q.st0 (J := []) (Tr.uniq_is []) (fun _ h => absurd h List.not_mem_nil)
      simp only [tr, frTr]; split <;> uniq_tac)
    (fun b p => by
      have := Prog.tr_ex (cE := cE) (bE := bE) (G := q.geo) (T := fun a => (ads a).ad.T) (c := q.ctx b p) q.P q.body
        q.st0 (J := []) (Tr.ex_is []) (fun _ h => absurd h List.not_mem_nil)
      simp only [tr, frTr]; split <;> ex_tac)
    fun b p _ h => eff (fun a => (ads a).ef) ho hc b p h

/-- **A bounded buffer's bound** from the inputs: its register is an input of its refined kind. -/
theorem sc_pre {st' : St} (ho : OkP q cE bE st') {c : Ctx} {sp : Word} {st : State} {vs : List V} {p : Nat × Kd}
    (hi : p ∈ q.sc) (hI : InsRel Rs c sp q.s.io st vs) :
    p.2.Bnd (bytesAt st.mem (st.regs ((q.xr.map (·.1)).getD p.1 0)) 32) := by
  have hk := ho.sc p hi
  unfold scOk at hk
  cases hxi : q.xr[p.1]? with
  | none => simp [hxi] at hk
  | some x =>
    simp only [hxi, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨⟨hrf, -⟩, -⟩, hm⟩ := hk
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hxi
    obtain ⟨v, hv⟩ := (All2.ex hI).1 _ hm
    rw [getD_fst hlt]
    rw [show st.regs q.xr[p.1].1 + BitVec.ofNat 32 0 = st.regs q.xr[p.1].1 from BitVec.add_zero _] at hv
    exact Kd.bnd_of_rel Rs hrf hv

/-- **The callee's adapter**: its routine and call lemma from `te`, with the routine-specific
`post` that relates the program's values to the interface's semantics `sem`. -/
noncomputable def adE (ads : ∀ a, AdE Rs (cb := cb) (cE a)) (bds : ∀ b, Bd Rs (bE b)) {st' : St}
    (ho : OkP q cE bE st') (hc : q.codeOk cE bE B BS D = true) (sem : List V → List V)
    (post : ∀ c sp st m r0 vs, PreV q.s.io c sp st.regs → InsRel Rs c sp q.s.io st vs →
      q.post cE bE Rs (fun a => (ads a).ad.sem) (fun b => (bds b).sem) st m r0 →
      OutsRel Rs c sp q.s.io st m (sem vs)) : AdE Rs (cb := cb) q.s :=
  Ad.ofTSpec _ rfl rfl rfl (q.te ads bds ho hc) (fun _ _ _ h => h) sem (fun _ _ _ _ _ hG _ hI => ⟨⟨hG, fun _ hi => q.sc_pre ho hi hI⟩, trivial⟩) (fun _ => rfl)
    (fun _ => rfl) post

end ad

/-! ## Values up to a relation

`Prog.ev_rel`: two runs of `Prog.ev` with semantics that keep a relation `R` keep it at every
location, when their dispatches decide alike. With values related to powers of an input, a
field-power program's result follows from its exponents, which a closed run evaluates. -/

/-- A list along the passes of a loop with exits: the body's typing `tb`, the body's list `fb`,
the rest's `fk`. -/
def _root_.M0Crypto.Release.Ed25519CallProg.whL {α : Type} (tb : St → Option St) (fb fk : St → List α) :
    Nat → St → List α
  | 0, _ => []
  | n + 1, st => fb st ++ match tb st with
    | some s => match s.ex with
      | none => whL tb fb fk n s
      | some 0 => fk { s with ex := none }
      | some _ => []
    | none => []

/-- The public words the dispatches of a program test. -/
def _root_.M0Crypto.Release.Ed25519CallProg.Prog.selVs {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo) : Prog A Bk → St → List SV
  | .nil, _ => []
  | .op x k, st => match x.ty cE bE G st with
    | some st' => k.selVs cE bE G st'
    | none => []
  | .loop cnt _ b k, st => b.selVs cE bE G (loopSt st cnt) ++ k.selVs cE bE G (loopOut st cnt)
  | .sel w _ p₀ p₁ k, st => match pwAt st.Γ w, p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
    | some v, some s₀, some s₁ =>
      v :: (p₀.selVs cE bE G (selSt st) ++ p₁.selVs cE bE G (selSt st) ++ k.selVs cE bE G (joinSt s₀ s₁))
    | _, _, _ => []
  | .xit g s cc _ _ k, st => match xitSt G st g s cc with
    | some (st2, false) => k.selVs cE bE G st2
    | _ => []
  | .hd b h k, st => b.selVs cE bE G st ++ match b.ty cE bE G st with
    | some s => match s.ex with
      | none => k.selVs cE bE G s
      | some 0 => h.selVs cE bE G { s with ex := none } ++ match h.ty cE bE G { s with ex := none } with
        | some s' => if s'.ex = none then k.selVs cE bE G s' else []
        | none => []
      | some _ => []
    | none => []
  | .wh n b k, st => whL (fun s => b.ty cE bE G s) (fun s => b.selVs cE bE G s) (fun s => k.selVs cE bE G s) n st

/-- The sources a construct's inputs read. -/
def _root_.M0Crypto.Release.Ed25519CallProg.Op.srcs {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)
    (st : St) : Op A Bk → List Src
  | .call a as => match ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | some r => r.srcs
    | none => []
  | .blk b as => match ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
    | some r => r.srcs
    | none => []
  | _ => []

/-- The sources a program's inputs read. -/
def _root_.M0Crypto.Release.Ed25519CallProg.Prog.srcs {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo) : Prog A Bk → St → List Src
  | .nil, _ => []
  | .op x k, st => match x.ty cE bE G st with
    | some st' => x.srcs cE bE G st ++ k.srcs cE bE G st'
    | none => []
  | .loop cnt _ b k, st => b.srcs cE bE G (loopSt st cnt) ++ k.srcs cE bE G (loopOut st cnt)
  | .sel _ _ p₀ p₁ k, st => p₀.srcs cE bE G (selSt st) ++ p₁.srcs cE bE G (selSt st) ++
    match p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
    | some s₀, some s₁ => k.srcs cE bE G (joinSt s₀ s₁)
    | _, _ => []
  | .xit g s cc _ _ k, st => match xitSt G st g s cc with
    | some (st2, false) => k.srcs cE bE G st2
    | _ => []
  | .hd b h k, st => b.srcs cE bE G st ++ match b.ty cE bE G st with
    | some s => match s.ex with
      | none => k.srcs cE bE G s
      | some 0 => h.srcs cE bE G { s with ex := none } ++ match h.ty cE bE G { s with ex := none } with
        | some s' => if s'.ex = none then k.srcs cE bE G s' else []
        | none => []
      | some _ => []
    | none => []
  | .wh n b k, st => whL (fun s => b.ty cE bE G s) (fun s => b.srcs cE bE G s) (fun s => k.srcs cE bE G s) n st

/-- The region of an entry-bytes source. -/
def _root_.M0Crypto.Release.Ed25519CallProg.Src.sr : Src → Option SR
  | .ext r => some r
  | _ => none

theorem _root_.M0Crypto.Release.Ed25519CallProg.Prog.ev_op {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS}
    {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V} {c : Ctx} {m0 : Mem} {x : Op A Bk}
    {k : Prog A Bk} {st st' : St} (h : x.ty cE bE G st = some st') (E : Loc → V) :
    (Prog.op x k).ev cE bE G semA semB c m0 st E = k.ev cE bE G semA semB c m0 st' (x.ev cE bE G semA semB c m0 st E) := by
  simp only [Prog.ev, h]

section rel
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo} {c c' : Ctx} {m0 m0' : Mem}

/-- A relation of values that unknown values, bytes and words on its right satisfy. -/
structure VRel (R : V → V → Prop) : Prop where
  none : ∀ v, R v .none
  b : ∀ v L, R v (.b L)
  w : ∀ v x, R v (.w x)

variable {R : V → V → Prop} (hR : VRel R) {semA semA' : A → List V → List V} {semB semB' : Bk → List V → List V}
  (hA : ∀ a vs vs', All2 R vs vs' → All2 R (semA a vs) (semA' a vs'))
  (hB : ∀ b vs vs', All2 R vs vs' → All2 R (semB b vs) (semB' b vs'))
include hR

theorem src_rel {E E' : Loc → V} (h : ∀ l, R (E l) (E' l)) (s : Src) (hx : s.isXF = false) :
    R (Src.val G c m0 E s) (Src.val G c' m0' E' s) := by
  cases s with
  | extF => simp [Src.isXF] at hx
  | view l => exact h l
  | slice l d n =>
    simp only [Src.val]
    cases E' l with
    | b L => exact hR.b _ _
    | _ => exact hR.none _
  | ext r => exact hR.b _ _
  | pv v => exact hR.w _ _

omit hR in
theorem updOuts_rel {E E' : Loc → V} (h : ∀ l, R (E l) (E' l)) :
    ∀ (outs : List (Loc × Kd)) (vs vs' : List V), All2 R vs vs' → ∀ l, R (updOuts E outs vs l) (updOuts E' outs vs' l)
  | [], _, _, _ => h
  | _ :: _, [], [], _ => h
  | (l0, _) :: outs, v :: vs, v' :: vs', ⟨hv, hvs⟩ => fun l => by
    simp only [updOuts]; split
    · exact hv
    · exact updOuts_rel h outs vs vs' hvs l

omit hR in
theorem all2_take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) (l : List α) (l' : List β), All2 R l l' → All2 R (l.take n) (l'.take n)
  | 0, _, _, _ => by simp [All2]
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: l, _ :: l', ⟨h1, h2⟩ => ⟨h1, all2_take n l l' h2⟩
  | _ + 1, [], _ :: _, h | _ + 1, _ :: _, [], h => by simp [All2] at h

omit hR in
theorem all2_drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) (l : List α) (l' : List β), All2 R l l' → All2 R (l.drop n) (l'.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: l, _ :: l', ⟨_, h2⟩ => all2_drop n l l' h2
  | _ + 1, [], _ :: _, h | _ + 1, _ :: _, [], h => by simp [All2] at h

theorem all2_getD : ∀ (l l' : List V), All2 R l l' → ∀ i : Nat, R (l[i]?.getD .none) (l'[i]?.getD .none)
  | [], [], _, _ => by simpa using hR.none _
  | _ :: _, _ :: _, ⟨h1, _⟩, 0 => by simpa using h1
  | _ :: l, _ :: l', ⟨_, h2⟩, i + 1 => by simpa using all2_getD l l' h2 i
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [All2] at h

theorem byteW_rel (v v' : V) : R v (byteW v') := by
  unfold byteW; split
  · exact hR.w _ _
  · exact hR.none _

theorem setRg_rel {E E' : Loc → V} (h : ∀ l, R (E l) (E' l)) (ro : List Reg) {ws ws' : List V}
    (hw : All2 R ws ws') (l : Loc) : R (setRg E ro ws l) (setRg E' ro ws' l) := by
  cases l
  case rg q =>
    simp only [setRg]; split
    · exact all2_getD hR _ _ hw _
    · exact h _
  all_goals exact h _

theorem srcs_rel {E E' : Loc → V} (h : ∀ l, R (E l) (E' l)) :
    ∀ l : List Src, (∀ s ∈ l, s.isXF = false) → All2 R (l.map (Src.val G c m0 E)) (l.map (Src.val G c' m0' E'))
  | [], _ => trivial
  | s :: l, hx => ⟨src_rel hR h s (hx s (.head _)), srcs_rel h l fun s hs => hx s (.tail _ hs)⟩

include hA hB

theorem op_rel (x : Op A Bk) (st : St) (hx : ∀ s ∈ x.srcs cE bE G st, s.isXF = false) {E E' : Loc → V}
    (h : ∀ l, R (E l) (E' l)) (l : Loc) :
    R (x.ev cE bE G semA semB c m0 st E l) (x.ev cE bE G semA' semB' c' m0' st E' l) := by
  cases x with
  | call a as =>
    simp only [Op.ev]; simp only [Op.srcs] at hx; revert hx
    cases ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | some r => exact fun hx => updOuts_rel h _ _ _ (hA a _ _ (srcs_rel hR h _ hx)) l
    | none => exact fun _ => h l
  | blk b as =>
    simp only [Op.ev]; simp only [Op.srcs] at hx; revert hx
    cases ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
    | some r =>
      intro hx
      have hw := hB b _ _ (srcs_rel (G := G) (c := c) (c' := c') (m0 := m0) (m0' := m0') hR h r.srcs hx)
      exact setRg_rel hR (updOuts_rel h _ _ _ (all2_take _ _ _ hw)) _ (all2_drop _ _ _ hw) l
    | none => exact fun _ => h l
  | spill => exact h l
  | drop => exact h l
  | ld => exact h l
  | pub => exact h l
  | keep => exact h l
  | ldb rd rb ri =>
    simp only [Op.ev]
    cases ldbOff st.σ rb ri with
    | none => exact h l
    | some a =>
      dsimp only
      cases findSlice st.Γ (.fr a) 1 with
      | none => exact h l
      | some s => exact setRg_rel hR h [rd.toReg] (ws := [_]) (ws' := [_]) ⟨byteW_rel hR _ _, trivial⟩ l
  | isl => exact h l

omit hA hB in
theorem loopIt_rel {f f' : (Loc → V) → Loc → V} (hf : ∀ E E', (∀ l, R (E l) (E' l)) → ∀ l, R (f E l) (f' E' l))
    (cnt : Nat) : ∀ n (E E' : Loc → V), (∀ l, R (E l) (E' l)) → ∀ l, R (loopIt f cnt n E l) (loopIt f' cnt n E' l)
  | 0, _, _, h => h
  | n + 1, E, E', h => loopIt_rel hf cnt n _ _ (hf _ _ fun l => by
      simp only [setCnt]; split
      · exact hR.w _ _
      · exact h l)

omit hR hA hB in
theorem whEv_rel {tb : St → Option St} {eb eb' ek ek' : St → (Loc → V) → Loc → V} {fb fk : St → List SV}
    {gb gk : St → List Src}
    (hb : ∀ s, (∀ v ∈ fb s, ∀ i, (v.val c (G.fsp c) == BitVec.ofNat 32 i) = (v.val c' (G.fsp c') == BitVec.ofNat 32 i)) →
      (∀ x ∈ gb s, x.isXF = false) → ∀ (E E' : Loc → V), (∀ l, R (E l) (E' l)) → ∀ l, R (eb s E l) (eb' s E' l))
    (hk : ∀ s, (∀ v ∈ fk s, ∀ i, (v.val c (G.fsp c) == BitVec.ofNat 32 i) = (v.val c' (G.fsp c') == BitVec.ofNat 32 i)) →
      (∀ x ∈ gk s, x.isXF = false) → ∀ (E E' : Loc → V), (∀ l, R (E l) (E' l)) → ∀ l, R (ek s E l) (ek' s E' l)) :
    ∀ n st, (∀ v ∈ whL tb fb fk n st, ∀ i,
      (v.val c (G.fsp c) == BitVec.ofNat 32 i) = (v.val c' (G.fsp c') == BitVec.ofNat 32 i)) →
    (∀ x ∈ whL tb gb gk n st, x.isXF = false) → ∀ (E E' : Loc → V), (∀ l, R (E l) (E' l)) →
    ∀ l, R (whEv tb eb ek n st E l) (whEv tb eb' ek' n st E' l)
  | 0, _, _, _, _, _, h => h
  | n + 1, st, hS, hX, E, E', h => by
    simp only [whEv, whL, List.mem_append] at hS hX ⊢
    have e1 := hb st (fun v hv => hS v (.inl hv)) (fun x hx => hX x (.inl hx)) E E' h
    cases h1 : tb st with
    | none => simp only [h1]; exact h
    | some s =>
    simp only [h1] at hS hX ⊢
    cases h2 : s.ex with
    | none =>
      simp only [h2] at hS hX ⊢
      exact whEv_rel hb hk n s (fun v hv => hS v (.inr hv)) (fun x hx => hX x (.inr hx)) _ _ e1
    | some j =>
    cases j with
    | zero =>
      simp only [h2] at hS hX ⊢
      exact hk _ (fun v hv => hS v (.inr hv)) (fun x hx => hX x (.inr hx)) _ _ e1
    | succ j => simp only [h2]; exact e1

/-- **Values related at the start stay related** after a program, run with semantics that keep
the relation and in contexts where its dispatches decide alike. -/
theorem Prog.ev_rel : ∀ (P : Prog A Bk) (st : St),
    (∀ v ∈ P.selVs cE bE G st, ∀ i, (v.val c (G.fsp c) == BitVec.ofNat 32 i) = (v.val c' (G.fsp c') == BitVec.ofNat 32 i)) →
    (∀ s ∈ P.srcs cE bE G st, s.isXF = false) →
    ∀ (E E' : Loc → V), (∀ l, R (E l) (E' l)) →
    ∀ l, R (P.ev cE bE G semA semB c m0 st E l) (P.ev cE bE G semA' semB' c' m0' st E' l)
  | .nil, _, _, _, _, _, h => h
  | .op x k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs] at hS hX ⊢
    revert hS hX
    cases x.ty cE bE G st with
    | some st' =>
      intro hS hX
      simp only [List.mem_append] at hX
      exact Prog.ev_rel k _ hS (fun s hs => hX s (.inr hs)) _ _ (op_rel hR hA hB x st (fun s hs => hX s (.inl hs)) h)
    | none => exact fun _ _ => h
  | .loop cnt n b k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs, List.mem_append] at hS hX ⊢
    exact Prog.ev_rel k _ (fun v hv => hS v (.inr hv)) (fun s hs => hX s (.inr hs)) _ _
      (loopIt_rel hR (fun _ _ h' => Prog.ev_rel b _ (fun v hv => hS v (.inl hv)) (fun s hs => hX s (.inl hs)) _ _ h')
        cnt n E E' h)
  | .sel w i p₀ p₁ k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs] at hS hX ⊢
    revert hS hX
    cases pwAt st.Γ w with
    | none => exact fun _ _ => h
    | some v =>
    cases p₀.ty cE bE G (selSt st) with
    | none => exact fun _ _ => h
    | some s₀ =>
    cases p₁.ty cE bE G (selSt st) with
    | none => exact fun _ _ => h
    | some s₁ =>
    intro hS hX; dsimp only
    simp only [List.mem_cons, List.mem_append] at hS hX
    have h0 := fun v hv => hS v (.inr (.inl (.inl hv)))
    have h1 := fun v hv => hS v (.inr (.inl (.inr hv)))
    have hk := fun v hv => hS v (.inr (.inr hv))
    have x0 := fun s hs => hX s (.inl (.inl hs))
    have x1 := fun s hs => hX s (.inl (.inr hs))
    have xk := fun s hs => hX s (.inr hs)
    rw [hS v (.inl rfl) i]
    by_cases hc : (v.val c' (G.fsp c') == BitVec.ofNat 32 i) = true
    · simp only [hc, ↓reduceIte]; exact Prog.ev_rel k _ hk xk _ _ (Prog.ev_rel p₁ _ h1 x1 _ _ h)
    · simp only [hc]; exact Prog.ev_rel k _ hk xk _ _ (Prog.ev_rel p₀ _ h0 x0 _ _ h)
  | .xit g s cc sh l k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs] at hS hX ⊢
    revert hS hX
    cases xitSt G st g s cc with
    | none => exact fun _ _ => h
    | some p =>
    obtain ⟨st2, b⟩ := p
    cases b with
    | false => exact fun hS hX => Prog.ev_rel k st2 hS hX _ _ h
    | true => exact fun _ _ => h
  | .hd b g k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs, List.mem_append] at hS hX ⊢
    have eb := Prog.ev_rel b st (fun v hv => hS v (.inl hv)) (fun x hx => hX x (.inl hx)) E E' h
    cases h1 : b.ty cE bE G st with
    | none => simp only [h1]; exact h
    | some s =>
    simp only [h1] at hS hX ⊢
    cases h2 : s.ex with
    | none =>
      simp only [h2] at hS hX ⊢
      exact Prog.ev_rel k s (fun v hv => hS v (.inr hv)) (fun x hx => hX x (.inr hx)) _ _ eb
    | some j =>
    cases j with
    | succ j => simp only [h2]; exact eb
    | zero =>
    simp only [h2, List.mem_append] at hS hX ⊢
    have eh := Prog.ev_rel g { s with ex := none } (fun v hv => hS v (.inr (.inl hv)))
      (fun x hx => hX x (.inr (.inl hx))) _ _ eb
    cases h3 : g.ty cE bE G { s with ex := none } with
    | none => simp only [h3]; exact eb
    | some s' =>
    simp only [h3] at hS hX ⊢
    by_cases hn : s'.ex = none
    · simp only [hn, ↓reduceIte] at hS hX ⊢
      exact Prog.ev_rel k s' (fun v hv => hS v (.inr (.inr hv))) (fun x hx => hX x (.inr (.inr hx))) _ _ eh
    · simp only [hn, ↓reduceIte]; exact eh
  | .wh n b k, st, hS, hX, E, E', h => by
    simp only [Prog.ev, Prog.selVs, Prog.srcs] at hS hX ⊢
    exact whEv_rel (fun s h1 h2 E E' h' => Prog.ev_rel b s h1 h2 E E' h')
      (fun s h1 h2 E E' h' => Prog.ev_rel k s h1 h2 E E' h') n st hS hX E E' h

end rel

end CalleeP

end M0Crypto.Release.Ed25519CallProg
