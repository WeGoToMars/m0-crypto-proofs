import M0Crypto.Release.Ed25519CallProgEntryRun
import M0Crypto.Release.Ed25519CallProgGood
import M0Crypto.Release.Ed25519CallProgUnit

/-!
# Call programs: first-failure reporters

`Prog.tyErr` and `Prog.bokErr` give the code offset of the first construct that fails the static
check `Prog.ty` or the code checks `Prog.bok`, or `none` when the check passes
(`Prog.tyErr_eq_none`, `Prog.bokErr_eq_none`). A failing body is reported inside the loop or arm
that holds it; a construct's own condition is reported at its offset. `entryErr` reports an
entry's first failure: an instruction the bytes do not hold, a `unitFns` row, the static check,
the frame's shape, or a code check. `Prog.eokErr` names the first construct and condition that
fails `Prog.eok` (`Prog.eokErr_eq_none`), from the named conditions of `callOk`, `blkOk` and
`Op.eok` (`callOk_eq`, `blkOk_eq`, `Op.eok_eq`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Thumb
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Armv6M (Reg)
open M0Crypto.Release.StackEffect (blkChk)

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- **The first construct that fails `Prog.ty`**, by code offset from `o`. -/
def Prog.tyErr : Prog A Bk → St → Nat → Option Nat
  | .nil, _, _ => none
  | .op x k, st, o =>
    match x.ty cE bE G st with
    | some st' => k.tyErr st' (o + x.size cE bE)
    | none => some o
  | .loop cnt n b k, st, o =>
    let ob := o + seqSize (loopHead cnt n)
    match b.ty cE bE G (loopSt st cnt) with
    | some sB =>
      if slotOk G cnt && decide (0 < n) && decide (n < 256) && (Loc.fr cnt, Kd.cw) ∈ sB.Γ &&
          subL (loopSt st cnt).Γ ((.fr cnt, .cw) :: cntViews sB.Γ cnt) && sB.X == st.X && sB.ex == none then
        k.tyErr (loopOut st cnt) (ob + b.size cE bE + seqSize (loopDec cnt) + 4)
      else some o
    | none => b.tyErr (loopSt st cnt) ob
  | .sel w i p₀ p₁ k, st, o =>
    let o₀ := o + seqSize (selHead w i) + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    match p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
    | none, _ => p₀.tyErr (selSt st) o₀
    | some _, none => p₁.tyErr (selSt st) o₁
    | some s₀, some s₁ =>
      if (pwAt st.Γ w).isSome && slotOk G w && decide (i < 256) && s₀.ex == none && s₁.ex == none then
        k.tyErr (joinSt s₀ s₁) (o₁ + p₁.size cE bE + 2)
      else some o
  | .xit g s cc sh l k, st, o => if (Prog.ty cE bE G (.xit g s cc sh l k) st).isSome then none else some o
  | .hd b h k, st, o => if (Prog.ty cE bE G (.hd b h k) st).isSome then none else some o
  | .wh n b k, st, o => if (Prog.ty cE bE G (.wh n b k) st).isSome then none else some o

theorem ite_none_iff {α : Type} (b : Bool) (a : α) : ((if b = true then none else some a) = none) ↔ b = true := by
  cases b <;> simp

theorem Prog.tyErr_eq_none : ∀ (P : Prog A Bk) (st : St) (o : Nat),
    P.tyErr cE bE G st o = none ↔ (P.ty cE bE G st).isSome = true
  | .nil, _, _ => by simp [Prog.tyErr, Prog.ty]
  | .op x k, st, o => by
    simp only [Prog.tyErr, Prog.ty]
    split <;> rename_i h <;> simp only [h, Option.bind_some, Option.bind_none, reduceCtorEq,
      Option.isSome_none, Bool.false_eq_true]
    exact Prog.tyErr_eq_none k _ _
  | .loop cnt n b k, st, o => by
    have ib := Prog.tyErr_eq_none b (loopSt st cnt) (o + seqSize (loopHead cnt n))
    simp only [Prog.tyErr, Prog.ty]
    split <;> rename_i h <;> simp only [h] at ib ⊢
    · split
      · exact Prog.tyErr_eq_none k _ _
      · simp
    · simpa using ib
  | .sel w i p₀ p₁ k, st, o => by
    have i₀ := Prog.tyErr_eq_none p₀ (selSt st) (o + seqSize (selHead w i) + 4)
    have i₁ := Prog.tyErr_eq_none p₁ (selSt st) (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2)
    simp only [Prog.tyErr, Prog.ty]
    cases h₀ : p₀.ty cE bE G (selSt st) <;> cases h₁ : p₁.ty cE bE G (selSt st) <;>
      cases hw : pwAt st.Γ w <;> simp only [h₀, h₁] at i₀ i₁ <;> simp_all
    split
    · exact Prog.tyErr_eq_none k _ _
    · simp
  | .xit .., _, _ | .hd .., _, _ | .wh .., _, _ => by simp only [Prog.tyErr]; exact ite_none_iff _ _

/-! ## Code checks -/

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **The first construct that fails `Prog.bok`**, by code offset. -/
def Prog.bokErr : List Nat → Prog A Bk → Nat → Option Nat
  | _, .nil, _ => none
  | J, .op x k, o => if x.bok cE bE G o then k.bokErr J (o + x.size cE bE) else some o
  | J, .loop cnt n b k, o =>
    let ob := o + seqSize (loopHead cnt n)
    let od := ob + b.size cE bE
    let oe := od + seqSize (loopDec cnt)
    if glueOk G.cs (loopHead cnt n) o G.top G.N [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)] [] &&
        traceOk (loopHead cnt n) [13] &&
        glueOk G.cs (loopDec cnt) od G.top G.N [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)]
          [(13, BitVec.ofNat 32 cnt, 4)] && traceOk (loopDec cnt) [13] &&
        bcOk G.cs oe (oe + 4) && bOk G.cs (oe + 2) ob then
      (b.bokErr [] ob).or (k.bokErr J (oe + 4))
    else some o
  | J, .sel w i p₀ p₁ k, o =>
    let oh := o + seqSize (selHead w i)
    let o₀ := oh + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    let oo := o₁ + p₁.size cE bE + 2
    if glueOk G.cs (selHead w i) o G.top G.N [(13, 4)] [] [(13, BitVec.ofNat 32 w, 4)] &&
        traceOk (selHead w i) [13] && bcOk G.cs oh o₀ && bOk G.cs (oh + 2) o₁ &&
        bOk G.cs (o₁ - 2) oo && bOk G.cs (oo - 2) oo then
      (p₀.bokErr [] o₀).or ((p₁.bokErr [] o₁).or (k.bokErr J oo))
    else some o
  | J, .xit g s cc sh l k, o => if Prog.bok cE bE G J (.xit g s cc sh l k) o then none else some o
  | J, .hd b h k, o => if Prog.bok cE bE G J (.hd b h k) o then none else some o
  | J, .wh n b k, o => if Prog.bok cE bE G J (.wh n b k) o then none else some o

theorem Prog.bokErr_eq_none : ∀ (P : Prog A Bk) (J : List Nat) (o : Nat),
    P.bokErr cE bE G J o = none ↔ P.bok cE bE G J o = true
  | .nil, _, _ => by simp [Prog.bokErr, Prog.bok]
  | .op x k, J, o => by
    have := Prog.bokErr_eq_none k J (o + x.size cE bE)
    simp only [Prog.bokErr, Prog.bok]
    split <;> simp_all
  | .loop cnt n b k, J, o => by
    have ib := Prog.bokErr_eq_none b [] (o + seqSize (loopHead cnt n))
    have ik := Prog.bokErr_eq_none k J (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 4)
    simp only [Prog.bokErr, Prog.bok]
    split <;> simp_all [Option.or_eq_none_iff]
  | .sel w i p₀ p₁ k, J, o => by
    have i₀ := Prog.bokErr_eq_none p₀ [] (o + seqSize (selHead w i) + 4)
    have i₁ := Prog.bokErr_eq_none p₁ [] (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2)
    have ik := Prog.bokErr_eq_none k J
      (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2)
    simp only [Prog.bokErr, Prog.bok]
    split <;> simp_all [Option.or_eq_none_iff, and_assoc]
  | .xit .., _, _ | .hd .., _, _ | .wh .., _, _ => by simp only [Prog.bokErr]; exact ite_none_iff _ _

end

/-! ## Named conditions

A decided check as a list of named conditions: `firstFail` names the first that fails, and
`each` names the conditions of every element of a list by the element. -/

/-- The name of the first condition of `cs` that fails. -/
def firstFail (cs : List (String × Bool)) : Option String := (cs.find? fun c => !c.2).map (·.1)

theorem firstFail_eq_none (cs : List (String × Bool)) : firstFail cs = none ↔ cs.all (·.2) = true := by
  simp [firstFail, List.find?_eq_none, List.all_eq_true]

/-- The conditions `f a` of each `a` of `l`, under `a`'s name. -/
def each {α : Type} (nm : α → String) (l : List α) (f : α → List (String × Bool)) : List (String × Bool) :=
  l.flatMap fun a => (f a).map fun c => (nm a ++ ": " ++ c.1, c.2)

theorem all_each {α : Type} (nm : α → String) (l : List α) (f : α → List (String × Bool)) :
    (each nm l f).all (·.2) = l.all fun a => (f a).all (·.2) := by
  simp [each, List.all_flatMap, List.all_map, Function.comp_def]

def regN (r : Reg) : String := s!"r{r.val}"

/-! ## The decided effects -/

/-- `callOk`'s conditions. -/
def callC (s : CalleeS) (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) : List (String × Bool) :=
  [("registers known once", σOk σ), ("sp is the frame's", σ.lookup 13 == some (.sp 0)),
   ("sp public", PubW.r 13 ∈ s.pubs)] ++
  each (fun r => "region " ++ regN r.r) (s.io.rd ++ s.io.wr)
    (fun r => [("public", PubW.r r.r ∈ s.pubs && lenPub s.pubs r.len)]) ++
  each (fun x => "input " ++ regN x.1) s.io.ins (fun x => [("public", x.2.2 == .view .rw || PubW.r x.1 ∈ s.pubs &&
    match x.2.2 with
    | .raw l => lenPub s.pubs l
    | .view (.ctx n) => x.1 == 0 && x.2.1 == 0 && PubW.n 0 ∈ s.pubs && ctxAt Γ σ 0 == some n
    | .view _ => true)]) ++
  each (fun x => "output " ++ regN x.1) s.io.outs (fun x => [("public", PubW.r x.1 ∈ s.pubs && match x.2.2 with
    | .ctx n => (rawSVs σ s.io.ins).any fun l => n == ctxIn s Γ σ ++ l
    | _ => true)])

theorem callOk_eq (s : CalleeS) (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) :
    callOk s Γ σ = (callC s Γ σ).all (·.2) := by
  simp only [callOk, callC, List.all_append, all_each, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]
  rfl

/-- `blkOk`'s conditions. -/
def blkC (b : BlockS) (σ : List (Reg × SV)) : List (String × Bool) :=
  [("registers known once", σOk σ)] ++
  each (fun r => "region " ++ regN r.r) (b.io.rd ++ b.io.wr) (fun r => [("a block register", regIn b.L r.r)]) ++
  each (fun x => "input " ++ regN x.1) b.io.ins (fun x => [("a block register (unless a register word) and kind",
    match x.2.2 with
    | .view (.ctx _) => false
    | .view .rw => true
    | .view _ => regIn b.L x.1
    | .raw l => regIn b.L x.1 && l matches .k _)]) ++
  each (fun x => "output " ++ regN x.1) b.io.outs (fun x => [("a block register, no context",
    regIn b.L x.1 && !(x.2.2 matches .ctx _))]) ++
  [("accesses in footprints", blkChk (b.io.ins.map fun x => rgnE x.1 x.2.1 (x.2.2.kd fun _ => 0).sz)
    (b.io.outs.filterMap fun x => if inPlace b.io.ins x then none else
      some (rgnE x.1 x.2.1 x.2.2.sz))
    ((b.io.rd ++ b.io.wr).map fun r => rgnE r.r r.off r.len.kv) b.g)]

theorem blkOk_eq (b : BlockS) (σ : List (Reg × SV)) : blkOk b σ = (blkC b σ).all (·.2) := by
  simp only [blkOk, blkC, List.all_append, all_each, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]
  rfl

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- `Op.eok`'s conditions. -/
def Op.eokC (st : St) : Op A Bk → List (String × Bool)
  | .call a as => ("loads", blkChk (ldsIni as) [] [frR G] (ldsEmit as)) :: callC (cE a) st.Γ (regsOf st.Γ st.σ as)
  | .blk b as => ("loads", blkChk (ldsIni as) [] [frR G] (ldsEmit as)) :: blkC (bE b) (regsOf st.Γ st.σ as)
  | .spill r o => [("spill", blkChk [] [slotR o] [slotR o] [.strSp r (BitVec.ofNat 8 (o / 4))])]
  | .drop _ _ => []
  | .ld r (.C ..) => [("adr", blkChk [] [] [frR G] [.addPc r])]
  | .ld r l => [("load", blkChk (ldsIni [(r, l)]) [] [frR G] (l.emit r))]
  | .pub g => [("public block", blkChk (pwIni st.Γ) [] [frR G] g)]
  | .keep _ => []
  | .ldb rd rb ri => [("byte load", blkChk [ldbR rb ri] [] [ldbR rb ri] [ldbI rd rb ri])]
  | .isl _ _ => []

theorem Op.eok_eq (st : St) (x : Op A Bk) : x.eok cE bE G st = (x.eokC cE bE G st).all (·.2) := by
  cases x with
  | call => simp [Op.eok, Op.eokC, callOk_eq]
  | blk => simp [Op.eok, Op.eokC, blkOk_eq]
  | ld r l => cases l <;> simp [Op.eok, Op.eokC]
  | _ => simp [Op.eok, Op.eokC]

/-- **The first construct that fails `Prog.eok`**: its code offset from `o` and the condition. -/
def Prog.eokErr : Prog A Bk → St → Nat → Option (Nat × String)
  | .nil, _, _ => none
  | .op x k, st, o =>
    match firstFail (x.eokC cE bE G st), x.ty cE bE G st with
    | some c, _ => some (o, c)
    | none, some st' => k.eokErr st' (o + x.size cE bE)
    | none, none => some (o, "typing")
  | .loop cnt n b k, st, o =>
    let ob := o + seqSize (loopHead cnt n)
    if blkChk [] [slotR cnt] [slotR cnt] (loopHead cnt n) &&
        blkChk [slotR cnt] [slotR cnt] [slotR cnt] (loopDec cnt) then
      (b.eokErr (loopSt st cnt) ob).or (k.eokErr (loopOut st cnt) (ob + b.size cE bE + seqSize (loopDec cnt) + 4))
    else some (o, "loop counter")
  | .sel w i p₀ p₁ k, st, o =>
    let o₀ := o + seqSize (selHead w i) + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    if blkChk [slotR w] [] [slotR w] (selHead w i) then
      (p₀.eokErr (selSt st) o₀).or ((p₁.eokErr (selSt st) o₁).or
        (match p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
        | some s₀, some s₁ => k.eokErr (joinSt s₀ s₁) (o₁ + p₁.size cE bE + 2)
        | _, _ => some (o, "arm typing")))
    else some (o, "select word")
  | .xit g s cc sh l k, st, o => if Prog.eok cE bE G (.xit g s cc sh l k) st then none else some (o, "test")
  | .hd b h k, st, o => if Prog.eok cE bE G (.hd b h k) st then none else some (o, "branch")
  | .wh n b k, st, o => if Prog.eok cE bE G (.wh n b k) st then none else some (o, "loop")

theorem Prog.eokErr_eq_none : ∀ (P : Prog A Bk) (st : St) (o : Nat),
    P.eokErr cE bE G st o = none ↔ P.eok cE bE G st = true
  | .nil, _, _ => by simp [Prog.eokErr, Prog.eok]
  | .op x k, st, o => by
    have ih := fun st' => Prog.eokErr_eq_none k st' (o + x.size cE bE)
    simp only [Prog.eokErr, Prog.eok, Op.eok_eq]
    cases h1 : firstFail (x.eokC cE bE G st) with
    | some c =>
      have : (x.eokC cE bE G st).all (·.2) = false := by
        cases h : (x.eokC cE bE G st).all (·.2)
        · rfl
        · rw [← firstFail_eq_none, h1] at h; cases h
      simp [this]
    | none =>
      rw [(firstFail_eq_none _).1 h1]
      cases x.ty cE bE G st <;> simp [ih]
  | .loop cnt n b k, st, o => by
    have ib := Prog.eokErr_eq_none b (loopSt st cnt) (o + seqSize (loopHead cnt n))
    have ik := Prog.eokErr_eq_none k (loopOut st cnt)
      (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 4)
    simp only [Prog.eokErr, Prog.eok]
    split <;> simp_all [Option.or_eq_none_iff, Bool.and_assoc]
  | .sel w i p₀ p₁ k, st, o => by
    have i₀ := Prog.eokErr_eq_none p₀ (selSt st) (o + seqSize (selHead w i) + 4)
    have i₁ := Prog.eokErr_eq_none p₁ (selSt st) (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2)
    have ik := fun s => Prog.eokErr_eq_none k s
      (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2)
    simp only [Prog.eokErr, Prog.eok]
    cases h₀ : p₀.ty cE bE G (selSt st) <;> cases h₁ : p₁.ty cE bE G (selSt st) <;>
      split <;> simp_all [Option.or_eq_none_iff, Bool.and_assoc]
  | .xit .., _, _ | .hd .., _, _ | .wh .., _, _ => by simp only [Prog.eokErr]; cases Prog.eok .. <;> simp

end

/-- The first instruction of `is` that the bytes `bs` at `o` do not hold: its offset, the
decoded instruction and the expected one. -/
def seqErr : List (BitVec 8) → Nat → List Instr → Option (Nat × Option Instr × Instr)
  | _, _, [] => none
  | bs, o, i :: is =>
    if instrAt bs 0 == some i && decide (i.size ≤ bs.length) then seqErr (bs.drop i.size) (o + i.size) is
    else some (o, instrAt bs 0, i)

def piecesErr : List (BitVec 8) → Nat → List Piece → Option (Nat × Option Instr × Instr)
  | _, _, [] => none
  | bs, o, p :: ps => (seqErr bs o (p.instrs o)).or (piecesErr (bs.drop p.size) (o + p.size) ps)

/-- An entry's first failure. -/
inductive EntryErr where
  | instr (o : Nat) (found : Option Instr) (want : Instr)
  | unit (o : Nat) (r : UnitErr)
  | ty (o : Nat)
  | eok (o : Nat) (c : String)
  | shape
  | code (o : Nat)
  deriving Repr

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS)

/-- **The entry diagnostic** of the body `P` from `st0` at `oE` in build `b`: the first
instruction the bytes do not hold (with its offset, the decoded and the expected instruction),
then the unit table, `Prog.ty`, `Prog.eok`, `entryOk` and `Prog.bok`. -/
def entryErr (b : Build) (G : Geo) (P : Prog A Bk) (st0 : St) (oE : Nat) : Option EntryErr :=
  ((piecesErr (b.bytes.drop oE) oE (.seq (abiEnter G.top) :: P.emit cE bE [] (bodyAt G oE) ++
      leaveOf cE bE G P oE)).map fun (o, f, w) => .instr o f w) <|>
    ((unitErr b).map fun (o, r) => .unit o r) <|> ((P.tyErr cE bE G st0 (bodyAt G oE)).map .ty) <|>
    ((P.eokErr cE bE G st0 (bodyAt G oE)).map fun (o, c) => .eok o c) <|>
    (if entryOk cE bE G P oE then none else some .shape) <|>
    ((@Prog.bokErr A Bk cE bE G b.bytes b.size b.codeBytes [] P (bodyAt G oE)).map .code)

end

end M0Crypto.Release.Ed25519CallProg
