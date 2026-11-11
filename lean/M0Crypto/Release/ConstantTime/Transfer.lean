import M0Crypto.Release.ConstantTime.Domain
import M0Crypto.Armv6M.Step

/-!
# Constant-time transfer function and obligations

`xfer env off ctx i st` is the abstract effect of the instruction `i` at artifact offset
`off` in call context `ctx`. The result is either the first violated obligation, or:

* the successors, each a program point `(off', ctx')` or `exit` (the top-level return),
  paired with its abstract state;
* the site kinds at this instruction: accesses through a public non-stack pointer
  (`load` and `store`), and the declassified verdict branch (`declass`). Accesses at
  sites are not bounded by the analysis; the single-run site facts bound them.

Obligations: SP stays in the window; every memory address is public, and stack-relative
accesses lie in the window; literal loads lie in the artifact; conditional branches test
only public flags (except at the declassified branch); calls are at most one level deep;
a return goes to the address the call left, or at top level to the entry LR.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Thumb
open M0Crypto.Armv6M (Word addWithCarry)

/-- Fixed parameters of one entry's analysis. -/
structure Env where
  win : StackWindow
  /-- Artifact size: literal loads must lie below it. -/
  size : Nat
  /-- Offset of the declassified conditional branch, if any. -/
  declass : Option Nat
  deriving DecidableEq, Repr

inductive Tgt where
  | pt (off : Nat) (ctx : Option Nat)
  | exit
  deriving DecidableEq, Repr, Inhabited

inductive SiteK where
  | load
  | store
  | declass
  deriving DecidableEq, Repr, Inhabited

structure Out where
  succs : List (Tgt × AbsState)
  sites : List SiteK
  deriving Repr, Inhabited

/-! ## Helpers -/

/-- NZCV from `AddWithCarry(a, b, cin)` when all inputs are exact, else by label. -/
def addRes (va vb : AbsVal) (cin : AbsFlags) (exactV : AbsVal) : AbsVal × AFl :=
  match va.exact?, vb.exact?, cin with
  | some a, some b, .known c =>
    let (r, co, ov) := addWithCarry (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) c
    if a < AbsVal.word ∧ b < AbsVal.word then
      (.cst r.toNat, ⟨.known r.msb, .known (r == 0#32), .known co, .known ov, none⟩)
    else (exactV, AFl.all (AbsFlags.ofPub (va.pub && vb.pub)))
  | _, _, _ =>
    let p := va.pub && vb.pub && cin.pub
    (exactV, AFl.all (AbsFlags.ofPub p))

/-- Set N and Z by label, keep C and V. -/
def setNZ (f : AFl) (p : Bool) : AFl :=
  { f with n := AbsFlags.ofPub p, z := AbsFlags.ofPub p, cmp := none }

/-- Set N, Z and C by label, keep V. -/
def setNZC (f : AFl) (p pc : Bool) : AFl :=
  { f with n := AbsFlags.ofPub p, z := AbsFlags.ofPub p, c := AbsFlags.ofPub pc, cmp := none }

def notWord (v : AbsVal) : AbsVal :=
  match v.exact? with
  | some a => if a < AbsVal.word then .cst (AbsVal.word - 1 - a) else .lo
  | none => AbsVal.ofPub v.pub

def condFlagsPub (cond : Nat) (f : AFl) : Bool :=
  match cond with
  | 0 | 1 => f.z.pub
  | 2 | 3 => f.c.pub
  | 4 | 5 => f.n.pub
  | 6 | 7 => f.v.pub
  | 8 | 9 => f.c.pub && f.z.pub
  | 10 | 11 => f.n.pub && f.v.pub
  | 12 | 13 => f.z.pub && f.n.pub && f.v.pub
  | _ => false

def knownB : AbsFlags → Option Bool
  | .known b => some b
  | _ => none

/-- `ConditionPassed` on known flags. -/
def evalCond (cond : Nat) (f : AFl) : Option Bool :=
  match cond with
  | 0 => knownB f.z
  | 1 => (knownB f.z).map (!·)
  | 2 => knownB f.c
  | 3 => (knownB f.c).map (!·)
  | 4 => knownB f.n
  | 5 => (knownB f.n).map (!·)
  | 6 => knownB f.v
  | 7 => (knownB f.v).map (!·)
  | 8 => do let c ← knownB f.c; let z ← knownB f.z; pure (c && !z)
  | 9 => do let c ← knownB f.c; let z ← knownB f.z; pure (!c || z)
  | 10 => do let n ← knownB f.n; let v ← knownB f.v; pure (n == v)
  | 11 => do let n ← knownB f.n; let v ← knownB f.v; pure (n != v)
  | 12 => do let z ← knownB f.z; let n ← knownB f.n; let v ← knownB f.v; pure (!z && n == v)
  | 13 => do let z ← knownB f.z; let n ← knownB f.n; let v ← knownB f.v; pure (z || n != v)
  | _ => none

/-! ## Interval refinement after `CMP a, b` -/

def opndIval (st : AbsState) : Opnd → Option (Nat × Nat)
  | .reg r => ival (st.get r)
  | .imm w => if w < AbsVal.word then some (w, w) else none

/-- Relation between `a` and `b` that a taken (`true`) or untaken branch implies. -/
inductive Rel where
  | lt | le | gt | ge | eq | ne

def condRel (cond : Nat) (taken : Bool) : Option Rel :=
  match cond, taken with
  | 0, true | 1, false => some .eq
  | 0, false | 1, true => some .ne
  | 2, true | 3, false => some .ge
  | 2, false | 3, true => some .lt
  | 8, true | 9, false => some .gt
  | 8, false | 9, true => some .le
  | _, _ => none

/-- Refine `x ∈ [a1, a2]` against `y ∈ [b1, b2]` under `x rel y`; `none` if infeasible. -/
def refineI (rel : Rel) (a1 a2 b1 b2 : Nat) : Option ((Nat × Nat) × (Nat × Nat)) :=
  let r := match rel with
    | .lt => if b2 = 0 then none else some ((a1, min a2 (b2 - 1)), (max b1 (a1 + 1), b2))
    | .le => some ((a1, min a2 b2), (max b1 a1, b2))
    | .gt => if a2 = 0 then none else some ((max a1 (b1 + 1), a2), (b1, min b2 (a2 - 1)))
    | .ge => some ((max a1 b1, a2), (b1, min b2 a2))
    | .eq => some ((max a1 b1, min a2 b2), (max a1 b1, min a2 b2))
    | .ne =>
      if b1 = b2 then
        let a1' := if a1 = b1 then a1 + 1 else a1
        let a2' := if a2 = b1 ∧ 0 < a2 then a2 - 1 else a2
        some ((a1', a2'), (b1, b2))
      else some ((a1, a2), (b1, b2))
  match r with
  | some ((x1, x2), (y1, y2)) => if x1 ≤ x2 ∧ y1 ≤ y2 then r else none
  | none => none

/-- Apply the refinement of the recorded comparison to the state; `none` if the edge is
infeasible. Registers without an interval are left unchanged. -/
def refine (w : StackWindow) (st : AbsState) (cond : Nat) (taken : Bool) : Option AbsState :=
  match st.fl.cmp, condRel cond taken with
  | some c, some rel =>
    if c.zOnly && !(rel matches .eq | .ne) then some st else
    match ival (st.get c.a), opndIval st c.b with
    | some (a1, a2), some (b1, b2) =>
      match refineI rel a1 a2 b1 b2 with
      | none => none
      | some ((x1, x2), (y1, y2)) =>
        let regs := regSet st.regs c.a (.num x1 x2)
        let regs := match c.b with
          | .reg r => if r == c.a then regs else regSet regs r (.num y1 y2)
          | .imm _ => regs
        let st' := { st with regs := regs }
        let facts : List Fact := match c.b with
          | .reg r =>
            if r == c.a then [] else match rel with
            | .lt => [(c.a, r, true)]
            | .le => [(c.a, r, false)]
            | .gt => [(r, c.a, true)]
            | .ge => [(r, c.a, false)]
            | .ne => (if st.entails (c.a, r, false) then [(c.a, r, true)] else []) ++
                     (if st.entails (r, c.a, false) then [(r, c.a, true)] else [])
            | .eq => []
          | .imm _ => []
        some (AbsState.tighten w { st' with rel := (st'.rel ++ facts).eraseDups })
    | _, _ => some st
  | _, _ => some st

/-! ## Memory accesses -/

/-- Load of `w` bytes from the stack byte range of an `sp` address `[x, y)`. -/
def stkLoad (st : AbsState) (x y : Int) (w : Nat) : AbsVal :=
  if x == y && w == 4 && x % 4 == 0 then stkGet st.stk x else .hi

/-- Store of `v` (`w` bytes) at stack offsets `x..y` (the address interval). -/
def stkStore (st : AbsState) (x y : Int) (w : Nat) (v : AbsVal) : Stk :=
  if x == y && w == 4 && x % 4 == 0 then stkSet st.stk x v
  else stkForget st.stk x (y + w)

/-- Result of one load or store through address value `a`. -/
def access (env : Env) (st : AbsState) (a : AbsVal) (w : Nat) (isLoad : Bool) (t : Nat) :
    Except String (AbsState × List SiteK) :=
  match a with
  | .hi => .error "access through a secret address"
  | .sp x y =>
    if !env.win.covers x (y + w) then .error s!"stack access [{x}, {y + w}) outside the window"
    else if isLoad then .ok (st.set t (stkLoad st x y w), [])
    else .ok ({ st with stk := stkStore st x y w (st.get t) }, [])
  | _ =>
    if isLoad then .ok (st.set t .hi, [.load]) else .ok (st, [.store])

def regsOf (l : BitVec 8) : List Nat := (listRegs l).map (·.val)

/-! ## Branch targets -/

def relTarget (off : Nat) (disp : Int) : Option Nat :=
  let t := (off : Int) + 4 + disp
  if 0 ≤ t then some t.toNat else none

def bcondDisp (imm : BitVec 8) : Int := ((imm ++ 0#1).signExtend 32).toInt
def bDisp (imm : BitVec 11) : Int := ((imm ++ 0#1).signExtend 32).toInt
def blDisp (imm : BitVec 25) : Int := (imm.signExtend 32).toInt

/-! ## Transfer -/

/-- After `R[r] := R[r] + δ` (no wrap, checked on the pre-state interval), the links of `r`
move along. -/
def shiftLinks (w : StackWindow) (pre : AbsState) (r : Nat) (δ : Int) (post : AbsState) : AbsState :=
  let ok : Bool := match pre.get r, ival (pre.get r) with
    | .sp _ _, _ => true
    | _, some (l, h) => decide (0 ≤ (l : Int) + δ) && decide ((h : Int) + δ < AbsVal.word)
    | _, none => false
  if !ok then post else
  let moved := pre.lnk.filterMap fun l =>
    if l.i == r && l.j == r then none
    else if l.i == r then some { l with c := l.c + δ }
    else if l.j == r then some { l with c := l.c - l.k * δ }
    else none
  AbsState.tighten w { post with lnk := (post.lnk ++ moved).eraseDups }

/-- After `R[d] := R[n] + 1`, a fact `R[n] < R[j]` (with `j ≠ d`) becomes `R[d] ≤ R[j]`;
the addition cannot wrap because `R[n] < R[j] < 2³²`. `pre` is the state before the
instruction, `post` the state after it. -/
def incFacts (pre : AbsState) (d n k : Nat) (post : AbsState) : AbsState :=
  if k == 1 then
    let new : List Fact := pre.rel.filterMap fun (i, j, strict) =>
      if i == n && strict && j != d && j != 13 then some (d, j, false) else none
    { post with rel := (post.rel ++ new).eraseDups }
  else post

def fall (off : Nat) (ctx : Option Nat) (i : Instr) (st : AbsState) : Except String Out :=
  .ok ⟨[(.pt (off + i.size) ctx, st)], []⟩

def xferCore (env : Env) (off : Nat) (ctx : Option Nat) (i : Instr) (st : AbsState) :
    Except String Out :=
  let g := st.get
  match i with
  | .lslImm d m imm5 =>
    let v := g m.val
    if imm5.toNat = 0 then
      fall off ctx i { st.set d.val v with fl := setNZ st.fl v.pub }
    else
      let r := match v.exact? with
        | some a => .cst ((a <<< imm5.toNat) % AbsVal.word)
        | none => AbsVal.ofPub v.pub
      fall off ctx i { st.set d.val r with fl := setNZC st.fl v.pub v.pub }
  | .lsrImm d m imm5 =>
    let v := g m.val
    let n := if imm5.toNat = 0 then 32 else imm5.toNat
    let r := match v with
      | .num a b => .num (a >>> n) (b >>> n)
      | _ => AbsVal.ofPub v.pub
    fall off ctx i { st.set d.val r with fl := setNZC st.fl v.pub v.pub }
  | .addReg d n m =>
    let (r, f) := addRes (g n.val) (g m.val) (.known false) (AbsVal.add (g n.val) (g m.val))
    fall off ctx i { st.set d.val r with fl := f }
  | .subReg d n m =>
    let (r, f) := addRes (g n.val) (notWord (g m.val)) (.known true) (AbsVal.sub (g n.val) (g m.val))
    fall off ctx i { st.set d.val r with fl := f }
  | .addImm3 d n imm3 =>
    let (r, f) := addRes (g n.val) (.cst imm3.toNat) (.known false) ((g n.val).addK imm3.toNat)
    fall off ctx i (incFacts st d.val n.val imm3.toNat { st.set d.val r with fl := f })
  | .subImm3 d n imm3 =>
    let (r, f) := addRes (g n.val) (notWord (.cst imm3.toNat)) (.known true) ((g n.val).subK imm3.toNat)
    fall off ctx i { st.set d.val r with fl := f }
  | .movImm d imm8 =>
    let f := { st.fl with n := .known false, z := .known (imm8.toNat == 0), cmp := none }
    fall off ctx i { st.set d.val (.cst imm8.toNat) with fl := f }
  | .cmpImm n imm8 =>
    let (_, f) := addRes (g n.val) (notWord (.cst imm8.toNat)) (.known true) .lo
    let f := if (g n.val).pub then { f with cmp := some ⟨n.val, .imm imm8.toNat, false⟩ } else f
    fall off ctx i { st with fl := f }
  | .addImm8 dn imm8 =>
    let (r, f) := addRes (g dn.val) (.cst imm8.toNat) (.known false) ((g dn.val).addK imm8.toNat)
    fall off ctx i (shiftLinks env.win st dn.val imm8.toNat
      (incFacts st dn.val dn.val imm8.toNat { st.set dn.val r with fl := f }))
  | .subImm8 dn imm8 =>
    let (r, f) := addRes (g dn.val) (notWord (.cst imm8.toNat)) (.known true) ((g dn.val).subK imm8.toNat)
    -- Z says whether the result is zero
    let f := if r.pub then { f with cmp := some ⟨dn.val, .imm 0, true⟩ } else f
    fall off ctx i (shiftLinks env.win st dn.val (-(imm8.toNat : Int)) { st.set dn.val r with fl := f })
  | .dp op dn m =>
    let a := g dn.val
    let b := g m.val
    let p := a.pub && b.pub
    match op with
    | .ands =>
      -- `x &&& y ≤ min x y`; Z says whether the result is zero
      let r := match ival a, ival b with
        | some (_, ha), some (_, hb) => if min ha hb < AbsVal.word - 1 then .num 0 (min ha hb) else .lo
        | _, _ => AbsVal.ofPub p
      let st' := st.set dn.val r
      let f := setNZ st.fl p
      let f := if p then { f with cmp := some ⟨dn.val, .imm 0, true⟩ } else f
      fall off ctx i { st' with fl := f }
    | .eors | .orrs | .muls =>
      fall off ctx i { st.set dn.val (AbsVal.ofPub p) with fl := setNZ st.fl p }
    | .mvns => fall off ctx i { st.set dn.val (notWord b) with fl := setNZ st.fl b.pub }
    | .tst => fall off ctx i { st with fl := setNZ st.fl p }
    | .adcs =>
      let q := p && st.fl.c.pub
      fall off ctx i { st.set dn.val (AbsVal.ofPub q) with fl := AFl.all (AbsFlags.ofPub q) }
    | .rsbs =>
      fall off ctx i { st.set dn.val (AbsVal.ofPub b.pub) with fl := AFl.all (AbsFlags.ofPub b.pub) }
    | .cmp =>
      let f := AFl.all (AbsFlags.ofPub p)
      let f := if p then { f with cmp := some ⟨dn.val, .reg m.val, false⟩ } else f
      fall off ctx i { st with fl := f }
    | .rors =>
      fall off ctx i
        { st.set dn.val (AbsVal.ofPub p) with fl := setNZC st.fl p (p && st.fl.c.pub) }
  | .movHi d m =>
    if d.val == 13 || d.val == 15 || m.val == 13 || m.val == 15 then
      .error "register move uses SP or PC"
    else fall off ctx i (st.set d.val (g m.val))
  | .ldrLit t imm8 =>
    let lit := (off + 4) / 4 * 4 + imm8.toNat * 4
    if lit + 4 ≤ env.size then fall off ctx i (st.set t.val .lo)
    else .error s!"literal at {lit} outside the artifact"
  | .memReg op t n m =>
    let a := AbsVal.add (g n.val) (g m.val)
    match a, g n.val, g m.val with
    | .lo, .sp _ _, _ | .lo, _, .sp _ _ => .error "stack access with an unbounded index"
    | _, _, _ =>
      match access env st a op.width op.isLoad t.val with
      | .error e => .error e
      | .ok (st', ks) => .ok ⟨[(.pt (off + 2) ctx, st')], ks⟩
  | .memImm op t n imm5 =>
    let a := (g n.val).addK (imm5.toNat * op.width)
    match access env st a op.width op.isLoad t.val with
    | .error e => .error e
    | .ok (st', ks) => .ok ⟨[(.pt (off + 2) ctx, st')], ks⟩
  | .strSp t imm8 =>
    let o := st.spOff + (imm8.toNat * 4 : Nat)
    if env.win.covers o (o + 4) then
      fall off ctx i { st with stk := stkSet st.stk o (g t.val) }
    else .error s!"str to SP offset {o} outside the window"
  | .ldrSp t imm8 =>
    let o := st.spOff + (imm8.toNat * 4 : Nat)
    if env.win.covers o (o + 4) then fall off ctx i (st.set t.val (stkGet st.stk o))
    else .error s!"ldr from SP offset {o} outside the window"
  | .addRdSp d imm8 =>
    let o := st.spOff + (imm8.toNat * 4 : Nat)
    fall off ctx i (st.set d.val (.sp o o))
  | .addSp imm7 => fall off ctx i { st with spOff := st.spOff + (imm7.toNat * 4 : Nat) }
  | .subSp imm7 => fall off ctx i { st with spOff := st.spOff - (imm7.toNat * 4 : Nat) }
  | .uxth d m =>
    let v := g m.val
    let r := match v with
      | .num a b => if b < 65536 then .num a b else .num 0 65535
      | .hi => .hi
      | _ => .num 0 65535
    fall off ctx i (st.set d.val r)
  | .push l lr =>
    let rs := regsOf l ++ (if lr then [14] else [])
    let base := st.spOff - (4 * rs.length : Nat)
    if !env.win.covers base st.spOff then .error "push outside the window" else
    let stk := (rs.zip (List.range rs.length)).foldl
      (fun s (r, k) => stkSet s (base + (4 * k : Nat)) (g r)) st.stk
    fall off ctx i { st with spOff := base, stk := stk }
  | .pop l pcBit =>
    let rs := regsOf l
    let cnt := rs.length + (if pcBit then 1 else 0)
    if !env.win.covers st.spOff (st.spOff + (4 * cnt : Nat)) then
      .error "pop outside the window"
    else
      let st1 := (rs.zip (List.range rs.length)).foldl
        (fun s (r, k) => s.set r (stkGet st.stk (st.spOff + (4 * k : Nat)))) st
      let st2 := { st1 with spOff := st.spOff + (4 * cnt : Nat) }
      if pcBit then
        match stkGet st.stk (st.spOff + (4 * rs.length : Nat)), ctx with
        | .ret r, some r' => if r == r' then .ok ⟨[(.pt r none, st2)], []⟩
                             else .error s!"return to {r}, expected {r'}"
        | .lr0, none => .ok ⟨[(.exit, st2)], []⟩
        | v, _ => .error s!"pop pc of {repr v} in context {ctx}"
      else .ok ⟨[(.pt (off + 2) ctx, st2)], []⟩
  | .stm n l =>
    let rs := regsOf l
    let a := g n.val
    let nb := 4 * rs.length
    match a with
    | .hi => .error "stm through a secret address"
    | .sp x y =>
      if !env.win.covers x (y + nb) then .error "stm outside the window" else
      let stk := if x == y && x % 4 == 0 then
          (rs.zip (List.range rs.length)).foldl
            (fun s (r, k) => stkSet s (x + (4 * k : Nat)) (g r)) st.stk
        else stkForget st.stk x (y + nb)
      fall off ctx i ({ st with stk := stk }.set n.val (a.addK nb))
    | _ => .ok ⟨[(.pt (off + 2) ctx, st.set n.val (a.addK nb))], [.store]⟩
  | .ldm n l =>
    let rs := regsOf l
    let a := g n.val
    let nb := 4 * rs.length
    let wb := !(rs.contains n.val)
    match a with
    | .hi => .error "ldm through a secret address"
    | .sp x y =>
      if !env.win.covers x (y + nb) then .error "ldm outside the window" else
      let st1 := (rs.zip (List.range rs.length)).foldl
        (fun s (r, k) => s.set r (if x == y && x % 4 == 0 then stkGet st.stk (x + (4 * k : Nat))
                                  else .hi)) st
      fall off ctx i (if wb then st1.set n.val (a.addK nb) else st1)
    | _ =>
      let st1 := rs.foldl (fun s r => s.set r .hi) st
      .ok ⟨[(.pt (off + 2) ctx, if wb then st1.set n.val (a.addK nb) else st1)], [.load]⟩
  | .bcond cond imm8 =>
    match relTarget off (bcondDisp imm8) with
    | none => .error "branch target before the artifact"
    | some tgt =>
      if env.declass == some off then
        .ok ⟨[(.pt (off + 2) ctx, st), (.pt tgt ctx, st)], [.declass]⟩
      else if !condFlagsPub cond.toNat st.fl then
        .error s!"conditional branch on secret flags (cond {cond.toNat})"
      else
        let edge := fun (taken : Bool) (pc : Nat) =>
          match evalCond cond.toNat st.fl with
          | some b => if b == taken then [(Tgt.pt pc ctx, st)] else []
          | none => match refine env.win st cond.toNat taken with
            | some st' => [(Tgt.pt pc ctx, st')]
            | none => []
        .ok ⟨edge false (off + 2) ++ edge true tgt, []⟩
  | .b imm11 =>
    match relTarget off (bDisp imm11) with
    | none => .error "branch target before the artifact"
    | some tgt => .ok ⟨[(.pt tgt ctx, st)], []⟩
  | .bl imm25 =>
    if ctx.isSome then .error "nested call" else
    match relTarget off (blDisp imm25) with
    | none => .error "call target before the artifact"
    | some tgt => .ok ⟨[(.pt tgt (some (off + 4)), st.set 14 (.ret (off + 4)))], []⟩

/-- Transfer with the SP-window obligation checked first. -/
def xfer (env : Env) (off : Nat) (ctx : Option Nat) (i : Instr) (st : AbsState) : Except String Out :=
  if env.win.covers st.spOff st.spOff && decide (st.spOff ≤ 0) then xferCore env off ctx i st
  else .error s!"SP offset {st.spOff} outside the window"

end M0Crypto.Release.ConstantTime
