import M0Crypto.Release.Ed25519CallProgPub
import M0Crypto.Release.ReachTrace

set_option linter.unusedSimpArgs false

/-!
# Call programs: typing, values and traces

`Prog.ty` checks a program against the static state `St` between constructs (the live views, the
registers whose symbolic values are known, the buffer regions written so far) and returns the
state after it. It decides, per construct, every condition that does not depend on the code
bytes: each operand resolves, each input has a source (a view, a slice of a byte view, or a
buffer's entry bytes or field element), alignment, equal-or-apart arguments, constants,
footprints inside the frame or a buffer, publicity of the callee's public registers, which views
a write ends. `Prog.bok` checks what depends on the code (the call sites and blocks at their
offsets). `Prog.ev` is the program's value transformer and `Prog.tr` its trace, a function of the
public context alone.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces

/-! ## Static state -/

/-- The static state between constructs. -/
structure St where
  Γ : List (Loc × Kd)
  σ : List (Reg × SV)
  X : List SR
  /-- Registers holding a block's outputs, their values at `.rg r`. -/
  ρ : List Reg := []
  /-- The exit the program takes, to the enclosing construct of this level. -/
  ex : Option Nat := none
  deriving DecidableEq

/-- Only `sp` known. -/
def σsp : List (Reg × SV) := [(13, .sp 0)]

/-- Where an input's value comes from. -/
inductive Src where
  /-- The view at the location. -/
  | view (l : Loc)
  /-- `n` bytes from `d` of the byte view at `l`. -/
  | slice (l : Loc) (d n : Nat)
  /-- The entry bytes of a buffer region. -/
  | ext (r : SR)
  /-- The field element of a buffer's entry bytes. -/
  | extF (r : SR)
  /-- A register's public value. -/
  | pv (v : SV)

/-- A source of a field element in a buffer's entry bytes. -/
def Src.isXF : Src → Bool
  | .extF _ => true
  | _ => false

def Loc.diff : Loc → Loc → Option Nat
  | .fr o, .fr p => if p ≤ o then some (o - p) else none
  | .ex i e, .ex j f => if i = j ∧ f ≤ e then some (e - f) else none
  | _, _ => none

/-- A byte view that covers `n` bytes at `l`. -/
def findSlice (Γ : List (Loc × Kd)) (l : Loc) (n : Nat) : Option Src :=
  Γ.findSome? fun p => match p.2 with
    | .bytes n0 => match l.diff p.1 with
      | some d => if d + n ≤ n0 then some (.slice p.1 d n) else none
      | none => none
    | _ => none

def Loc.isEx : Loc → Bool
  | .ex _ _ => true
  | _ => false

/-- A view of `l` whose kind serves where kind `k` is required (`Kd.le`). -/
def viewOf (Γ : List (Loc × Kd)) (l : Loc) (k : Kd) : Bool := Γ.any fun p => p.1 == l && p.2.le k

/-- A bounded buffer of refined kind `k`: the start of a buffer whose entry bytes hold a kind that
serves as `k`, not written so far. -/
def refSrc (G : Geo) (st : St) (l : Loc) (k : Kd) : Option Src :=
  match l with
  | .ex i 0 => if st.X = [] ∧ G.xv.any (fun p => p.1 == i && p.2.le k) ∧ SR.ok G ⟨l, .k 32⟩ ∧
      SR.acc G false ⟨l, .k 32⟩ then some (.ext ⟨l, .k 32⟩) else none
  | _ => none

theorem viewOf_mem {Γ : List (Loc × Kd)} {l : Loc} {k : Kd} (h : viewOf Γ l k = true) :
    ∃ k', (l, k') ∈ Γ ∧ k'.le k = true := by
  obtain ⟨⟨l', k'⟩, hm, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨k', hp.1 ▸ hm, hp.2⟩

theorem refSrc_some {G : Geo} {st : St} {l : Loc} {k : Kd} {s : Src} (h : refSrc G st l k = some s) :
    ∃ i k', l = .ex i 0 ∧ s = .ext ⟨l, .k 32⟩ ∧ st.X = [] ∧ (i, k') ∈ G.xv ∧ k'.le k = true ∧
      SR.ok G ⟨l, .k 32⟩ = true ∧ SR.acc G false ⟨l, .k 32⟩ = true := by
  unfold refSrc at h
  split at h
  · rename_i i
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      obtain ⟨⟨i', k'⟩, hm, hp⟩ := List.any_eq_true.mp hc.2.1
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨i, k', rfl, h.symm, hc.1, hp.1 ▸ hm, hp.2, hc.2.2.1, hc.2.2.2⟩
    · simp at h
  · simp at h

/-- A read of a code buffer, valid after any writes: every written region is an `ok` writable
one, so apart from the code buffer (`GeoOk.cdW`). -/
def codeRd (G : Geo) (st : St) : Loc → Bool
  | .ex i _ => (G.cd.lookup i).isSome && st.X.all fun r => r.ok G && r.acc G true
  | _ => false

/-- The source of input `(r, off, i)` with registers `σ`. -/
def inSrc (G : Geo) (st : St) (σ : List (Reg × SV)) (x : Reg × Nat × In) : Option Src :=
  if x.2.2 = .view .rw then
    if x.1 ∈ st.ρ ∧ x.2.1 = 0 ∧ σ.all (·.1 != x.1) then some (.view (.rg x.1))
    else if x.2.1 = 0 then (σ.lookup x.1).map .pv else none
  else match locOf σ x.1 x.2.1, x.2.2 with
  | none, _ => none
  | some l, .view k =>
    if viewOf st.Γ l k then some (.view l) else match k with
      | .bytes n => findSlice st.Γ l n
      | .fe => if (st.X = [] ∨ codeRd G st l) ∧ l.isEx ∧ SR.ok G ⟨l, .k 32⟩ ∧ SR.acc G false ⟨l, .k 32⟩ then
          some (.extF ⟨l, .k 32⟩) else none
      | .sc => refSrc G st l .sc
      | .cl => refSrc G st l .cl
      | _ => none
  | some l, .raw len => match len.res σ with
    | none => none
    | some xl =>
      let ex := if (st.X = [] ∨ codeRd G st l) ∧ l.isEx ∧ SR.ok G ⟨l, xl⟩ ∧ SR.acc G false ⟨l, xl⟩ then
        some (Src.ext ⟨l, xl⟩) else none
      match xl with
      | .k n => (findSlice st.Γ l n).or ex
      | .p _ => ex

/-- A symbolic value is a word-aligned address. -/
def SV.al (G : Geo) : SV → Bool
  | .sp o => o % 4 == 0
  | .ext i e => e % 4 == 0 && (match G.xs[i]? with | some x => x.al4 | none => false)
  | .k n => n % 4 == 0
  | .prm _ => false

/-- The pair is equal, or apart over `n` bytes (also a code buffer against a writable region). -/
def eqdOk (G : Geo) (σ : List (Reg × SV)) (p : Reg × Reg × Nat) : Bool :=
  match locOf σ p.1 0, locOf σ p.2.1 0 with
  | some a, some b => a == b ||
      (decide (0 < p.2.2) && SR.ok G ⟨a, .k p.2.2⟩ && SR.ok G ⟨b, .k p.2.2⟩ &&
        (SR.apart ⟨a, .k p.2.2⟩ ⟨b, .k p.2.2⟩ || SR.cdSep G ⟨a, .k p.2.2⟩ ⟨b, .k p.2.2⟩ ||
          SR.cdSep G ⟨b, .k p.2.2⟩ ⟨a, .k p.2.2⟩))
  | _, _ => false

/-- The two regions resolve, lie in the geometry and lie apart. -/
def aptOk (G : Geo) (σ : List (Reg × SV)) (p : SRgn × SRgn) : Bool :=
  match p.1.res σ, p.2.res σ with
  | some a, some b => a.ok G && b.ok G && a.apart b
  | _, _ => false

/-- The sum of public lengths stays below `p.2`. -/
def limOk (G : Geo) (p : List SV × Nat) : Bool :=
  match smax G p.1 with
  | some x => decide (x < p.2)
  | none => false

/-- The views of `Γ` that the writes `ws` leave and that are not at an output location. -/
def keepViews (Γ : List (Loc × Kd)) (ws : List SR) (outs : List (Loc × Kd)) : List (Loc × Kd) :=
  Γ.filter fun p => ws.all (fun w => (Kd.sr p.1 p.2).apart w) && !(outs.any fun q => q.1 == p.1)

/-- The resolved interface at registers `σ`: input sources, output views, write regions. -/
structure IoR where
  srcs : List Src
  outs : List (Loc × Kd)
  wrs : List SR

/-- **The decided checks of an interface** at registers `σ`, and its resolution. -/
def ioRes (G : Geo) (st : St) (σ : List (Reg × SV)) (io : Iface) : Option IoR := do
  let srcs ← io.ins.mapM (inSrc G st σ)
  let outs ← io.outs.mapM fun x => (locOf σ x.1 x.2.1).map (·, x.2.2)
  let wrs ← io.wr.mapM (SRgn.res σ)
  let rds ← io.rd.mapM (SRgn.res σ)
  if wrs.all (fun r => r.ok G && r.acc G true) && rds.all (fun r => r.ok G && r.acc G false) &&
      outs.all (fun p => (Kd.sr p.1 p.2).ok G && p.2 != .cw) && (outs.map (·.1)).Nodup &&
      io.al.all (fun r => ((σ.lookup r).map (SV.al G)).getD false) &&
      io.eqd.all (eqdOk G σ) && io.kreq.all (fun p => σ.lookup p.1 == some (.k p.2)) &&
      io.kreqv.all (fun p => σ.lookup p.1 == some p.2) && io.lim.all (limOk G) &&
      io.apt.all (aptOk G σ) then
    some ⟨srcs, outs, wrs⟩
  else none

/-- The static state after an interface's run. -/
def IoR.after (st : St) (r : IoR) (σ : List (Reg × SV)) : St :=
  { Γ := r.outs ++ keepViews st.Γ r.wrs r.outs, σ, X := st.X ++ r.wrs.filter (·.loc.isEx) }

/-- Every register of `L` has a known value. -/
def pubOk (σ : List (Reg × SV)) (L : List Reg) : Bool := L.all fun r => (σ.lookup r).isSome

/-- The public length of the context view at register `r`. -/
def ctxAt (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) (r : Reg) : Option (List SV) :=
  (locOf σ r 0).bind fun l => Γ.findSome? fun p => match p with
    | (l', .ctx n) => if l' = l then some n else none
    | _ => none

/-- Every public value of a call is known. -/
def pubsOk (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) (L : List PubW) : Bool :=
  L.all fun | .r r => (σ.lookup r).isSome | .n r => (ctxAt Γ σ r).isSome

/-- The loads resolve. -/
def ldsRes (Γ : List (Loc × Kd)) (as : List (LowReg × Ld)) : Bool :=
  ldsOk as && as.all fun a => (a.2.sv Γ).isSome

/-- Register `p.1` holds a frame address with `p.2` bytes below the frame's top from it. -/
def nwOk (G : Geo) (σ : List (Reg × SV)) (p : Reg × Nat) : Bool :=
  match σ.lookup p.1 with
  | some (.sp o) => decide (o + p.2 ≤ G.top)
  | _ => false

/-- The frame word at `o` is a valid slot. -/
def slotOk (G : Geo) (o : Nat) : Bool := o % 4 == 0 && decide (o + 4 ≤ G.top) && decide (o ≤ 1020)

/-- The views apart from the frame bytes `[o, o + n)`. -/
def dropViews (Γ : List (Loc × Kd)) (o n : Nat) : List (Loc × Kd) :=
  keepViews Γ [⟨.fr o, .k n⟩] []

/-- The symbolic value a loader of its own leaves in `r`: `A` adds to `r`'s address, `C` is the
address into a code buffer. -/
def ldSv (G : Geo) (st : St) (r : LowReg) : Ld → Option SV
  | .A k => match st.σ.lookup r.toReg with
    | some (.sp o) => some (.sp (o + k))
    | some (.ext i e) => some (.ext i (e + k))
    | _ => none
  | .C i e _ => if (G.cd.lookup i).isSome then some (.ext i e) else none
  | l => if l.ok then l.sv st.Γ else none

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- The registers after a block's instructions `g`: `sp`, and those of `σ` below `r13` that `g` does
not write. -/
def blkσ (g : List Instr) (σ : List (Reg × SV)) : List (Reg × SV) :=
  σsp ++ σ.filter fun p => decide (p.1.val < 13) && g.all fun i => !(i.dsts.contains p.1.val)

/-- The frame offset `o + j` that `ldrb rd, [rb, ri]` reads, with `rb` the frame address `o` and
`ri` the constant `j`. -/
def ldbOff (σ : List (Reg × SV)) (rb ri : LowReg) : Option Nat :=
  match σ.lookup rb.toReg, σ.lookup ri.toReg with
  | some (.sp o), some (.k j) => some (o + j)
  | _, _ => none

/-- The views of `Γ` at the locations `ls`, in that order. -/
def keepΓ (Γ : List (Loc × Kd)) (ls : List Loc) : Option (List (Loc × Kd)) :=
  ls.mapM fun l => Γ.find? (·.1 == l)

/-- **The static check of one construct**, and the state after it. -/
def Op.ty (st : St) : Op A Bk → Option St
  | .call a as =>
    let σ' := regsOf st.Γ st.σ as
    if ldsRes st.Γ as && pubsOk st.Γ σ' (cE a).pubs && decide (G.top + (cE a).stack ≤ G.N) then
      (ioRes G st σ' (cE a).io).map (·.after st σsp)
    else none
  | .blk b as =>
    let σ' := regsOf st.Γ st.σ as
    if ldsRes st.Γ as && pubOk σ' (bE b).L && (bE b).io.wr.all (fun r => r.len matches .k _) &&
        (bE b).io.rd.all (fun r => r.len matches .k _) && (bE b).io.nw.all (nwOk G σ') &&
        (bE b).io.ro.all (·.val < 13) then
      (ioRes G st σ' (bE b).io).map fun r => { r.after st (blkσ (bE b).g σ') with ρ := (bE b).io.ro }
    else none
  | .spill r o =>
    match st.σ.lookup r.toReg with
    | some v => if slotOk G o then
        some { st with Γ := (.fr o, .pw v) :: keepViews st.Γ [⟨.fr o, .k 4⟩] [(.fr o, .pw v)] }
      else none
    | none => none
  | .drop o n => some { st with Γ := dropViews st.Γ o n }
  | .ld r l => (ldSv G st r l).map fun v =>
    { st with σ := (r.toReg, v) :: st.σ.filter (·.1 != r.toReg), ρ := st.ρ.filter (· != r.toReg) }
  | .pub g => (pubEval st.σ st.Γ g).map fun r => { st with σ := r.σ, ρ := [] }
  | .keep ls => (keepΓ st.Γ ls).map fun Γ => { st with Γ, σ := σsp, ρ := [] }
  | .ldb rd rb ri => match ldbOff st.σ rb ri with
    | some a => if decide (a + 1 ≤ G.top) && (findSlice st.Γ (.fr a) 1).isSome then
        some { st with σ := st.σ.filter (·.1 != rd.toReg), ρ := rd.toReg :: st.ρ.filter (· != rd.toReg) }
      else none
    | none => none
  | .isl _ _ => some st

/-- The state after `str r, [sp, #o]` (a spill). -/
def spillSt (st : St) (r : LowReg) (o : Nat) : Option St :=
  match st.σ.lookup r.toReg with
  | some v => if slotOk G o then
      some { st with Γ := (.fr o, .pw v) :: keepViews st.Γ [⟨.fr o, .k 4⟩] [(.fr o, .pw v)] }
    else none
  | none => none

/-- **A test's state and decision**: the public block's registers, then its store, and whether the
branch is taken. -/
def xitSt (st : St) (g : List Instr) (s : Option (LowReg × Nat)) (cc : BitVec 4) : Option (St × Bool) :=
  match pubEval st.σ st.Γ g with
  | some r =>
    let st1 : St := { st with σ := r.σ, ρ := [] }
    match (match s with | none => some st1 | some (q, o) => spillSt G st1 q o), r.dec cc with
    | some st2, some b => if cc.toNat < 14 then some (st2, b) else none
    | _, _ => none
  | none => none

/-- The passes of a loop with exits: the body's typing `tb`, the rest's `tk`. -/
def whTy (tb tk : St → Option St) : Nat → St → Option St
  | 0, _ => none
  | n + 1, st => match tb st with
    | some s => match s.ex with
      | none => whTy tb tk n s
      | some 0 => tk { s with ex := none }
      | some (l + 1) => some { s with ex := some l }
    | none => none

/-- A list contained in another. -/
def subL {α : Type} [DecidableEq α] (a b : List α) : Bool := a.all (· ∈ b)

/-- The views apart from the counter word at `cnt`. -/
def cntViews (Γ : List (Loc × Kd)) (cnt : Nat) : List (Loc × Kd) :=
  keepViews Γ [⟨.fr cnt, .k 4⟩] [(.fr cnt, .cw)]

/-- The state a loop body starts from: the counter view and the views apart from it. -/
def loopSt (st : St) (cnt : Nat) : St := { Γ := (.fr cnt, .cw) :: cntViews st.Γ cnt, σ := σsp, X := st.X }

/-- The state after a loop. -/
def loopOut (st : St) (cnt : Nat) : St := { Γ := cntViews st.Γ cnt, σ := σsp, X := st.X }

/-- The state a dispatch arm starts from. -/
def selSt (st : St) : St := { Γ := st.Γ, σ := σsp, X := st.X }

/-- The join of two arms: their common views. -/
def joinSt (s₀ s₁ : St) : St := { Γ := s₀.Γ.filter (· ∈ s₁.Γ), σ := σsp, X := s₀.X ++ s₁.X }

/-- **The static check of a program**, and the state after it. A loop's body ends with the
views it starts from and the counter, apart from the counter, and writes no buffer. The two arms
of a dispatch join on their common views. -/
def Prog.ty : Prog A Bk → St → Option St
  | .nil, st => some st
  | .op x k, st => (x.ty cE bE G st).bind k.ty
  | .loop cnt n b k, st =>
    match b.ty (loopSt st cnt) with
    | some sB =>
      if slotOk G cnt && decide (0 < n) && decide (n < 256) && (Loc.fr cnt, Kd.cw) ∈ sB.Γ &&
          subL (loopSt st cnt).Γ ((.fr cnt, .cw) :: cntViews sB.Γ cnt) && sB.X == st.X && sB.ex == none then
        k.ty (loopOut st cnt)
      else none
    | none => none
  | .sel w i p₀ p₁ k, st =>
    match pwAt st.Γ w, p₀.ty (selSt st), p₁.ty (selSt st) with
    | some _, some s₀, some s₁ =>
      if slotOk G w && decide (i < 256) && s₀.ex == none && s₁.ex == none then k.ty (joinSt s₀ s₁) else none
    | _, _, _ => none
  | .xit g s cc _ l k, st =>
    match xitSt G st g s cc with
    | some (st2, true) => some { st2 with ex := some l }
    | some (st2, false) => k.ty st2
    | none => none
  | .hd b h k, st =>
    match b.ty st with
    | some s => match s.ex with
      | none => k.ty s
      | some 0 => match h.ty { s with ex := none } with
        | some s' => if s'.ex = none then k.ty s' else some s'
        | none => none
      | some (l + 1) => some { s with ex := some l }
    | none => none
  | .wh n b k, st => whTy (fun s => b.ty s) (fun s => k.ty s) n st

/-! ## Values -/

/-- The value of a source. -/
def Src.val (c : Ctx) (m0 : Mem) (E : Loc → V) : Src → V
  | .view l => E l
  | .slice l d n => match E l with
    | .b L => .b ((L.drop d).take n)
    | _ => .none
  | .ext r => .b (bytesAt m0 (r.loc.addr c (G.fsp c)) (r.len.v c))
  | .extF r => .f (Field25519Routines.feVal m0 (r.loc.addr c (G.fsp c)))
  | .pv v => .w (v.val c (G.fsp c))

/-- `E` with the outputs `outs` set to `vs`. -/
def updOuts (E : Loc → V) : List (Loc × Kd) → List V → Loc → V
  | (l, _) :: outs, v :: vs => fun x => if x = l then v else updOuts E outs vs x
  | _, _ => E

/-- A loaded byte as a word. -/
def byteW : V → V
  | .b [x] => .w (x.setWidth 32)
  | _ => .none

/-- `E` with register `ro[i]` holding `ws[i]`. -/
def setRg (E : Loc → V) (ro : List Reg) (ws : List V) : Loc → V
  | .rg q => if q ∈ ro then ws[ro.idxOf q]?.getD .none else E (.rg q)
  | l => E l

variable (semA : A → List V → List V) (semB : Bk → List V → List V)

/-- The values after one construct. -/
def Op.ev (c : Ctx) (m0 : Mem) (st : St) : Op A Bk → (Loc → V) → Loc → V
  | .call a as, E => match ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | some r => updOuts E r.outs (semA a (r.srcs.map (Src.val G c m0 E)))
    | none => E
  | .blk b as, E => match ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
    | some r => let w := semB b (r.srcs.map (Src.val G c m0 E))
      setRg (updOuts E r.outs (w.take (bE b).io.outs.length)) (bE b).io.ro (w.drop (bE b).io.outs.length)
    | none => E
  | .spill _ _, E => E
  | .drop _ _, E => E
  | .ld _ _, E => E
  | .pub _, E => E
  | .keep _, E => E
  | .ldb rd rb ri, E => match ldbOff st.σ rb ri with
    | some a => match findSlice st.Γ (.fr a) 1 with
      | some s => setRg E [rd.toReg] [byteW (Src.val G c m0 E s)]
      | none => E
    | none => E
  | .isl _ _, E => E

/-- `E` with the counter at `cnt` holding `v`. -/
def setCnt (E : Loc → V) (cnt v : Nat) : Loc → V :=
  fun x => if x = .fr cnt then .w (BitVec.ofNat 32 v) else E x

/-- `r` passes of a loop body `f` with the counter `r`, `r - 1`, …, `1`. -/
def loopIt (f : (Loc → V) → Loc → V) (cnt : Nat) : Nat → (Loc → V) → Loc → V
  | 0, E => E
  | r + 1, E => loopIt f cnt r (f (setCnt E cnt (r + 1)))

/-- The values after the passes of a loop with exits: the body's typing `tb` and values `eb`, the
rest's values `ek`. -/
def whEv (tb : St → Option St) (eb ek : St → (Loc → V) → Loc → V) : Nat → St → (Loc → V) → Loc → V
  | 0, _, E => E
  | n + 1, st, E => match tb st with
    | some s => match s.ex with
      | none => whEv tb eb ek n s (eb st E)
      | some 0 => ek { s with ex := none } (eb st E)
      | some _ => eb st E
    | none => E

/-- **The values after a program**, from the values `E` before it. -/
def Prog.ev (c : Ctx) (m0 : Mem) : Prog A Bk → St → (Loc → V) → Loc → V
  | .nil, _, E => E
  | .op x k, st, E => match x.ty cE bE G st with
    | some st' => k.ev c m0 st' (x.ev cE bE G semA semB c m0 st E)
    | none => E
  | .loop cnt n b k, st, E =>
    k.ev c m0 (loopOut st cnt) (loopIt (b.ev c m0 (loopSt st cnt)) cnt n E)
  | .sel w i p₀ p₁ k, st, E =>
    match pwAt st.Γ w, p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
    | some v, some s₀, some s₁ =>
      k.ev c m0 (joinSt s₀ s₁) (if v.val c (G.fsp c) == BitVec.ofNat 32 i then
        p₁.ev c m0 (selSt st) E else p₀.ev c m0 (selSt st) E)
    | _, _, _ => E
  | .xit g s cc _ _ k, st, E =>
    match xitSt G st g s cc with
    | some (st2, false) => k.ev c m0 st2 E
    | _ => E
  | .hd b h k, st, E =>
    match b.ty cE bE G st with
    | some s => match s.ex with
      | none => k.ev c m0 s (b.ev c m0 st E)
      | some 0 => match h.ty cE bE G { s with ex := none } with
        | some s' => if s'.ex = none then k.ev c m0 s' (h.ev c m0 { s with ex := none } (b.ev c m0 st E))
          else h.ev c m0 { s with ex := none } (b.ev c m0 st E)
        | none => b.ev c m0 st E
      | some _ => b.ev c m0 st E
    | none => E
  | .wh n b k, st, E => whEv (fun s => b.ty cE bE G s) (fun s => b.ev c m0 s) (fun s => k.ev c m0 s) n st E

/-! ## Traces -/

/-- The value of register `r` from `σ`. -/
def σv (c : Ctx) (sp : Word) (σ : List (Reg × SV)) (r : Reg) : Word :=
  match σ.lookup r with
  | some v => v.val c sp
  | none => 0

/-- A public value of a call from the context, the views `Γ` and the registers `σ`. -/
def pubV (c : Ctx) (sp : Word) (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) : PubW → Word
  | .r r => σv c sp σ r
  | .n r => ((ctxAt Γ σ r).map fun n => BitVec.ofNat 32 (slen c sp n)).getD 0

variable (T : A → Word → (Nat → Word) → List Event)

/-- The trace of one construct at `o`, then `Ψ`. -/
def Op.tr (c : Ctx) (o : Nat) (st : St) : Op A Bk → TrP → TrP
  | .call a as, Ψ =>
    let g := ldsEmit as
    Tr.cat (Tr.is (blockTr g (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
      (Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 (o + seqSize g), .bl (blImm (o + seqSize g) (cE a).entry), []⟩])
        (Tr.cat (Tr.is (T a c.base (pubOf ((cE a).pubs.map (pubV c (G.fsp c) st.Γ (regsOf st.Γ st.σ as))))))
          Ψ))
  | .blk b as, Ψ =>
    let g := ldsEmit as
    Tr.cat (Tr.is (blockTr g (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
      (Tr.cat (Tr.is (blockTr (bE b).g (c.base + BitVec.ofNat 32 (o + seqSize g)) (bE b).L
        ((bE b).L.map (σv c (G.fsp c) (regsOf st.Γ st.σ as))))) Ψ)
  | .spill r o', Ψ =>
    Tr.cat (Tr.is (blockTr [.strSp r (BitVec.ofNat 8 (o' / 4))] (c.base + BitVec.ofNat 32 o) [13]
      [G.fsp c])) Ψ
  | .drop _ _, Ψ => Ψ
  | .ld r (.C _ _ imm), Ψ =>
    Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 o, .ldrLit r (BitVec.ofNat 8 imm),
        [⟨.read, c.base + BitVec.ofNat 32 (litOff o (BitVec.ofNat 8 imm)), 4⟩]⟩])
      (Tr.cat (Tr.is (blockTr [.addPc r] (c.base + BitVec.ofNat 32 (o + 2)) [13] [G.fsp c])) Ψ)
  | .ld r l, Ψ => Tr.cat (Tr.is (blockTr (l.emit r) (c.base + BitVec.ofNat 32 o) [13] [G.fsp c])) Ψ
  | .pub g, Ψ => Tr.cat (Tr.is (blockTr g (c.base + BitVec.ofNat 32 o) [13] [G.fsp c])) Ψ
  | .keep _, Ψ => Ψ
  | .ldb rd rb ri, Ψ => Tr.cat (Tr.is (blockTr [ldbI rd rb ri] (c.base + BitVec.ofNat 32 o) [rb.toReg, ri.toReg]
      [σv c (G.fsp c) st.σ rb.toReg, σv c (G.fsp c) st.σ ri.toReg])) Ψ
  | .isl pad n, Ψ => Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 o,
      .b (brImm11 o (o + 2 + seqSize (islPad pad) + n)), []⟩]) Ψ

/-- The event of `b<cond> tgt` at `o`. -/
def bcEv (c : Ctx) (cond : BitVec 4) (o tgt : Nat) : Event :=
  ⟨c.base + BitVec.ofNat 32 o, .bcond cond (brImm8 o tgt), []⟩

/-- The event of `b tgt` at `o`. -/
def bEv (c : Ctx) (o tgt : Nat) : Event := ⟨c.base + BitVec.ofNat 32 o, .b (brImm11 o tgt), []⟩

/-- The trace of a loop's passes with the counter at `r`: body `bt`, the decrement `D`, the
exit test `bc`, then the exit `Ψk` or the back branch `bb` and the next pass. -/
def loopTr (bt : TrP → TrP) (D : List Event) (bc bb : Event) (Ψk : TrP) : Nat → TrP
  | 0 => Tr.is []
  | r + 1 => bt (Tr.cat (Tr.is D) (Tr.cat (Tr.is [bc]) (Tr.cond (r == 0) Ψk
      (Tr.cat (Tr.is [bb]) (loopTr bt D bc bb Ψk r)))))

/-- The trace of the passes of a loop with exits: the body's typing `tb` and trace `bt` (from a
state, with its rest and exit continuations), the rest's trace `kt`, the back branch `back`, the
enclosing exits `Ψs`. -/
def whTr (tb : St → Option St) (bt : St → TrP → List TrP → TrP) (kt : St → TrP) (back : TrP → TrP)
    (Ψs : List TrP) : Nat → St → TrP
  | 0, _ => Tr.is []
  | n + 1, st => match tb st with
    | some s => bt st (back (whTr tb bt kt back Ψs n s)) (kt { s with ex := none } :: Ψs)
    | none => Tr.is []

/-- The trace of a test's block and store at `o`, then `Ψ`. -/
def xitT (c : Ctx) (o : Nat) (st : St) (g : List Instr) : Option (LowReg × Nat) → TrP → TrP
  | none, Ψ => (Op.pub g : Op A Bk).tr cE bE G T c o st Ψ
  | some (q, o'), Ψ =>
    (Op.pub g : Op A Bk).tr cE bE G T c o st ((Op.spill q o' : Op A Bk).tr cE bE G T c (o + seqSize g) st Ψ)

/-- **The trace of a program** at `o`, then `Ψ`, with the exits `J` of the enclosing constructs and
their traces `Ψs`: a function of the public context. -/
def Prog.tr (c : Ctx) : Prog A Bk → Nat → St → TrP → List Nat → List TrP → TrP
  | .nil, _, _, Ψ, _, _ => Ψ
  | .op x k, o, st, Ψ, J, Ψs => x.tr cE bE G T c o st
      (k.tr c (o + x.size cE bE) ((x.ty cE bE G st).getD st) Ψ J Ψs)
  | .loop cnt n b k, o, st, Ψ, J, Ψs =>
    let ob := o + seqSize (loopHead cnt n)
    let od := ob + b.size cE bE
    let oe := od + seqSize (loopDec cnt)
    Tr.cat (Tr.is (blockTr (loopHead cnt n) (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
      (loopTr (fun Ψ' => b.tr c ob (loopSt st cnt) Ψ' [] [])
        (blockTr (loopDec cnt) (c.base + BitVec.ofNat 32 od) [13] [G.fsp c])
        (bcEv c EQ oe (oe + 4)) (bEv c (oe + 2) ob) (k.tr c (oe + 4) (loopOut st cnt) Ψ J Ψs) n)
  | .sel w i p₀ p₁ k, o, st, Ψ, J, Ψs =>
    let oh := o + seqSize (selHead w i)
    let o₀ := oh + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    let oo := o₁ + p₁.size cE bE + 2
    let sJ := match p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
      | some s₀, some s₁ => joinSt s₀ s₁
      | _, _ => st
    let Ψk := k.tr c oo sJ Ψ J Ψs
    let b := ((pwAt st.Γ w).map fun v => v.val c (G.fsp c) == BitVec.ofNat 32 i).getD false
    Tr.cat (Tr.is (blockTr (selHead w i) (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
      (Tr.cat (Tr.is [bcEv c NE oh o₀])
        (Tr.cond (!b) (p₀.tr c o₀ (selSt st) (Tr.cat (Tr.is [bEv c (o₁ - 2) oo]) Ψk) [] [])
          (Tr.cat (Tr.is [bEv c (oh + 2) o₁])
            (p₁.tr c o₁ (selSt st) (Tr.cat (Tr.is [bEv c (oo - 2) oo]) Ψk) [] []))))
  | .xit g s cc sh l k, o, st, Ψ, J, Ψs =>
    let ob := o + xitSz g s
    let tg := J.getD l 0
    let r := xitSt G st g s cc
    let tk := (r.map (·.2)).getD false
    let Ψk := k.tr c (ob + xbSz sh) ((r.map (·.1)).getD st) Ψ J Ψs
    let Ψl := Ψs.getD l (Tr.is [])
    let Ψb := if sh then Tr.cat (Tr.is [bcEv c cc ob tg]) (Tr.cond tk Ψl Ψk)
      else Tr.cat (Tr.is [bcEv c (cc ^^^ 1) ob (ob + 4)])
        (Tr.cond (!tk) Ψk (Tr.cat (Tr.is [bEv c (ob + 2) tg]) Ψl))
    xitT cE bE G T c o st g s Ψb
  | .hd b h k, o, st, Ψ, J, Ψs =>
    let oh := o + b.size cE bE + (if h.isNil then 0 else 2)
    let oj := oh + h.size cE bE
    match b.ty cE bE G st with
    | some s =>
      let Ψh := match h.ty cE bE G { s with ex := none } with
        | some s' => h.tr c oh { s with ex := none } (k.tr c oj s' Ψ J Ψs) J Ψs
        | none => Tr.is []
      b.tr c o st (if h.isNil then k.tr c oj s Ψ J Ψs else Tr.cat (Tr.is [bEv c (oh - 2) oj]) (k.tr c oj s Ψ J Ψs))
        (oh :: J) (Ψh :: Ψs)
    | none => Tr.is []
  | .wh n b k, o, st, Ψ, J, Ψs =>
    let oe := o + b.size cE bE + 2
    whTr (fun s => b.ty cE bE G s) (fun s Ψ' Ψs' => b.tr c o s Ψ' (oe :: J) Ψs') (fun s => k.tr c oe s Ψ J Ψs)
      (fun Ψ' => Tr.cat (Tr.is [bEv c (oe - 2) o]) Ψ') Ψs n st

end

end M0Crypto.Release.Ed25519CallProg
