import M0Crypto.Release.Ed25519CallProgStitchRun
import M0Crypto.Release.Ed25519CallProgLin
import M0Crypto.Release.Ed25519CallProgGood

/-!
# Public glue that writes frame words, at a stitched site

Between straight lines that `prog_run` runs, a routine's own public block may write frame words
(digits, counters, pointers) and leave views there. `wglue_run` runs such a block `gs`, whose
footprints are expressions of its entry state (`sglueOk`) and whose trace is a function of the
atoms `As` (`traceOkE`): its writes lie in the frame regions `ws`, and the views `outs` hold
after it with values `vs`. The continuation receives the block's final state with the views
`outs` joined to those `ws` leaves and the registers `σ` it shows (`glueSt`). `br_run` is the
branch `b<!cc> +0; b T` after such a block, keeping the static state. `at_weak` forgets views,
registers and written regions, so that the states of several paths meet.
-/

namespace M0Crypto.Release.Ed25519GlueRun

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Sym (SExpr)

variable (Rs : Rels)

section run
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (m0 : Mem)

/-- **Weakening**: fewer views, registers and block outputs, more written regions. -/
theorem at_weak {o : Nat} {st st' : St} {E : Loc → V} {t : State} (h : At Rs B c G m0 o st E t)
    (hΓ : ∀ p ∈ st'.Γ, p ∈ st.Γ) (hX : ∀ r ∈ st.X, r ∈ st'.X) (hσ : ∀ p ∈ st'.σ, p ∈ st.σ)
    (hρ : ∀ r ∈ st'.ρ, r ∈ st.ρ) : At Rs B c G m0 o st' E t := by
  obtain ⟨hpc, h13, hc, hs, hi, hr⟩ := h
  exact ⟨hpc, h13, hc, fun p hp => hs p (hσ p hp),
    ⟨fun p hp => hi.1 p (hΓ p hp), fun y hy hx => hi.2.1 y hy fun r hr => hx r (hX r hr), hi.2.2⟩,
    fun r h => hr r (hρ r h)⟩

/-- The state after a glue block: the views `outs` joined to those the writes `ws` leave, and
the registers `σ`. -/
def glueSt (st : St) (ws : List SR) (outs : List (Loc × Kd)) (σ : List (Reg × SV)) : St :=
  { Γ := outs ++ keepViews st.Γ ws outs, σ, X := st.X ++ ws.filter (·.loc.isEx), ρ := [] }

/-- **Public glue with writes**: the block `gs` at `o`, its accesses aligned (`al`), its reads in
the caller's read footprint, its writes in the frame regions `ws`, after which the views `outs`
hold with values `vs`, and the registers `σ` hold. Its trace is `blockTrE` at the atoms `As`. -/
theorem wglue_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {gs : List Instr} {al wg rg : List (SExpr × Nat)} {As : List SExpr} {o : Nat} {st : St} {E : Loc → V}
    {t : State} {Q : State → Prop} {Ψ : TrP} {rest : List Piece} {ws : List SR} {outs : List (Loc × Kd)}
    {vs : List V} {σ : List (Reg × SV)} (hok : sglueOk G.cs gs o G.top G.N al wg rg = true) (htr : traceOkE gs As = true)
    (hp : piecesAt B o (.seq gs :: rest) = true) (hat : At Rs B c G m0 o st E t)
    (hal : ∀ r ∈ al, (r.1.denote t).toNat % r.2 = 0) (hrd : Sub (sregions t rg) Rc)
    (hws : ∀ w ∈ ws, w.ok G = true ∧ w.acc G true = true) (hwr : Sub (sregions t wg) (ws.flatMap (SR.rgns G c)))
    (ho : ∀ p ∈ outs, (Kd.sr p.1 p.2).ok G = true) (hnd : (outs.map (·.1)).Nodup)
    (hv : All2 (fun p v => Rel Rs c (G.fsp c) p.2 (execAll gs t).mem (p.1.addr c (G.fsp c)) v) outs vs)
    (hσ : (execAll gs t).regs 13 = G.fsp c → Holds c (G.fsp c) σ (execAll gs t).regs)
    (k : At Rs B c G m0 (o + seqSize gs) (glueSt st ws outs σ) (updOuts E outs vs) (execAll gs t) →
      piecesAt B (o + seqSize gs) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) (execAll gs t) Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (Tr.cat (Tr.is (blockTrE gs (c.base + BitVec.ofNat 32 o) As (As.map (·.denote t)))) Ψ) := by
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
  have hfa : gs.all Instr.falls = true := by
    simp only [sglueOk, Bool.and_eq_true] at hok; exact hok.1.1.1.1.1.1.2
  have hW : Sub (ws.flatMap (SR.rgns G c)) Wc := sub_flatMap fun w hw => by
    have := g.sub (hws w hw).1 true (hws w hw).2; simpa using this
  refine ReachFT.sglue F gs al wg rg hp1 hpc h13 hcode ⟨hal, sub_trans hwr hW, hrd⟩
    (traceAll_blockTrE hfa htr hpc rfl) (fun hpc1 h131 hc1 hm1 => k ?_ hp2) hok
  have hm : MemEq (⟨G.fsp c - BitVec.ofNat 32 0, 0⟩ :: ws.flatMap (SR.rgns G c)) t.mem (execAll gs t).mem :=
    fun y hy => hm1 y fun h => hy (Has.tail (hwr.has h))
  exact ⟨hpc1, h131, hc1, hσ h131,
    inv_after Rs g hi (by have := g.top; omega) (fun w hw => (hws w hw).1) hm σsp [] ho hnd hv,
    fun _ h => absurd h List.not_mem_nil⟩

/-- **A branch `b<!cc> +0; b T`** at `ob`: on decision `d` (the exit condition `cc` fails) the
run continues after it, else at `T`; the static state stays. -/
theorem br_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) {cc : BitVec 4} {ob T : Nat} {st : St}
    {E : Loc → V} {u : State} {Q : State → Prop} {Ψk Ψx : TrP} {d : Bool} {rest : List Piece}
    (hcc : cc.toNat < 14) (hbr : brOk (B := B) G false ob T = true)
    (hp : piecesAt B ob (xitBr cc false ob T ++ rest) = true) (hat : At Rs B c G m0 ob st E u)
    (hd : condPassed cc u = !d)
    (kS : d = true → At Rs B c G m0 (ob + 4) st E (u.setReg 15 (c.base + BitVec.ofNat 32 (ob + 4))) →
      piecesAt B (ob + 4) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N)
        (u.setReg 15 (c.base + BitVec.ofNat 32 (ob + 4))) Q Ψk)
    (kX : d = false → At Rs B c G m0 T st E (u.setReg 15 (c.base + BitVec.ofNat 32 T)) →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N)
        (u.setReg 15 (c.base + BitVec.ofNat 32 T)) Q Ψx) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q
      (Tr.cat (Tr.is [bcEv c (cc ^^^ 1) ob (ob + 4)]) (Tr.cond d Ψk (Tr.cat (Tr.is [bEv c (ob + 2) T]) Ψx))) := by
  have hpc1 := hat.1; have h131 := hat.2.1
  have htN : G.top ≤ G.N := g.top
  have hneg : condPassed (cc ^^^ 1) u = d := by
    rw [condPassed_fl, condFl_xor1 cc hcc, ← condPassed_fl, hd, Bool.not_not]
  simp only [brOk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hbr
  simp only [xitBr, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at hp
  obtain ⟨hpi, hpr⟩ := piecesAt_cons hp
  obtain ⟨hpj, hpk⟩ := piecesAt_cons hpr
  simp only [Piece.instrs, Piece.size_bcond, Piece.size_b] at hpi hpj hpk
  refine bc_run F hbr.1 hpi hpc1 h131 htN hneg (fun ht => ?_) (fun hf => ?_)
  · rw [hneg] at ht; subst ht
    exact kS rfl (at_br Rs m0 hat) (by simpa [Nat.add_assoc] using hpk)
  · rw [hneg] at hf; subst hf
    refine b_run F hbr.2 hpj (by simp [State.pc, State.setReg]) (by simpa [State.setReg, Geo.fsp] using h131) htN ?_
    have e : (u.setReg 15 (c.base + BitVec.ofNat 32 (ob + 2))).setReg 15 (c.base + BitVec.ofNat 32 T) =
        u.setReg 15 (c.base + BitVec.ofNat 32 T) := by
      simp only [State.setReg]; congr 1; funext i; split <;> rfl
    rw [e]; exact kX rfl (at_br Rs m0 hat)

/-- **A jump `b T`** at `o`, keeping the static state. -/
theorem jmp_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) {o T : Nat} {st : St} {E : Loc → V}
    {u : State} {Q : State → Prop} {Ψ : TrP} {rest : List Piece} (hok : bOk (B := B) G.cs o T = true)
    (hp : piecesAt B o (.b T :: rest) = true) (hat : At Rs B c G m0 o st E u)
    (k : At Rs B c G m0 T st E (u.setReg 15 (c.base + BitVec.ofNat 32 T)) →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N)
        (u.setReg 15 (c.base + BitVec.ofNat 32 T)) Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q
      (Tr.cat (Tr.is [bEv c o T]) Ψ) := by
  obtain ⟨hpj, -⟩ := piecesAt_cons hp
  simp only [Piece.instrs] at hpj
  exact b_run F hok hpj hat.1 (by simpa [Geo.fsp] using hat.2.1) g.top (k (at_br Rs m0 hat))

end run

/-! ## Values off the glue's words

Glue blocks set views at frame words `N` between straight lines. When no update of `L` reads a
word of `N`, values that agree off `N` stay so through `L` (`run_agree`). -/

section agree
variable {A Bk : Type} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V}
  {c : Ctx} {m0 : Mem}

/-- `E` and `E'` agree off the locations `N`. -/
def Agree (N : List Loc) (E E' : Loc → V) : Prop := ∀ l, l ∉ N → E l = E' l

/-- A source reads no location of `N`. -/
def srcOff (N : List Loc) : Src → Bool
  | .view l => !N.contains l
  | .slice l _ _ => !N.contains l
  | _ => true

/-- An update reads no location of `N`. -/
def opOff (N : List Loc) : ROp A Bk → Bool
  | .call _ _ s => s.all (srcOff N)
  | .blk _ _ s => s.all (srcOff N)
  | .ldb _ s => srcOff N s

theorem Agree.trans {N : List Loc} {E E' E'' : Loc → V} (h : Agree N E E') (h' : Agree N E' E'') : Agree N E E'' :=
  fun l hl => (h l hl).trans (h' l hl)

/-- Setting views at locations of `N` keeps agreement off `N`. -/
theorem agree_upd {N : List Loc} {E : Loc → V} :
    ∀ (o : List (Loc × Kd)) (vs : List V), (∀ p ∈ o, p.1 ∈ N) → Agree N (updOuts E o vs) E
  | [], _, _ => fun _ _ => rfl
  | _ :: _, [], _ => fun _ _ => rfl
  | (l, k) :: o, v :: vs, h => fun x hx => by
    have hl : x ≠ l := fun he => hx (he ▸ h (l, k) (List.mem_cons_self ..))
    simp only [updOuts, hl, ↓reduceIte]
    exact agree_upd o vs (fun p hp => h p (List.mem_cons_of_mem _ hp)) x hx

theorem src_agree {N : List Loc} {E E' : Loc → V} (h : Agree N E E') {s : Src} (hs : srcOff N s = true) :
    Src.val G c m0 E s = Src.val G c m0 E' s := by
  cases s <;> simp only [srcOff] at hs <;> simp only [Src.val]
  · exact h _ (by simpa using hs)
  · rw [h _ (by simpa using hs)]

theorem upd_agree {N : List Loc} {E E' : Loc → V} (h : Agree N E E') :
    ∀ (o : List (Loc × Kd)) (vs : List V), Agree N (updOuts E o vs) (updOuts E' o vs)
  | [], _ => h
  | _ :: _, [] => h
  | (l, _) :: o, v :: vs => fun x hx => by
    simp only [updOuts]; split
    · rfl
    · exact upd_agree h o vs x hx

theorem setRg_agree {N : List Loc} {E E' : Loc → V} (h : Agree N E E') (ro : List Reg) (ws : List V) :
    Agree N (setRg E ro ws) (setRg E' ro ws) := fun l hl => by
  cases l with
  | rg q => simp only [setRg]; split
            · rfl
            · exact h _ hl
  | _ => exact h _ hl

/-- **Updates that read no location of `N`** keep agreement off `N`. -/
theorem run_agree {N : List Loc} : ∀ (L : List (ROp A Bk)) {E E' : Loc → V}, Agree N E E' →
    (∀ r ∈ L, opOff N r = true) →
    Agree N (runR bE G semA semB c m0 L E) (runR bE G semA semB c m0 L E')
  | [], _, _, h, _ => h
  | r :: L, E, E', h, hL => by
    refine run_agree L ?_ fun r' hr => hL r' (List.mem_cons_of_mem _ hr)
    have hr := hL r (List.mem_cons_self ..)
    have hs : ∀ s : List Src, s.all (srcOff N) = true →
        s.map (Src.val G c m0 E) = s.map (Src.val G c m0 E') := fun s hs =>
      List.map_congr_left fun x hx => src_agree h (List.all_eq_true.mp hs x hx)
    cases r with
    | call a o s => simp only [ROp.ev]; rw [hs s hr]; exact upd_agree h o _
    | blk b o s => simp only [ROp.ev]; rw [hs s hr]; exact setRg_agree (upd_agree h o _) _ _
    | ldb r s => simp only [ROp.ev]; rw [src_agree h hr]; exact setRg_agree h _ _

end agree

/-! ## Values up to `p`

`VR` relates field values equal modulo `p` and other values that are equal; `run_er` carries it
through updates whose callees keep it (`hA`, `hB`) and whose sources are views or field
elements of buffer bytes equal modulo `p` in the two runs (`SOk`). -/

section modp
open M0Crypto.Release.Field25519Congr (ModP)
variable {A Bk : Type} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V} {semB : Bk → List V → List V}
  {c c' : Ctx} {m0 m0' : Mem}

/-- Field values equal modulo `p`; other values equal. -/
def VR : V → V → Prop
  | .f x, .f y => ModP x y
  | a, b => a = b

theorem VR.refl : ∀ v : V, VR v v
  | .f x => ModP.refl x
  | .b _ | .c _ | .p _ | .w _ | .none => Eq.refl _

theorem VR.cases : ∀ {a b : V}, VR a b → (∃ x y, a = .f x ∧ b = .f y ∧ ModP x y) ∨ a = b
  | .f _, .f _, h => .inl ⟨_, _, rfl, rfl, h⟩
  | .f _, .b _, h | .f _, .c _, h | .f _, .p _, h | .f _, .w _, h | .f _, .none, h => .inr h
  | .b _, _, h | .c _, _, h | .p _, _, h | .w _, _, h | .none, _, h => .inr h

/-- `E` and `E'` related by `VR` everywhere. -/
def ER (E E' : Loc → V) : Prop := ∀ l, VR (E l) (E' l)

theorem all2_rfl : ∀ l : List V, All2 VR l l
  | [] => trivial
  | v :: l => ⟨VR.refl v, all2_rfl l⟩

theorem all2_get : ∀ {l l' : List V}, All2 VR l l' → ∀ i : Nat, VR (l[i]?.getD .none) (l'[i]?.getD .none)
  | [], [], _, _ => VR.refl _
  | _ :: _, _ :: _, ⟨h, _⟩, 0 => h
  | _ :: _, _ :: _, ⟨_, h⟩, i + 1 => all2_get h i

theorem all2_take : ∀ {l l' : List V}, All2 VR l l' → ∀ n, All2 VR (l.take n) (l'.take n)
  | [], [], _, _ => by rw [List.take_nil]; trivial
  | _ :: _, _ :: _, _, 0 => trivial
  | _ :: _, _ :: _, ⟨h, t⟩, n + 1 => ⟨h, all2_take t n⟩

theorem all2_drop : ∀ {l l' : List V}, All2 VR l l' → ∀ n, All2 VR (l.drop n) (l'.drop n)
  | [], [], _, _ => by rw [List.drop_nil]; trivial
  | _ :: _, _ :: _, h, 0 => h
  | _ :: _, _ :: _, ⟨_, t⟩, n + 1 => all2_drop t n

theorem upd_er {E E' : Loc → V} (h : ER E E') :
    ∀ (o : List (Loc × Kd)) {vs vs' : List V}, All2 VR vs vs' → ER (updOuts E o vs) (updOuts E' o vs')
  | [], _, _, _ => h
  | _ :: _, [], [], _ => h
  | (l, _) :: o, _ :: _, _ :: _, ⟨hv, hr⟩ => fun x => by
    simp only [updOuts]; split
    · exact hv
    · exact upd_er h o hr x

theorem setRg_er {E E' : Loc → V} (h : ER E E') (ro : List Reg) {ws ws' : List V} (hw : All2 VR ws ws') :
    ER (setRg E ro ws) (setRg E' ro ws') := fun l => by
  cases l with
  | rg q => simp only [setRg]; split
            · exact all2_get hw _
            · exact h _
  | _ => exact h _

/-- A source that both runs read alike up to `p`: a view, or a buffer's field element. -/
def SOk (G : Geo) (c : Ctx) (m0 : Mem) (c' : Ctx) (m0' : Mem) : Src → Prop
  | .view _ => True
  | .extF r => ModP (Field25519Routines.feVal m0 (r.loc.addr c (G.fsp c)))
      (Field25519Routines.feVal m0' (r.loc.addr c' (G.fsp c')))
  | _ => False

theorem src_er {E E' : Loc → V} (h : ER E E') :
    ∀ s : Src, SOk G c m0 c' m0' s → VR (Src.val G c m0 E s) (Src.val G c' m0' E' s)
  | .view l, _ => h l
  | .extF _, hs => hs

theorem srcs_er {E E' : Loc → V} (h : ER E E') :
    ∀ s : List Src, (∀ x ∈ s, SOk G c m0 c' m0' x) → All2 VR (s.map (Src.val G c m0 E)) (s.map (Src.val G c' m0' E'))
  | [], _ => trivial
  | x :: s, hs => ⟨src_er h x (hs x (List.mem_cons_self ..)), srcs_er h s fun y hy => hs y (List.mem_cons_of_mem _ hy)⟩

theorem byteW_er {a b : V} (h : VR a b) : VR (byteW a) (byteW b) := by
  rcases h.cases with ⟨_, _, rfl, rfl, -⟩ | rfl
  · exact Eq.refl _
  · exact VR.refl _

/-- The sources of an update. -/
def srcsOf : ROp A Bk → List Src
  | .call _ _ s => s
  | .blk _ _ s => s
  | .ldb _ s => [s]

/-- **Updates keep values up to `p`**, when their callees and blocks do and their sources are read
alike up to `p`. -/
theorem run_er (hA : ∀ a {vs vs'}, All2 VR vs vs' → All2 VR (semA a vs) (semA a vs'))
    (hB : ∀ b {vs vs'}, All2 VR vs vs' → All2 VR (semB b vs) (semB b vs')) :
    ∀ (L : List (ROp A Bk)) {E E' : Loc → V}, ER E E' → (∀ r ∈ L, ∀ s ∈ srcsOf r, SOk G c m0 c' m0' s) →
      ER (runR bE G semA semB c m0 L E) (runR bE G semA semB c' m0' L E')
  | [], _, _, h, _ => h
  | r :: L, E, E', h, hL => by
    refine run_er hA hB L ?_ fun r' hr => hL r' (List.mem_cons_of_mem _ hr)
    have hs := srcs_er (G := G) (c := c) (m0 := m0) (c' := c') (m0' := m0') h (srcsOf r) (hL r (List.mem_cons_self ..))
    cases r with
    | call a o s => exact upd_er h o (hA a hs)
    | blk b o s =>
      have hw := hB b hs
      exact setRg_er (upd_er h o (all2_take hw _)) _ (all2_drop hw _)
    | ldb q s => exact setRg_er h [q] ⟨byteW_er hs.1, trivial⟩

end modp

/-! ## Glue that reads buffers: the body's invariant

`pubBlk_gp` keeps the body's invariant over a block that reads frame words. A routine's own glue
may also read its buffers (digits, an input) and code words. `bufBlk_gp` keeps the invariant over
a decided block valued by its atoms (`blockTrE`) whose reads are written bytes of views, bytes of
readable buffers or code (`BufRd`), whose accesses lie in the frame, in a resolved region or in
code (`BufAc`), and whose writes cover the views it adds. `bufEv_gp` is the same for one event
that adds no view, such as a code literal's load. -/

section bufGlue
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The bytes a buffer-reading glue block may read at static state `st`: the written bytes of a
view, the bytes of a readable buffer, or code. -/
def BufRd (c : Ctx) (G : Geo) (st : St) (y : Word) : Prop :=
  Ext c (G.fsp c) st.Γ y ∨
    (∃ r : SR, r.ok G = true ∧ r.loc.isEx = true ∧ r.acc G false = true ∧ Has (r.rgns G c) y) ∨
    Has [@codeR B BS _ c.base] y

/-- The bytes a buffer-reading glue block may access: the frame, a resolved region, or code. -/
def BufAc (c : Ctx) (G : Geo) (y : Word) : Prop :=
  Region (G.fsp c) G.top y ∨ (∃ r : SR, r.ok G = true ∧ Has (r.rgns G c) y) ∨ Has [@codeR B BS _ c.base] y

/-! ### Decided frame regions

A glue block whose atom `0` is SP at the frame's: its SP regions are decided against the views
(`frChk`), so that only its other regions (buffers, code) are left to `glue_gp`'s hypotheses. -/

/-- A region at atom `0` of `As`: its offset and width. -/
def spOf (As : List SExpr) (r : SExpr × Nat) : Option (Nat × Nat) :=
  match atomOf As r.1 with
  | some (0, d) => some (d.toNat, r.2)
  | _ => none

/-- Not a context view, whose written bytes are its size. -/
def kdNc : Kd → Bool
  | .ctx _ => false
  | _ => true

/-- The frame bytes `[o, o + w)` lie in a view of `Γ`. -/
def frIn (Γ : List (Loc × Kd)) (o w : Nat) : Bool :=
  Γ.any fun p => match p.1 with
    | .fr a => kdNc p.2 && decide (a ≤ o ∧ o + w ≤ a + p.2.sz)
    | _ => false

/-- **The decided frame regions** of a block at atoms `As`: its SP reads in views of `Γ`, its SP
accesses in the frame of `top` bytes, and each view of `Γ'` in `Γ` or a frame view covered by an
SP region of `wo`. -/
def frChk (top : Nat) (Γ Γ' : List (Loc × Kd)) (As : List SExpr) (ini wo fp : List (SExpr × Nat)) : Bool :=
  ini.all (fun r => (spOf As r).all fun x => frIn Γ x.1 x.2) &&
  fp.all (fun r => (spOf As r).all fun x => decide (x.1 + x.2 ≤ top)) &&
  Γ'.all fun p => Γ.contains p || match p.1 with
    | .fr a => kdNc p.2 && wo.any fun r => (spOf As r).any fun x => decide (x.1 ≤ a ∧ a + p.2.sz ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ top)
    | _ => false

theorem nc_ini {k : Kd} (h : kdNc k = true) (c : Ctx) (sp : Word) : Kd.ini c sp k = k.sz := by
  cases k <;> first | rfl | simp [kdNc] at h

theorem spOf_some {pc s : Word} {As : List SExpr} {vs : List Word} {r : SExpr × Nat} {x : Nat × Nat}
    (hl : vs.length = As.length) (hv : vs[0]? = some s) (h : spOf As r = some x) :
    ∃ d : Word, d.toNat = x.1 ∧ x.2 = r.2 ∧ addrE pc As vs r.1 = s + d := by
  unfold spOf at h
  split at h
  · next d hd =>
    obtain ⟨v, hv', he⟩ := addrE_atom (pc := pc) hl hd
    rw [hv] at hv'; cases hv'; cases h
    exact ⟨d, rfl, rfl, he⟩
  · cases h

theorem rgn_in {s d y : Word} {w a m : Nat} (ha : a ≤ d.toNat) (hm : d.toNat + w ≤ a + m)
    (hy : Region (s + d) w y) : Region (s + BitVec.ofNat 32 a) m y := by
  simp only [Region] at *; bv_omega

theorem rgn_self {a : Word} {o w : Nat} (h : o < w) : Region a w (a + BitVec.ofNat 32 o) := by
  simp only [Region]; bv_omega

theorem rgn_off {s d y : Word} {w a m : Nat} (ha : d.toNat ≤ a) (hm : a + m ≤ d.toNat + w)
    (hw : d.toNat + w < 2 ^ 32) (hy : Region (s + BitVec.ofNat 32 a) m y) :
    ∃ o < w, y = s + d + BitVec.ofNat 32 o := by
  simp only [Region] at hy
  refine ⟨(y - (s + d)).toNat, by bv_omega, ?_⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

theorem inRD_one {den : SExpr → Word} {rs : List (SExpr × Nat)} {y : Word} (h : InRD den rs y) :
    ∃ r ∈ rs, InRD den [r] y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  exact ⟨r, hr, r, List.mem_singleton_self _, o, ho, rfl⟩


variable {c : Ctx} {G : Geo} {sp0 : Word} {n : Nat} {X0 : Word → Prop} (fm : Frm c G sp0 n X0)
  (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (G.fsp c) y ∧ X0 y)
include fm hcode

theorem bufAc_above {y : Word} (h : BufAc (B := B) c G y) (hb : BelowEntry sp0 n y) :
    AtOrAboveSp sp0 (G.fsp c) y := by
  rcases h with h | ⟨r, ho, h⟩ | h
  · exact fm.fr_above (o := 0) (m := G.top) (by omega) (by rw [BitVec.add_zero]; exact h)
  · exact (fm.sr_above ho h hb).1
  · exact (hcode y h hb).1

theorem bufRd_ext {st : St} {y : Word} (h : BufRd (B := B) c G st y) (hb : BelowEntry sp0 n y) :
    Ext c (G.fsp c) st.Γ y ∨ X0 y := by
  rcases h with h | ⟨r, ho, hx, ha, h⟩ | h
  · exact .inl h
  · exact .inr ((fm.sr_above ho h hb).2 hx ha)
  · exact .inr (hcode y h hb).2

/-- **A buffer-reading glue block** keeps the body's invariant: from `st` to `st'`, whose views'
bytes are those of `st` or written by the block. -/
theorem bufBlk_gp {st st' : St} {g : List Instr} {ini wo fp : List (SExpr × Nat)}
    (hk : blkChk ini wo fp g = true) {pc : Word} {As : List SExpr} {vs : List Word}
    (hI : ∀ y, InRD (addrE pc As vs) ini y → BufRd (B := B) c G st y)
    (hA : ∀ y, InRD (addrE pc As vs) fp y → BufAc (B := B) c G y)
    (hΓ : ∀ y, Ext c (G.fsp c) st'.Γ y → Ext c (G.fsp c) st.Γ y ∨ InRD (addrE pc As vs) wo y) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTrE g pc As vs)) (BI c G sp0 n X0 st') :=
  bi_seg (blkE_seg hk (X := InRD (addrE pc As vs) ini) (fun _ h => h)
      fun y hy hb => bufAc_above fm hcode (hA y hy) hb)
    (fun y hy hb => bufRd_ext fm hcode (hI y hy) hb) fun y hy _ => (hΓ y hy).elim .inl (.inr ∘ .inr)

/-- **One buffer-reading event** that keeps SP keeps the body's invariant at `st`. -/
theorem bufEv_gp {st : St} {e : Event} (hx : spExact e.instr = true) (hs : spAfter e.instr (G.fsp c) = G.fsp c)
    (hR : ∀ y, Reads e.accesses y → BufRd (B := B) c G st y)
    (hA : ∀ y, Reads e.accesses y ∨ Writes e.accesses y → BufAc (B := B) c G y) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is [e]) (BI c G sp0 n X0 st) :=
  bi_seg (ev_seg (X := BufRd (B := B) c G st) hx hs (fun y hy hb => bufAc_above fm hcode (hA y hy) hb)
      fun y hy _ => hR y hy)
    (fun _ hy hb => bufRd_ext fm hcode hy hb) fun _ hy _ => .inl hy

/-- **A decided glue block** at atoms `As` whose atom `0` is SP at the frame's: its SP regions by
`frChk`, its other reads and accesses by `hB` and `hBA`. -/
theorem glue_gp {st st' : St} {g : List Instr} {ini wo fp : List (SExpr × Nat)}
    (hk : blkChk ini wo fp g = true) {pc : Word} {As : List SExpr} {vs : List Word}
    (hl : vs.length = As.length) (hv : vs[0]? = some (G.fsp c))
    (hf : frChk G.top st.Γ st'.Γ As ini wo fp = true)
    (hB : ∀ r ∈ ini, spOf As r = none → ∀ y, InRD (addrE pc As vs) [r] y → BufRd (B := B) c G st y)
    (hBA : ∀ r ∈ fp, spOf As r = none → ∀ y, InRD (addrE pc As vs) [r] y → BufAc (B := B) c G y) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTrE g pc As vs)) (BI c G sp0 n X0 st') := by
  simp only [frChk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hf
  obtain ⟨⟨hi, ha⟩, hg⟩ := hf
  have := fm.top; have := fm.n32; have := fm.room
  refine bufBlk_gp fm hcode hk (fun y hy => ?_) (fun y hy => ?_) fun y ⟨p, hp, hy⟩ => ?_
  · obtain ⟨r, hr, hy⟩ := inRD_one hy
    cases hs : spOf As r with
    | none => exact hB r hr hs y hy
    | some x =>
      have h1 := hi r hr
      rw [hs, Option.all_some] at h1
      obtain ⟨d, hd, hx, he⟩ := spOf_some (pc := pc) hl hv hs
      obtain ⟨_, hr', o, ho, rfl⟩ := hy
      rw [List.mem_singleton] at hr'; subst hr'
      obtain ⟨⟨l, k⟩, hq, hm⟩ := List.any_eq_true.mp h1
      cases l with
      | fr a =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        refine .inl ⟨(.fr a, k), hq, ?_⟩
        show Region (G.fsp c + BitVec.ofNat 32 a) (Kd.ini c (G.fsp c) k) _
        rw [nc_ini hm.1, he]
        exact rgn_in (d := d) (w := x.2) (by omega) (by omega) (rgn_self (a := G.fsp c + d) (o := o) (by omega))
      | _ => simp at hm
  · obtain ⟨r, hr, hy⟩ := inRD_one hy
    cases hs : spOf As r with
    | none => exact hBA r hr hs y hy
    | some x =>
      have h1 := ha r hr
      rw [hs, Option.all_some, decide_eq_true_eq] at h1
      obtain ⟨d, hd, hx, he⟩ := spOf_some (pc := pc) hl hv hs
      obtain ⟨_, hr', o, ho, rfl⟩ := hy
      rw [List.mem_singleton] at hr'; subst hr'
      refine .inl ?_
      rw [he]
      have := rgn_in (a := 0) (m := G.top) (d := d) (w := x.2) (Nat.zero_le _) (by omega) (rgn_self (a := G.fsp c + d) (o := o) (by omega))
      rwa [BitVec.add_zero] at this
  · rcases hg p hp with h | h
    · exact .inl ⟨p, List.contains_iff_mem.mp h, hy⟩
    obtain ⟨l, k⟩ := p
    cases l with
    | fr a =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨hn, h⟩ := h
      obtain ⟨r, hr, hx⟩ := List.any_eq_true.mp h
      cases hs : spOf As r with
      | none => simp [hs] at hx
      | some x =>
        rw [hs, Option.any_some, decide_eq_true_eq] at hx
        obtain ⟨d, hd, hx2, he⟩ := spOf_some (pc := pc) hl hv hs
        change Region (G.fsp c + BitVec.ofNat 32 a) (Kd.ini c (G.fsp c) k) y at hy
        rw [nc_ini hn] at hy
        obtain ⟨o, ho, rfl⟩ := rgn_off (d := d) (w := x.2) (by omega) (by omega) (by omega) hy
        exact .inr ⟨r, hr, o, by omega, by rw [he]⟩
    | _ => simp at h

end bufGlue

end M0Crypto.Release.Ed25519GlueRun
