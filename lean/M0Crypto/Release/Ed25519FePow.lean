import M0Crypto.Release.Ed25519CallProgCallee
import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.Ed25519CallProgBytes
import M0Crypto.Release.Ed25519FeCanon
import M0Crypto.Release.Ed25519FeMulSqr
import M0Crypto.Release.Ed25519WordLoop

/-!
# `m0c_fe_pow` as a callee call program

`m0c_fe_pow(r0 = dst, r1 = src)` copies `src` to its frame, runs the generator's
`POW58` chain, and copies the `(p - 5) / 8` power to `dst`. Its adapter uses the
decided checks of both builds and relates the program's values to exponents
of the input.
-/

namespace M0Crypto.Release.Ed25519FePow

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519Words (wsum)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Ed25519FeCanon (feVal_congr)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Field25519Congr
open M0Crypto.Artifacts.Ed25519Compact (fe_pow fe_sqr fe_mul copy)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519Routines (fieldR)
open M0Crypto.Release.Field25519Routines (mulFrame)
open M0Crypto.Release.Ed25519FeMulSqr (fpX iniX woX)
open M0Crypto.Release.StackEffect (inR_one InR)
open M0Crypto.Thumb (Event)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-! ## The callees -/

inductive PA where
  | copyIn | copyOut | sqr | mul
  deriving DecidableEq

/-- `copy(r0, r1, 8 words)` to a view of kind `k`. -/
def ioCopy (i : In) (k : Kd := .fe) : Iface :=
  { ins := [(1, 0, i)], outs := [(0, 0, k)], wr := [⟨0, 0, .k 32⟩], rd := [⟨1, 0, .k 32⟩], al := [0, 1],
    eqd := [(0, 1, 32)], kreq := [(2, 8)] }

def ioSqr : Iface :=
  { ins := [(1, 0, .view .fe)], outs := [(0, 0, .fe)], wr := [⟨0, 0, .k 32⟩], rd := [⟨1, 0, .k 32⟩], al := [0, 1],
    eqd := [(0, 1, 32)] }

def ioMul : Iface :=
  { ins := [(1, 0, .view .fe), (2, 0, .view .fe)], outs := [(0, 0, .fe)], wr := [⟨0, 0, .k 32⟩],
    rd := [⟨1, 0, .k 32⟩, ⟨2, 0, .k 32⟩], al := [0, 1, 2], eqd := [(0, 1, 32), (0, 2, 32)] }

def paS : PA → CalleeS
  | .copyIn => calleeAt copy (ioCopy (.raw (.k 32))) [0, 1, 2]
  | .copyOut => calleeAt copy (ioCopy (.view .fe)) [0, 1, 2]
  | .sqr => calleeAt fe_sqr ioSqr [0, 1]
  | .mul => calleeAt fe_mul ioMul [0, 1, 2]

/-! ## The program -/

/-- The loop counter and saved destination follow six field elements. -/
abbrev oCnt : Nat := 192
abbrev oDst : Nat := 196
abbrev topP : Nat := 200

section
open Op Ld

def sq (d a : Nat) : Op PA Empty := call .sqr [(0, S d), (1, S a)]

/-- A step of `POW58`: `d ← a ^ (2 ^ n)` by one squaring and a counted loop of `n - 1`, or
`d ← a · b`. -/
inductive PS where
  | sqr (d a n : Nat)
  | mul (d a b : Nat)

def PS.prog : PS → Prog PA Empty → Prog PA Empty
  | .sqr d a n, k => .op (sq d a) (if n = 1 then k else .loop oCnt (n - 1) (.op (sq d d) .nil) k)
  | .mul d a b, k => .op (call .mul [(0, S d), (1, S a), (2, S b)]) k

def chain (l : List PS) (k : Prog PA Empty) : Prog PA Empty := l.foldr PS.prog k

/-- The chain prefix to `z ^ (2 ^ 250 - 1)` in slot 64, with `z` in slot 0 and `z ^ 11` in slot 32. -/
def head : List PS :=
  [.sqr 32 0 1, .sqr 64 32 2, .mul 64 0 64, .mul 32 32 64, .sqr 96 32 1, .mul 64 64 96, .sqr 96 64 5,
   .mul 64 96 64, .sqr 96 64 10, .mul 96 96 64, .sqr 128 96 20, .mul 96 128 96, .sqr 96 96 10,
   .mul 64 96 64, .sqr 96 64 50, .mul 96 96 64, .sqr 128 96 100, .mul 96 128 96, .sqr 96 96 50,
   .mul 64 96 64]

/-- After saving the destination and copying the source to slot 0. -/
def rest : Prog PA Empty :=
  chain (head ++ [.sqr 64 64 2, .mul 160 64 0]) <|
    .op (call .copyOut [(0, W oDst 0), (1, S 160), (2, K 8)]) .nil

def cIn : Op PA Empty := call .copyIn [(0, S 0), (2, K 8)]

def powP : Prog PA Empty := .op (spill 0 oDst) <| .op cIn rest

end

/-- The exponents of the two kinds: the inverse and the `(p - 5) / 8` power. -/
def powE : Fin 2 → Nat
  | 0 => 2 ^ 255 - 21
  | 1 => 2 ^ 252 - 3

def ioPow : Iface :=
  { ins := [(1, 0, .view .fe)], outs := [(0, 0, .fe)], wr := [⟨0, 0, .k 32⟩],
    rd := [⟨1, 0, .k 32⟩], al := [0, 1] }

def powQ : CalleeP PA Empty :=
  ⟨calleeAt fe_pow ioPow [0, 1], powP, topP, [(0, ⟨.k 32, true, false, true⟩), (1, ⟨.k 32, false, true, true⟩)],
    [], [], []⟩

theorem pow_ok : powQ.ok paS Empty.elim = true := by decide +kernel

open M0Crypto.Thumb M0Crypto.Release.RoutinePieces in
theorem pow_code (b : Build) :
    @CalleeP.codeOk _ _ paS Empty.elim powQ b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]
  cases b <;> decide +kernel

/-! ## The value -/

/-- The callees' values. -/
def paV : PA → List V → V
  | .copyIn, [.b l] => .f (decodeInt l)
  | .copyOut, [.f x] => .f x
  | .sqr, [.f x] => .f (x * x)
  | .mul, [.f x, .f y] => .f (x * y)
  | _, _ => .none

/-- The callees on exponents of one input. -/
def expV : PA → List V → V
  | .copyOut, [.f e] => .f e
  | .sqr, [.f e] => .f ((2 * e.toNat : Nat) : Int)
  | .mul, [.f a, .f b] => .f ((a.toNat + b.toNat : Nat) : Int)
  | _, _ => .none

/-- Values against exponents of `x`: an exponent `e` stands for `x ^ e`. -/
def PowR (x : Int) (v : V) : V → Prop
  | .f e => ∃ y, v = .f y ∧ ModP y (x ^ e.toNat)
  | _ => True

theorem pa_rel (x : Int) (a : PA) (vs vs' : List V) (h : All2 (PowR x) vs vs') :
    All2 (PowR x) [paV a vs] [expV a vs'] := by
  refine ⟨?_, trivial⟩
  unfold expV; split
  · rcases vs with _ | ⟨v, _ | _⟩ <;> simp only [All2, and_false] at h
    obtain ⟨⟨y, rfl, hy⟩, -⟩ := h; exact ⟨y, rfl, hy⟩
  · rcases vs with _ | ⟨v, _ | _⟩ <;> simp only [All2, and_false] at h
    obtain ⟨⟨y, rfl, hy⟩, -⟩ := h
    exact ⟨y * y, rfl, by rw [Int.toNat_natCast, Nat.two_mul, Int.pow_add]; exact ModP.mul hy hy⟩
  · rcases vs with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> simp only [All2, and_false] at h
    obtain ⟨⟨y, rfl, hy⟩, ⟨z, rfl, hz⟩, -⟩ := h
    exact ⟨y * z, rfl, by rw [Int.toNat_natCast, Int.pow_add]; exact ModP.mul hy hz⟩
  · trivial

/-- The result: `src ^ e` for the kind's exponent. -/
def powSem (k : Fin 2) : List V → List V
  | [.f x] => [.f (x ^ powE k)]
  | _ => [.none]

/-- A closed context for the run on exponents. -/
def c₀ : Ctx := ⟨0, 0, fun _ => 0, fun _ => 0⟩

def spilled : St := (((Op.spill 0 oDst : Op PA Empty).ty paS Empty.elim powQ.geo powQ.st0)).getD powQ.st0
def copied : St := ((cIn.ty paS Empty.elim powQ.geo spilled)).getD powQ.st0

/-- The exponents after `rest`, from `1` at slot 0. -/
def expAt : V :=
  rest.ev paS Empty.elim powQ.geo (fun a vs => [expV a vs]) (fun b => b.elim) c₀ (fun _ => 0) copied
    (updOuts (fun _ => .none) [(.fr 0, .fe)] [.f 1]) (.ex 0 0)

abbrev PowFacts : Prop :=
  (Op.spill 0 oDst : Op PA Empty).ty paS Empty.elim powQ.geo powQ.st0 = some spilled ∧
  cIn.ty paS Empty.elim powQ.geo spilled = some copied ∧
  ((ioRes powQ.geo spilled (regsOf spilled.Γ spilled.σ [(0, .S 0), (2, .K 8)]) (paS .copyIn).io).map
    fun r => (r.outs, r.srcs.map Src.sr)) = some ([(.fr 0, .fe)], [some ⟨.ex 1 0, .k 32⟩]) ∧
  rest.selVs paS Empty.elim powQ.geo copied = [] ∧
  (rest.srcs paS Empty.elim powQ.geo copied).all (fun s => !s.isXF) = true ∧
  locOf powQ.σ0 0 0 = some (.ex 0 0) ∧
  (match expAt with | .f e => decide (e = powE 1) | _ => false) = true

theorem pow_facts : PowFacts := by decide +kernel

attribute [local irreducible] Prog.selVs Prog.srcs Prog.ev

theorem sum_range_wsum (f : Nat → Nat) : ∀ n, ((List.range n).map fun i => f i * 2 ^ (32 * i)).sum = wsum f n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_wsum f n]
    simp [wsum, Nat.mul_comm]

theorem decode_feVal (m : Mem) (a : Word) : (decodeInt (bytesAt m a 32) : Int) = feVal m a := by
  rw [show 32 = 4 * 8 from rfl, decodeInt_words, feVal, sum_range_wsum]

/-- **The result of `m0c_fe_pow`** from its program's: the exponents evaluate to the expected power. -/
theorem pow_post {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels} {semA : PA → List V → List V} (hA : ∀ a vs, semA a vs = [paV a vs])
    {semB : Empty → List V → List V} (c : Ctx) (sp : Word) (st : State) (m : Mem) (r0 : Word) (vs : List V)
    (hi : InsRel Rs c sp powQ.s.io st vs) (hp : powQ.post paS Empty.elim Rs semA semB st m r0) :
    OutsRel Rs c sp powQ.s.io st m (powSem 1 vs) := by
  obtain ⟨_, base, m0, -, hm, ho⟩ := hp
  obtain ⟨f1, f3, f4, f5, fx, f6, f7⟩ := pow_facts
  have z : ∀ a : Word, a + BitVec.ofNat 32 0 = a := fun a => by simp
  have hio : powQ.s.io = ioPow := rfl
  rw [hio] at hi ho ⊢
  obtain ⟨x, rfl, hx⟩ : ∃ x, vs = [.f x] ∧ ModP (feVal st.mem (st.regs 1 + BitVec.ofNat 32 0)) x := by
    rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩
    · exact hi.elim
    · cases v <;> first | exact hi.1.elim | exact ⟨_, rfl, hi.1⟩
    · exact hi.2.elim
  generalize hcc : powQ.ctx base (powQ.s.pub base st) = cc at ho hm
  dsimp only at ho
  have hp1 : cc.ptr 1 = st.regs 1 := by
    rw [← hcc, CalleeP.ctx_ptr (by simp [powQ])]; exact CalleeP.reg_pub (r := 1) (by simp [powQ, calleeAt])
  have hcin : ∀ E, cIn.ev paS Empty.elim powQ.geo semA semB cc m0 spilled E =
      updOuts E [(.fr 0, .fe)] [paV .copyIn [.b (bytesAt m0 (cc.ptr 1) 32)]] := by
    intro E
    simp only [cIn, Op.ev]
    revert f4
    cases ioRes powQ.geo spilled (regsOf spilled.Γ spilled.σ [(0, .S 0), (2, .K 8)]) (paS .copyIn).io with
    | none => intro h; cases h
    | some r =>
      intro h
      obtain ⟨srcs, outs, wrs⟩ := r
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hs⟩ := h
      rcases srcs with _ | ⟨s1, _ | _⟩ <;> simp only [List.map, List.cons.injEq, reduceCtorEq, and_false,
        List.ne_cons_self, and_true] at hs
      cases s1 <;> simp only [Src.sr, reduceCtorEq, Option.some.injEq] at hs
      subst hs
      simp only [List.map, Src.val, Loc.addr, XLen.v, z, hA]
  rw [show powQ.P = .op (.spill 0 oDst) (.op cIn rest) from rfl, Prog.ev_op f1,
    Prog.ev_op f3] at ho
  rw [hcin] at ho; simp only [Op.ev] at ho
  have hS : ∀ v ∈ rest.selVs paS Empty.elim powQ.geo copied, ∀ i,
      (v.val cc (powQ.geo.fsp cc) == BitVec.ofNat 32 i) =
        (v.val c₀ (powQ.geo.fsp c₀) == BitVec.ofNat 32 i) := by
    rw [f5]
    intro v hv
    exact False.elim (List.not_mem_nil hv)
  have hrel : PowR (decodeInt (bytesAt m0 (cc.ptr 1) 32)) _ expAt :=
    CalleeP.Prog.ev_rel (R := PowR _) (cE := paS) (bE := Empty.elim) (G := powQ.geo) (c := cc) (c' := c₀)
      (m0 := m0) (m0' := fun _ => 0) (semA := semA) (semB := semB) (semA' := fun a vs => [expV a vs])
      (semB' := fun b => b.elim) ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩
      (fun a vs vs' h => (hA a vs).symm ▸ pa_rel _ a vs vs' h) (fun b => b.elim) rest copied hS
      (fun s hs => by simpa using List.all_eq_true.mp fx s hs) _ _
      (CalleeP.updOuts_rel (R := PowR _) (E := fun _ => .none) (E' := fun _ => .none) (fun _ => trivial)
        [(.fr 0, .fe)] [paV .copyIn [.b (bytesAt m0 (cc.ptr 1) 32)]] [.f 1]
        ⟨⟨_, rfl, by show _ ≡p _ ^ (0 + 1); rw [Int.pow_succ, Int.pow_zero, Int.one_mul]; exact ModP.refl _⟩, trivial⟩)
      (.ex 0 0)
  revert f7 hrel; generalize expAt = ev; intro f7 hrel
  cases ev <;> simp only [decide_eq_true_eq, reduceCtorEq] at f7
  subst f7
  obtain ⟨y, hy, hxy⟩ := hrel
  simp only [CalleeP.outVals, OutsRel, Iface.base, Kd.base, hio, ioPow, List.map, f6, Option.map_some, Option.getD_some, hy, All2,
    and_true] at ho
  simp only [powSem, OutsRel, ioPow, All2, and_true]
  refine ModP.trans ho (ModP.trans (by simpa using hxy) (ModP.pow ?_ _))
  rw [decode_feVal, hp1, feVal_congr (m := st.mem) (m' := m0) fun y hy => hm 1 _ rfl rfl y (by
    simpa [XInfo.rgns, XLen.v, hp1] using hy)]
  simpa [z] using hx

/-! ## The field callees -/

/-- **`m0c_fe_mul`'s adapter** in build `b`: `x · y` from the call lemma with its effect. -/
noncomputable def mulAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (paS .mul) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by decide) ((Ed25519FeMulSqr.fe_mul_te b).code _ (by decide +kernel))
    (fun _ _ _ h => Ed25519Leaf.blk_eff (s := paS .mul) (L := [0, 1, 2]) (pc := 0) (stk := mulFrame) (fp := fpX true)
      (ini := iniX true) (wo := woX) (by exact h) (by decide +kernel) (by decide) (by decide))
    (fun vs => [paV .mul vs])
    (fun _ _ _ _ _ hg _ _ => ⟨hg.1 0 (by decide), hg.1 1 (by decide), fun _ => hg.1 2 (by decide),
      hg.2.1 (0, 1, 32) (by decide), fun _ => hg.2.1 (0, 2, 32) (by decide)⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, paS, calleeAt, ioMul, fieldR])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, paS, calleeAt, ioMul, fieldR])
    fun _ _ _ _ _ vs _ hi hp => by
      rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | ⟨_ | y | _ | _ | _ | _, _ | _⟩⟩ <;>
        simp only [InsRel, All2, paS, calleeAt, ioMul, Rel, In.kd, and_false, false_and, and_true] at hi
      simp only [OutsRel, All2, paS, calleeAt, ioMul, paV, Rel, BitVec.add_zero, and_true] at hi ⊢
      exact ModP.trans hp (ModP.mul hi.1 hi.2)

/-- **`m0c_fe_sqr`'s adapter** in build `b`: `x · x` from the call lemma with its effect, over the
unit's footprint (its code and padding). -/
noncomputable def sqrAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (paS .sqr) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by decide) ((Ed25519FeMulSqr.fe_sqr_te b).code _ (by decide +kernel))
    (fun _ _ _ h => Ed25519Leaf.blk_eff (s := paS .sqr) (L := [0, 1]) (pc := 0) (stk := mulFrame) (fp := fpX false)
      (ini := iniX false) (wo := woX) (by exact h) (by decide +kernel) (by decide) (by decide))
    (fun vs => [paV .sqr vs])
    (fun _ _ _ _ _ hg _ _ => ⟨hg.1 0 (by decide), hg.1 1 (by decide), by nofun, hg.2.1 (0, 1, 32) (by decide),
      by nofun⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, paS, calleeAt, ioSqr, fieldR])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, paS, calleeAt, ioSqr, fieldR])
    fun _ _ _ _ _ vs _ hi hp => by
      rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, paS, calleeAt, ioSqr, Rel, In.kd, and_false, and_true] at hi
      simp only [OutsRel, All2, paS, calleeAt, ioSqr, paV, Rel, BitVec.add_zero, and_true] at hi ⊢
      exact ModP.trans hp (ModP.mul hi hi)

/-- `m0c_copy` of 8 words, its count pinned. -/
noncomputable def copy8 (b : Build) := letI := b.codeBytes
  ((Ed25519WordLoop.copy_te b).pin 2 2 (BitVec.ofNat 32 8) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 32⟩])
    (fun s => [⟨s.regs 1, 32⟩]) (fun _ h => by simp [Ed25519WordLoop.wordR, h])
    fun _ h => by simp [Ed25519WordLoop.wordR, h]).code (footprint copy) (by decide +kernel)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem inR_of {t : State} {rs : List (M0Crypto.Sym.SExpr × Nat)} {e : M0Crypto.Sym.SExpr} {w : Nat} {y : Word}
    (hm : (e, w) ∈ rs) (h : Region (e.denote t) w y) : InR t rs y :=
  let ⟨_, h1, h2⟩ := inR_one h; ⟨_, List.mem_singleton.1 h1 ▸ hm, h2⟩

/-- The copies of 8 words: bytes or an element to an element, bytes to bytes. -/
def CopyK (i : In) (k : Kd) : Prop :=
  i = .raw (.k 32) ∧ k = .fe ∨ i = .view .fe ∧ k = .fe ∨ i = .view (.bytes 32) ∧ k = .bytes 32

/-- The effect of `m0c_copy` of 8 words is its callee's. -/
theorem copy8_eff {i : In} {k : Kd} (hi : CopyK i k) {base : Word} {p : Nat → Word}
    {tr : List Event} (h : Ed25519WordLoop.wloopE false true base (setPub p 2 (BitVec.ofNat 32 8)) tr) :
    (calleeAt copy (ioCopy i k) [0, 1, 2]).Eff p base tr := by
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, true_and, Bool.false_eq_true, false_and, false_or] at h
  have r0 : (M0Crypto.Sym.SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 0 := rfl
  have r1 : (M0Crypto.Sym.SExpr.reg0 1).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 1 := rfl
  refine Ed25519Leaf.blk_eff (L := [0, 1, 2]) (pc := 0) (fp := [(.reg0 0, 32), (.reg0 1, 32)]) (ini := [(.reg0 1, 32)])
    (wo := [(.reg0 0, 32)]) (EffT.mono h (Nat.le_refl _) (fun y hy => .inr ?_) (fun y hy => .inr ?_) fun y hy => ?_)
    (by rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel)
    (by rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
    (by rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  · rcases hy with hy | hy
    · exact inR_of List.mem_cons_self (r0 ▸ hy)
    · exact inR_of (List.mem_cons_of_mem _ List.mem_cons_self) (r1 ▸ hy)
  · exact inR_of List.mem_cons_self (r1 ▸ hy)
  · obtain ⟨r, hr, o, ho, rfl⟩ := hy
    simp only [List.mem_singleton] at hr; subst hr
    exact region_lt ho

end

/-- **`m0c_copy`'s adapter** from the `ldm`/`stm` loop pinned at 8 words, for input `i` (bytes or
an element) and the result `sem` of its words. -/
noncomputable def copyAd (b : Build) (Rs : Rels) (i : In) (k : Kd) (hi : CopyK i k)
    (sem : List V → List V)
    (hs : ∀ c sp st m vs, InsRel Rs c sp (ioCopy i k) st vs → feVal m (st.regs 0) = feVal st.mem (st.regs 1) →
      OutsRel Rs c sp (ioCopy i k) st m (sem vs)) :
    AdE Rs (cb := b.codeBytes) (calleeAt copy (ioCopy i k) [0, 1, 2]) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf copy; decide) (copy8 b) (fun _ _ _ h => copy8_eff hi h) sem
    (fun _ _ _ st _ hg _ _ => by
      have h2 : st.regs 2 = BitVec.ofNat 32 8 := hg.2.2 (2, 8) (by simp [calleeAt, ioCopy])
      refine ⟨⟨by rw [h2]; unfold Ed25519WordLoop.WordsOk; decide, hg.1 0 (by simp [calleeAt, ioCopy]),
        fun _ => ⟨hg.1 1 (by simp [calleeAt, ioCopy]), ?_⟩, trivial⟩, h2⟩
      rw [h2]; exact hg.2.1 (0, 1, 32) (by simp [calleeAt, ioCopy]))
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioCopy])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioCopy])
    fun c sp st m _ vs _ hi hp => hs c sp st m vs hi (by
      unfold feVal; congr 1; apply List.map_congr_left; intro j hj
      have := List.mem_range.mp hj
      rw [hp.1 j (by rw [hp.2]; simp; omega)])

/-- **The callees' adapters** in build `b`. -/
noncomputable def paAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (paS a)
  | .copyIn => copyAd b Rs _ _ (.inl ⟨rfl, rfl⟩) (fun vs => [paV .copyIn vs]) fun _ _ st m vs hi hw => by
      rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, ioCopy, Rel, In.kd, ALen.val, and_true, and_false] at hi
      simp only [OutsRel, All2, ioCopy, paV, Rel, BitVec.add_zero, and_true] at hi ⊢
      rw [hw, ← decode_feVal, hi]; exact ModP.refl _
  | .copyOut => copyAd b Rs _ _ (.inr (.inl ⟨rfl, rfl⟩)) (fun vs => [paV .copyOut vs]) fun _ _ st m vs hi hw => by
      rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, ioCopy, Rel, In.kd, and_true, and_false] at hi
      simp only [OutsRel, All2, ioCopy, paV, Rel, BitVec.add_zero, and_true] at hi ⊢
      rw [hw]; exact hi
  | .sqr => sqrAd b Rs
  | .mul => mulAd b Rs

theorem paAd_sem (b : Build) (Rs : Rels) :
    ∀ a vs, @Ad.sem Rs b.bytes b.size b.codeBytes _ (paAd b Rs a).ad vs = [paV a vs]
  | .copyIn, _ | .copyOut, _ | .sqr, _ | .mul, _ => rfl

/-- The adapter of `m0c_fe_pow` in each linked build. -/
noncomputable def powAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) powQ.s :=
  CalleeP.adE (cb := b.codeBytes) (q := powQ) (cE := paS) (bE := Empty.elim) (paAd b Rs) (fun e => e.elim)
    (CalleeP.ok_parts pow_ok).choose_spec (pow_code b) (powSem 1)
    fun c sp st m r0 vs _ hi hp => pow_post (cb := b.codeBytes) (paAd_sem b Rs) c sp st m r0 vs hi hp

end M0Crypto.Release.Ed25519FePow
