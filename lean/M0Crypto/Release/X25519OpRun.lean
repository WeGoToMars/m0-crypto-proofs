import M0Crypto.Release.X25519EntryCode

set_option linter.unusedSectionVars false

/-!
Runs of slot operations of `m0c_x25519` (plan `x25519-proofs.md`, phase 9, step 1).

`Fn.rel` is what one operation computes on slot values: a congruence mod p for the five
arithmetic operations, the exact choice for `select` (mask in `r7`). `Eff` is the effect of one
operation between `Body` states: the destination slot is related to the operands, the rest of
the frame is unchanged, and `select` keeps its mask. `OpW fn` says that every operation with
function `fn` placed in the entry has that effect; `call_opW` proves it for the three calls from
`X25519Op.op_call_w`. `opsAt_w` runs a list of operations by induction on the list.
-/

namespace M0Crypto.Release.X25519OpRun
open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feMulSize feSqr feSqrSize feMulcAdd feMulcAddSize)

/-- The value relation of an operation: `rel m x a b` with `m` the mask in `r7` before it,
`x` the destination after it and `a`, `b` the operands before it. -/
def _root_.M0Crypto.Release.X25519EntryCode.Fn.rel : Fn → Word → Int → Int → Int → Prop
  | .add => fun _ x a b => ModP x (a + b)
  | .sub => fun _ x a b => ModP x (a - b)
  | .sel => fun m x a b => x = if m = 0 then a else b
  | .mul => fun _ x a b => ModP x (a * b)
  | .sqr => fun _ x a _ => ModP x (a * a)
  | .mulc => fun _ x a b => ModP x (121666 * a + b)

/-- A slot address of the frame. -/
abbrev slotAt (c : X25519.Ctx) (d : Nat) : Word := E c + BitVec.ofNat 32 d

/-- Slot-level well-formedness of an operation (decidable). -/
def _root_.M0Crypto.Release.X25519EntryCode.Op.ok (p : Op) : Bool :=
  decide (SlotOk p.d) && decide (SlotOk p.a) &&
    match p.b with
    | some b => decide (SlotOk b)
    | none => p.fn == .sqr

/-- The effect of one operation from `s` to `t`. -/
structure Eff (c : X25519.Ctx) (m1 : Mem) (p : Op) (s t : State) : Prop where
  body : Body c m1 t
  val : p.fn.rel (s.regs 7) (feVal t.mem (slotAt c p.d)) (feVal s.mem (slotAt c p.a))
    (feVal s.mem (bAddr (E c) (s.regs 2) p.b))
  keep : ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c p.d) 32 y → t.mem y = s.mem y
  mask : p.fn = .sel → t.regs 7 = s.regs 7

/-- The mask precondition of `select`. -/
def MaskOk (fn : Fn) (s : State) : Prop := fn = .sel → s.regs 7 = 0 ∨ s.regs 7 = BitVec.allOnes 32

/-- Every operation with function `fn` placed in the entry has its effect. -/
def OpW (fn : Fn) : Prop :=
  ∀ {c : X25519.Ctx} (_ : X25519.Valid c) {m1 : Mem} (_ : CodeAt m1 c.base B)
    {Wr : Word → Prop} (_ : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (_ : PcOk c.base lo hi Pc)
    {s : State} {Q : State → Prop} {o d a : Nat} {b : Option Nat},
    seqAt B o (opAt o ⟨fn, d, a, b⟩) = true → o % 2 = 0 → lo ≤ o →
    o + seqSize (opAt o ⟨fn, d, a, b⟩) ≤ hi →
    s.pc = c.base + BitVec.ofNat 32 o → Body c m1 s → Op.ok ⟨fn, d, a, b⟩ = true → MaskOk fn s →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (opAt o ⟨fn, d, a, b⟩)) →
      Eff c m1 ⟨fn, d, a, b⟩ s t → ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q

theorem ok_parts {p : Op} (h : p.ok = true) :
    SlotOk p.d ∧ SlotOk p.a ∧ (∀ x, p.b = some x → SlotOk x) ∧ (p.b = none → p.fn = .sqr) := by
  obtain ⟨fn, d, a, b⟩ := p
  simp only [Op.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun x hx => ?_, fun hb => ?_⟩
  · subst hx; simpa using h3
  · subst hb; simpa using h3

/-- The three call operations. -/
theorem call_opW {fn : Fn} {off size frame : Nat} {useB : Bool} {f : Int → Int → Int}
    (hrun : X25519Call.RoutineRun off size frame useB f) (hfr : frame ≤ CALLEE)
    (hrt : off + size ≤ Artifacts.Release.x25519)
    (htgt : fn.target = off) (hcall : fn ≠ .add ∧ fn ≠ .sub ∧ fn ≠ .sel)
    (hB : useB = true → fn ≠ .sqr)
    (hrel : ∀ m x a b, ModP x (f a b) → fn.rel m x a b) : OpW fn := by
  intro c hv m1 hcode Wr hWr Pc lo hi hPO s Q o d a b hseq ho hlo hend hpc hs hok _ k
  obtain ⟨hd, ha, hb, hbn⟩ := ok_parts hok
  have he : opAt o ⟨fn, d, a, b⟩ = opCall o off d a b := by
    subst htgt
    match fn, hcall with
    | .mul, _ | .sqr, _ | .mulc, _ => rfl
    | .add, h | .sub, h | .sel, h => simp at h
  rw [he] at hseq hend k
  refine op_call_w hrun hfr hrt hv hcode hWr hPO hseq ho hlo hend hpc hs hd ha hb
    (fun hu => ?_) fun t tp tb tv tk => k t tp ⟨tb, hrel _ _ _ _ tv, tk, fun h => absurd h hcall.2.2⟩
  cases hb' : b with
  | some _ => rfl
  | none => exact absurd (hbn hb') (hB hu)

theorem mul_opW : OpW .mul :=
  call_opW (fn := .mul) X25519Call.mul_run (by decide) (by decide) rfl (by decide) (fun _ => by decide)
    fun _ _ _ _ h => h

theorem sqr_opW : OpW .sqr :=
  call_opW (fn := .sqr) X25519Call.sqr_run (by decide) (by decide) rfl (by decide) (fun h => nomatch h)
    fun _ _ _ _ h => h

theorem mulc_opW : OpW .mulc :=
  call_opW (fn := .mulc) X25519Call.mulcAdd_run (by decide) (by decide) rfl (by decide) (fun _ => by decide)
    fun _ _ _ _ h => h

/-! ## Lists of operations -/

theorem seqSize_even : ∀ is : List Instr, seqSize is % 2 = 0
  | [] => rfl
  | i :: is => by
    have := seqSize_even is
    have : i.size % 2 = 0 := by cases i <;> simp [Instr.size]
    simp only [seqSize, List.map_cons, List.sum_cons] at *
    omega

/-- The effects of a list of operations, one state per boundary. -/
inductive OpsEff (c : X25519.Ctx) (m1 : Mem) : List Op → State → State → Prop
  | nil (s) : OpsEff c m1 [] s s
  | cons {p ps s u t} : Eff c m1 p s u → OpsEff c m1 ps u t → OpsEff c m1 (p :: ps) s t

/-- A list of operations without `select`, each meeting `OpW`. -/
theorem opsAt_w {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
    {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : PcOk c.base lo hi Pc) {Q : State → Prop} :
    ∀ (ops : List Op) (o : Nat) (s : State), (∀ p ∈ ops, OpW p.fn ∧ p.fn ≠ .sel) →
    ops.all Op.ok = true →
    seqAt B o (opsAt o ops) = true → o % 2 = 0 → lo ≤ o →
    o + seqSize (opsAt o ops) ≤ hi →
    s.pc = c.base + BitVec.ofNat 32 o → Body c m1 s →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (opsAt o ops)) → OpsEff c m1 ops s t →
      ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q
  | [], o, s, _, _, _, _, _, _, hpc, _, k => k s (by simpa [opsAt, seqSize] using hpc) (.nil s)
  | p :: ps, o, s, hW, hok, hseq, ho, hlo, hend, hpc, hs, k => by
    obtain ⟨fn, d, a, b⟩ := p
    simp only [opsAt] at hseq hend k
    rw [seqAt_append, Bool.and_eq_true] at hseq
    rw [seqSize_append] at hend
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hW1 := hW _ List.mem_cons_self
    have h1 : o + seqSize (opAt o ⟨fn, d, a, b⟩) ≤ hi := by omega
    refine hW1.1 hv hcode hWr hPO hseq.1 ho hlo h1 hpc hs hok.1 (fun h => absurd h hW1.2) ?_
    intro u upc ue
    have he := seqSize_even (opAt o ⟨fn, d, a, b⟩)
    refine opsAt_w hv hcode hWr hPO ps _ u (fun q hq => hW q (List.mem_cons_of_mem _ hq)) hok.2 hseq.2
      (by omega) (by omega) (by omega) upc ue.body fun t tpc te => k t ?_ (.cons ue te)
    rw [tpc, seqSize_append, Nat.add_assoc]

end M0Crypto.Release.X25519OpRun
