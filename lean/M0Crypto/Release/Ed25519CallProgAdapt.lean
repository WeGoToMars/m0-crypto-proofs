import M0Crypto.Release.Ed25519CallProgEffect

/-!
# Call programs: adapters by construction

`AdE` is a callee adapter with the byte effect of its trace. `Ad.ofTSpec` builds one from a
routine's call lemma with an effect (`Routine.TE`, for example from `Routine.te_by`) at the
callee's public words: the trace `T`, its spec and its effect come from the call lemma, and only
the interface lemmas (entry condition, footprints, result) are the routine's own.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb (Event)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect

-- The code bytes are an implicit argument, not an instance argument: projections and call sites
-- take them from the types (`CodeBytes` has out-params).
variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} {cb : CodeBytes B BS}

/-- **A callee adapter with its effect**: the adapter and the effect of its trace at every public
value. -/
structure AdE (s : CalleeS) where
  ad : Ad Rs B BS s
  ef : ∀ base p, s.Eff p base (ad.T base p)

/-- The public values of callee `s` at its entry state. -/
def CalleeS.pub (s : CalleeS) (_ : Word) (st : State) : Nat → Word := pubOf (s.pubs.map (PubW.get st))

variable {Rs}

/-- **An adapter from a call lemma with an effect.** `te` is the routine's call lemma at the
callee's public values with effect `E`, which implies the callee's effect (`hE`); `sem` and the
interface lemmas `pre`, `wr`, `rd` and `post` are those of `Ad`. -/
noncomputable def Ad.ofTSpec {s : CalleeS} (R : Routine) (he : R.entry = s.entry) (hc : R.code = s.code)
    (hs : R.stack = s.stack) {E : Word → (Nat → Word) → TrP} (te : R.TE s.pub E)
    (hE : ∀ base p tr, E base p tr → s.Eff p base tr) (sem : List V → List V)
    (pre : ∀ c sp base st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
      R.Pre base st)
    (wr : ∀ st, R.wr st = rgnsC st.regs s.io.wr) (rd : ∀ st, R.rd st = rgnsC st.regs s.io.rd)
    (post : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → R.Post st m r0 →
      OutsRel Rs c sp s.io st m (sem vs)) : AdE Rs (cb := cb) s :=
  ⟨⟨R, he, hc, hs, te.T, te.spec, sem, pre, wr, rd, post⟩, fun base p => hE base p _ (te.eff base p)⟩

/-- **A call lemma for code `c` that covers the routine's**, such as a unit's footprint with its
padding. -/
noncomputable def _root_.M0Crypto.Release.Routine.Routine.TE.code {α : Type} {f : Routine} {pub : Word → State → α}
    {E : Word → α → TrP} [CodeBytes B BS] (te : f.TE pub E) (c : List (Nat × Nat)) (h : rangesSub f.code c = true) :
    ({ f with code := c } : Routine).TE pub E :=
  ⟨te.T, fun base s e => ReachFT.mono (te.spec base s ⟨e.pc, e.base4, e.code, e.sp4, e.room, e.lr, e.sepCode,
      e.sepWr, e.sepRd, fun hp => e.ret (PcIn.mono h hp), e.pre⟩) (fun _ hy => PcIn.mono h hy) (fun _ h => h)
      (fun _ h => h) (fun _ h => h) (fun _ ht => ⟨ht.pc, ht.sp, ht.keep, ht.post⟩) fun _ h => h, te.eff⟩

/-- The public values `p` with value `j` set to `v`. -/
def setPub (p : Nat → Word) (j : Nat) (v : Word) : Nat → Word := fun i => if i = j then v else p i

theorem setPub_self {p : Nat → Word} {j : Nat} {v : Word} (h : p j = v) : setPub p j v = p :=
  funext fun i => by unfold setPub; split <;> simp_all

/-- **A call lemma pinned at a public value**: where public value `j` is register `r`, the routine
whose entry also has `r = v`, with footprints `wr₁`, `rd₁` that are `f`'s there, has the trace `T`
at `p` with `p j = v` and the effect there, and its result records `r = v`. -/
noncomputable def _root_.M0Crypto.Release.Routine.Routine.TE.pin {f : Routine} {pub : Word → State → Nat → Word}
    {E : Word → (Nat → Word) → TrP} [CodeBytes B BS] (te : f.TE pub E) (j : Nat) (r : Reg) (v : Word)
    (hp : ∀ base s, pub base s j = s.regs r) (wr₁ rd₁ : State → List Rgn)
    (hw : ∀ s, s.regs r = v → f.wr s = wr₁ s) (hr : ∀ s, s.regs r = v → f.rd s = rd₁ s) :
    (Routine.mk f.entry f.code f.stack (fun b s => f.Pre b s ∧ s.regs r = v) wr₁ rd₁
      (fun s m x => f.Post s m x ∧ s.regs r = v) f.clob).TE pub
      fun b p => E b (setPub p j v) :=
  ⟨fun b p => te.T b (setPub p j v), fun base s e => by
    have hv := e.pre.2
    show ReachFT _ _ _ _ _ _ _ (Tr.is (te.T base (setPub (pub base s) j v)))
    rw [setPub_self (by rw [hp]; exact hv)]
    have e' : f.Entry base s := ⟨e.pc, e.base4, e.code, e.sp4, e.room, e.lr, by rw [hw s hv]; exact e.sepCode,
      by rw [hw s hv]; exact e.sepWr, by rw [hr s hv]; exact e.sepRd, e.ret, e.pre.1⟩
    refine ReachFT.mono (te.spec base s e') (fun _ h => h) (fun y h => ?_) (fun y h => ?_) (fun _ h => h)
      (fun _ ht => ⟨ht.pc, ht.sp, ht.keep, ht.post, hv⟩) fun _ h => h
    · show Has (_ :: _ :: rd₁ s) y; rw [← hr s hv]; exact h
    · show Has (_ :: wr₁ s) y; rw [← hw s hv]; exact h, fun b p => te.eff b _⟩

/-! ## Symbolic effects as callee effects -/

section eff
open M0Crypto.Sym (SExpr inRgn)

/-- A footprint region of a constant length. -/
def SRgn.e (x : SRgn) : Option (SExpr × Nat) :=
  match x.len with | .k n => some (rgnE x.r x.off n) | .r _ => none

/-- The written bytes of an input of a constant size: a view other than a context, or raw bytes. -/
def inE : Reg × Nat × In → Option (SExpr × Nat)
  | (_, _, .view (.ctx _)) | (_, _, .view .rw) | (_, _, .raw (.r _)) => none
  | (r, o, .view k) => some (rgnE r o k.sz)
  | (r, o, .raw (.k n)) => some (rgnE r o n)

/-- The written bytes of an output other than a context. -/
def outE : Reg × Nat × Kd → Option (SExpr × Nat)
  | (_, _, .ctx _) => none
  | (r, o, k) => some (rgnE r o k.sz)

/-- Every region of `xs` lies in one of `ys`. -/
def subR (xs ys : List (SExpr × Nat)) : Bool := xs.all fun a => ys.any (inRgn a.1 a.2)

/-- Every byte of each region of `xs` lies in one of `ys`. -/
def covR (xs ys : List (SExpr × Nat)) : Bool :=
  xs.all fun a => (List.range a.2).all fun k => ys.any (inRgnOff a.1 k)

/-- The registers of an interface's regions. -/
def ioRegs (io : Iface) : List Reg :=
  io.ins.filterMap (fun x => (inE x).map fun _ => x.1) ++ io.outs.map (·.1) ++ (io.rd ++ io.wr).map (·.r)

/-- **The decided effect check**: the accessed regions `fp` lie in the footprints, each byte of the
regions `ini` read first lies in an input, and the outputs have constant sizes and lie in the
writes `wo`. -/
def effOk (io : Iface) (fp ini wo : List (SExpr × Nat)) : Bool :=
  subR fp ((io.rd ++ io.wr).filterMap SRgn.e) && covR ini (io.ins.filterMap inE) &&
    io.outs.all (fun x => (outE x).isSome) && subR (io.outs.filterMap outE) wo

theorem inR_sub {t : State} {xs ys : List (SExpr × Nat)} (h : subR xs ys = true) {y : Word}
    (hy : InR t xs y) : InR t ys y := by
  obtain ⟨a, ha, o, ho, rfl⟩ := hy
  obtain ⟨b, hb, hi⟩ := List.any_eq_true.1 (List.all_eq_true.1 h a ha)
  obtain ⟨o', ho', he⟩ := inRgn_den (spl_denote t) hi ho
  exact ⟨b, hb, o', ho', he⟩

theorem inR_cov {t : State} {xs ys : List (SExpr × Nat)} (h : covR xs ys = true) {y : Word}
    (hy : InR t xs y) : InR t ys y := by
  obtain ⟨a, ha, o, ho, rfl⟩ := hy
  obtain ⟨b, hb, hi⟩ :=
    List.any_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h a ha) o (List.mem_range.2 ho))
  obtain ⟨o', ho', he⟩ := inRgnOff_den (spl_denote t) hi
  exact ⟨b, hb, o', ho', he⟩

theorem region_lt {a : Word} {o n : Nat} (h : o < n) : Region a n (a + BitVec.ofNat 32 o) := by
  simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp only [BitVec.toNat_ofNat]; omega

theorem inE_eq (s : CalleeS) (p : Nat → Word) {x : Reg × Nat × In} {a : SExpr × Nat} (h : inE x = some a) :
    a = rgnE x.1 x.2.1 (s.iniIn p x.2.2) := by
  rcases x with ⟨r, o, ⟨_ | _ | _ | _ | _ | _ | _⟩ | ⟨_ | _⟩⟩ <;> simp only [inE, reduceCtorEq, Option.some.injEq] at h <;>
    exact h.symm

theorem outE_eq (s : CalleeS) (p : Nat → Word) {x : Reg × Nat × Kd} {a : SExpr × Nat} (h : outE x = some a) :
    a = rgnE x.1 x.2.1 (s.iniOut p x.2.2) := by
  rcases x with ⟨r, o, _ | _ | _ | _ | _ | _ | _⟩ <;> simp only [outE, reduceCtorEq, Option.some.injEq] at h <;>
    exact h.symm

/-- **An effect over symbolic regions is the callee's**, given the decided `effOk` and a state `t`
whose interface registers are the callee's public values. -/
theorem CalleeS.eff_of {s : CalleeS} {p : Nat → Word} {base : Word} {stk : Nat} {t : State}
    {fp ini wo : List (SExpr × Nat)} {tr : List Event}
    (h : EffT stk (fun y => Has [codeR base] y ∨ InR t fp y) (fun y => Has [codeR base] y ∨ InR t ini y)
      (InR t wo) (s.reg p 13) tr) (hc : effOk s.io fp ini wo = true)
    (hs : stk ≤ s.stack) (ht : ∀ r ∈ ioRegs s.io, t.regs r = s.reg p r) : s.Eff p base tr := by
  simp only [effOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hf, hi⟩, ho⟩, hw⟩ := hc
  refine EffT.mono h hs (fun y hy => hy.elim (fun ⟨q, hq, h⟩ => ⟨q, List.mem_cons.2 (.inl (List.mem_singleton.1 hq)), h⟩) fun hy => ?_)
    (fun y hy => hy.elim .inl fun hy => ?_) (fun y ⟨x, hx, hy⟩ => ?_)
  · obtain ⟨a, ha, o, ho', rfl⟩ := inR_sub hf hy
    obtain ⟨⟨r, off, l⟩, hx, he⟩ := List.mem_filterMap.1 ha
    cases l with
    | r _ => simp [SRgn.e] at he
    | k n =>
      simp only [SRgn.e, Option.some.injEq] at he; subst he; simp only [rgnE] at ho'
      have hm : (⟨s.reg p r + BitVec.ofNat 32 off, n⟩ : Rgn) ∈ rgnsC (s.reg p) (s.io.rd ++ s.io.wr) :=
        List.mem_flatMap.2 ⟨_, hx, by simp [SRgn.rgnC, ALen.val, show n ≠ 0 by omega]⟩
      rw [rgnsC, List.flatMap_append] at hm
      refine ⟨⟨s.reg p r + BitVec.ofNat 32 off, n⟩, ?_, o, ho', ?_⟩
      · exact (List.mem_append.1 hm).elim (fun h => List.mem_append_left _ (.tail _ h)) (List.mem_append_right _)
      · show t.regs r + _ + _ = _; rw [ht r (List.mem_append_right _ (List.mem_map_of_mem hx))]; rfl
  · obtain ⟨a, ha, o, ho', rfl⟩ := inR_cov hi hy
    obtain ⟨x, hx, he⟩ := List.mem_filterMap.1 ha
    have e := inE_eq s p he; subst e
    refine .inr ⟨x, hx, ?_⟩
    rw [← ht x.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_filterMap.2 ⟨x, hx, by simp [he]⟩)))]
    exact region_lt ho'
  · obtain ⟨a, he⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 ho x hx)
    have e := outE_eq s p he; subst e
    refine inR_sub hw ⟨_, List.mem_filterMap.2 ⟨x, hx, he⟩, (y - (s.reg p x.1 + BitVec.ofNat 32 x.2.1)).toNat, hy, ?_⟩
    show y = t.regs x.1 + BitVec.ofNat 32 x.2.1 + _
    rw [ht x.1 (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx))), BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

end eff

end M0Crypto.Release.Ed25519CallProg
