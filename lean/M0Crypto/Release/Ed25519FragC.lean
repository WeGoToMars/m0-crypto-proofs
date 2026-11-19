import M0Crypto.Release.Ed25519GeProg

/-!
# Field fragments with code-constant operands

`fop` loads an operand `C(label)` by `ldr r, =lit; add r, pc`, which a call's loaders do not
express (`Ld.C` loads only as `Op.ld`). `fragC ι ops k` emits a field operation with such an
operand as its loads, each an `Op.ld` in the generator's order, then the call with no loaders;
any other operation is `fragP`'s call. The bytes are those of `fop`.

`fresC` resolves such a fragment at a static state, as `fres` does, and `fragC_ev0` gives its
values as those of the symbolic run `symL`, so `GeProg`'s term lemmas apply unchanged.
-/

namespace M0Crypto.Release.Ed25519FragC

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg

/-- The operation loads a code address. -/
def hasC (o : FOp) : Bool := o.args.any fun a => a.2 matches .C ..

/-- The loads before the call: all of them when one is a code address. -/
def pre (o : FOp) : List (LowReg × Ld) := if hasC o then o.args else []

/-- The call's own loaders. -/
def cargs (o : FOp) : List (LowReg × Ld) := if hasC o then [] else o.args

section
variable {A Bk : Type}

/-- The constructs of one field operation. -/
def fops (ι : FA → A) (o : FOp) : List (Op A Bk) :=
  (pre o).map (fun a => .ld a.1 a.2) ++ [.call (ι o.a) (cargs o)]

/-- The fragment `ops` before `k`, with the field callees at `ι`. -/
def fragC (ι : FA → A) : List FOp → Prog A Bk → Prog A Bk
  | [], k => k
  | o :: os, k => (fops ι o).foldr .op (fragC ι os k)

end

/-- The state after the loads `as`, each an `Op.ld`. -/
def ldsTy (G : Geo) : St → List (LowReg × Ld) → Option St
  | st, [] => some st
  | st, (r, l) :: as => (ldSv G st r l).bind fun v =>
    ldsTy G { st with σ := (r.toReg, v) :: st.σ.filter (·.1 != r.toReg), ρ := st.ρ.filter (· != r.toReg) } as

/-- **A fragment resolved at a static state**, as `fres`, with the loads of code addresses. -/
def fresC (G : Geo) : St → List FOp → Option (FL × St)
  | st, [] => some ([], st)
  | st, o :: os =>
    match ldsTy G st (pre o) with
    | none => none
    | some st1 =>
      if ldsRes st1.Γ (cargs o) && pubsOk st1.Γ (regsOf st1.Γ st1.σ (cargs o)) (faS o.a).pubs &&
          decide (G.top + (faS o.a).stack ≤ G.N) then
        match ioRes G st1 (regsOf st1.Γ st1.σ (cargs o)) (faS o.a).io with
        | some r => match r.outs, r.srcs.mapM toLf with
          | [(l, .fe)], some ls => (fresC G (r.after st1 σsp) os).map fun p => ((l, o.a, ls) :: p.1, p.2)
          | _, _ => none
        | none => none
      else none

section
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo} {semA : A → List V → List V}
  {semB : Bk → List V → List V} {c : Ctx} {m0 : Mem} {ι : FA → A}

/-- The loads keep the values. -/
theorem lds_ev (k : Prog A Bk) : ∀ (as : List (LowReg × Ld)) (st st' : St) (E : Loc → V), ldsTy G st as = some st' →
    ((as.map fun a => (Op.ld a.1 a.2 : Op A Bk)).foldr Prog.op k).ev cE bE G semA semB c m0 st E =
      k.ev cE bE G semA semB c m0 st' E
  | [], st, st', E, h => by simp only [ldsTy, Option.some.injEq] at h; subst h; rfl
  | (r, l) :: as, st, st', E, h => by
    simp only [ldsTy, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hty : (Op.ld r l : Op A Bk).ty cE bE G st =
        some { st with σ := (r.toReg, v) :: st.σ.filter (·.1 != r.toReg), ρ := st.ρ.filter (· != r.toReg) } := by
      simp only [Op.ty, hv, Option.map_some]
    simp only [List.map_cons, List.foldr_cons]
    rw [Prog.ev_op hty]
    exact lds_ev k as _ _ E h

/-- **A resolved fragment's values**: those of its symbolic run, at every location. -/
theorem fragC_ev (hE : ∀ a, cE (ι a) = faS a) (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) (E0 : Loc → V)
    (k : Prog A Bk) : ∀ (ops : List FOp) (st st' : St) (L : FL) (cur : Loc → Tm) (E : Loc → V),
      fresC G st ops = some (L, st') → (∀ l, E l = (cur l).ev (lfV G c m0 E0)) →
      (fragC ι ops k).ev cE bE G semA semB c m0 st E =
        k.ev cE bE G semA semB c m0 st' (fun l => (symL cur L l).ev (lfV G c m0 E0))
  | [], st, st', L, cur, E, h, hE' => by
    simp only [fresC, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [fragC, symL]; rw [show E = _ from funext hE']
  | o :: os, st, st', L, cur, E, h, hE' => by
    simp only [fresC] at h
    split at h
    · exact absurd h (by simp)
    · rename_i st1 h1
      split at h
      · rename_i hc
        split at h
        · rename_i r hr
          split at h
          · rename_i l ls ho hl
            obtain ⟨⟨L', st''⟩, hL', he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
            have hty : (Op.call (ι o.a) (cargs o) : Op A Bk).ty cE bE G st1 = some (r.after st1 σsp) := by
              simp only [Op.ty, hE, hc, ↓reduceIte, hr, Option.map_some]
            simp only [fragC, fops, List.foldr_append, List.foldr_cons, List.foldr_nil]
            rw [lds_ev _ _ _ _ _ h1, Prog.ev_op hty]
            refine fragC_ev hE hS E0 k os _ _ L' _ _ hL' fun x => ?_
            simp only [Op.ev, hE, hr, hS, ho, updOuts, stepT]
            split
            · rw [opT_ev, List.map_map, srcs_val E0 hE' r.srcs ls hl]; rfl
            · exact hE' x
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- `fragC_ev` from the values before the fragment. -/
theorem fragC_ev0 (hE : ∀ a, cE (ι a) = faS a) (hS : ∀ a vs, semA (ι a) vs = [faV a vs]) {ops : List FOp}
    {st st' : St} {L : FL} (h : fresC G st ops = some (L, st')) (k : Prog A Bk) (E : Loc → V) :
    (fragC ι ops k).ev cE bE G semA semB c m0 st E = k.ev cE bE G semA semB c m0 st' (fragE G c m0 E L) :=
  fragC_ev hE hS E k ops st st' L tm0 E h fun _ => rfl

end

end M0Crypto.Release.Ed25519FragC
