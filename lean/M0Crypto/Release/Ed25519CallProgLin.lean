import M0Crypto.Release.Ed25519CallProgCheck

/-!
# Call programs: static runs as lists of updates

A program without counted loops or dispatches decides its control flow from its static states
alone: every test and every loop exit is public. `Prog.lin` runs it at a static state and lists
the updates of the values its constructs make (`ROp`: a call's or a block's outputs, a loaded
byte), each resolved at its state. `lin_ev`: where `lin` succeeds, the program's values are those
of its updates (`runR`), and its typing ends in the same state. A decided equation of `lin` with a
list in a closed form then reduces a program's values to a fold over that list.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Reg Mem)

deriving instance DecidableEq for Src

/-- A construct's update of the values, resolved at its static state. -/
inductive ROp (A Bk : Type) where
  | call (a : A) (outs : List (Loc × Kd)) (srcs : List Src)
  | blk (b : Bk) (outs : List (Loc × Kd)) (srcs : List Src)
  | ldb (r : Reg) (s : Src)
  deriving DecidableEq

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- A construct's updates at the state `st`. -/
def Op.rops (st : St) : Op A Bk → List (ROp A Bk)
  | .call a as => match ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | some r => [.call a r.outs r.srcs]
    | none => []
  | .blk b as => match ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
    | some r => [.blk b r.outs r.srcs]
    | none => []
  | .ldb rd rb ri => match ldbOff st.σ rb ri with
    | some a => match findSlice st.Γ (.fr a) 1 with
      | some s => [.ldb rd.toReg s]
      | none => []
    | none => []
  | _ => []

/-- The passes of a loop with exits, from the body's run `fb` and the rest's `fk`. -/
def whLin (fb fk : St → Option (List (ROp A Bk) × St)) : Nat → St → Option (List (ROp A Bk) × St)
  | 0, _ => none
  | n + 1, st => match fb st with
    | some (L, s) => match s.ex with
      | none => (whLin fb fk n s).map fun p => (L ++ p.1, p.2)
      | some 0 => (fk { s with ex := none }).map fun p => (L ++ p.1, p.2)
      | some (l + 1) => some (L, { s with ex := some l })
    | none => none

/-- **A static run**: the updates of a program without counted loops or dispatches, and its state
after. -/
def Prog.lin : Prog A Bk → St → Option (List (ROp A Bk) × St)
  | .nil, st => some ([], st)
  | .op x k, st => (x.ty cE bE G st).bind fun st' => (k.lin st').map fun p => (x.rops cE bE G st ++ p.1, p.2)
  | .loop .., _ => none
  | .sel .., _ => none
  | .xit g s cc _ l k, st => match xitSt G st g s cc with
    | some (st2, true) => some ([], { st2 with ex := some l })
    | some (st2, false) => k.lin st2
    | none => none
  | .hd b h k, st => match b.lin st with
    | some (L, s) => match s.ex with
      | none => (k.lin s).map fun p => (L ++ p.1, p.2)
      | some 0 => match h.lin { s with ex := none } with
        | some (L', s') => if s'.ex = none then (k.lin s').map fun p => (L ++ L' ++ p.1, p.2)
          else some (L ++ L', s')
        | none => none
      | some (_ + 1) => none
    | none => none
  | .wh n b k, st => whLin (fun s => b.lin s) (fun s => k.lin s) n st

variable (semA : A → List V → List V) (semB : Bk → List V → List V) (c : Ctx) (m0 : Mem)

/-- The values after an update. -/
def ROp.ev : ROp A Bk → (Loc → V) → Loc → V
  | .call a outs srcs, E => updOuts E outs (semA a (srcs.map (Src.val G c m0 E)))
  | .blk b outs srcs, E => let w := semB b (srcs.map (Src.val G c m0 E))
    setRg (updOuts E outs (w.take (bE b).io.outs.length)) (bE b).io.ro (w.drop (bE b).io.outs.length)
  | .ldb r s, E => setRg E [r] [byteW (Src.val G c m0 E s)]

/-- The values after a list of updates. -/
def runR : List (ROp A Bk) → (Loc → V) → Loc → V
  | [], E => E
  | r :: L, E => runR L (r.ev bE G semA semB c m0 E)

theorem runR_append (L L' : List (ROp A Bk)) (E : Loc → V) :
    runR bE G semA semB c m0 (L ++ L') E = runR bE G semA semB c m0 L' (runR bE G semA semB c m0 L E) := by
  induction L generalizing E with
  | nil => rfl
  | cons r L ih => exact ih _

/-- A construct's values are those of its updates. -/
theorem Op.ev_rops (st : St) (x : Op A Bk) (E : Loc → V) :
    x.ev cE bE G semA semB c m0 st E = runR bE G semA semB c m0 (x.rops cE bE G st) E := by
  cases x with
  | call a as => simp only [Op.ev, Op.rops]; cases ioRes G st (regsOf st.Γ st.σ as) (cE a).io <;> rfl
  | blk b as => simp only [Op.ev, Op.rops]; cases ioRes G st (regsOf st.Γ st.σ as) (bE b).io <;> rfl
  | ldb rd rb ri =>
    simp only [Op.ev, Op.rops]
    cases ldbOff st.σ rb ri with
    | none => rfl
    | some a => dsimp only; cases findSlice st.Γ (.fr a) 1 <;> rfl
  | spill | drop | ld | pub | keep | isl => rfl

theorem whLin_ev {tb : St → Option St} {eb ek : St → (Loc → V) → Loc → V}
    {fb fk : St → Option (List (ROp A Bk) × St)}
    (hb : ∀ st L s, fb st = some (L, s) → tb st = some s ∧ ∀ E, eb st E = runR bE G semA semB c m0 L E)
    (hk : ∀ st L s, fk st = some (L, s) → ∀ E, ek st E = runR bE G semA semB c m0 L E) :
    ∀ n st L s, whLin fb fk n st = some (L, s) → ∀ E, whEv tb eb ek n st E = runR bE G semA semB c m0 L E
  | 0, _, _, _, h, _ => by simp [whLin] at h
  | n + 1, st, L, s, h, E => by
    simp only [whLin] at h
    split at h
    · rename_i L1 s1 h1
      obtain ⟨t1, e1⟩ := hb st L1 s1 h1
      simp only [whEv, t1]
      split at h
      · rename_i hx
        simp only [hx]
        obtain ⟨⟨L2, s2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        rw [whLin_ev hb hk n s1 L2 s2 h2, e1, runR_append]
      · rename_i hx
        simp only [hx]
        obtain ⟨⟨L2, s2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        rw [hk _ L2 s2 h2, e1, runR_append]
      · rename_i l hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        simp only [hx]; exact e1 E
    · exact absurd h (by simp)

theorem whLin_ty {tb tk : St → Option St} {fb fk : St → Option (List (ROp A Bk) × St)}
    (hb : ∀ st L s, fb st = some (L, s) → tb st = some s) (hk : ∀ st L s, fk st = some (L, s) → tk st = some s) :
    ∀ n st L s, whLin fb fk n st = some (L, s) → whTy tb tk n st = some s
  | 0, _, _, _, h => by simp [whLin] at h
  | n + 1, st, L, s, h => by
    simp only [whLin] at h
    split at h
    · rename_i L1 s1 h1
      simp only [whTy, hb st L1 s1 h1]
      split at h
      · rename_i hx
        simp only [hx]
        obtain ⟨⟨L2, s2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        exact whLin_ty hb hk n s1 L2 s2 h2
      · rename_i hx
        simp only [hx]
        obtain ⟨⟨L2, s2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        exact hk _ L2 s2 h2
      · rename_i l hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        simp only [hx]
    · exact absurd h (by simp)

/-- **A static run's values and state**: where `lin` succeeds, the program types to its state and
its values are those of its updates. -/
theorem Prog.lin_ev : ∀ (P : Prog A Bk) (st : St) (L : List (ROp A Bk)) (s : St),
    P.lin cE bE G st = some (L, s) →
      P.ty cE bE G st = some s ∧ ∀ E, P.ev cE bE G semA semB c m0 st E = runR bE G semA semB c m0 L E
  | .nil, st, L, s, h => by
    simp only [Prog.lin, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  | .op x k, st, L, s, h => by
    simp only [Prog.lin, Option.bind_eq_some_iff] at h
    obtain ⟨st', h1, h2⟩ := h
    obtain ⟨⟨L2, s2⟩, h3, he⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨t, e⟩ := Prog.lin_ev k st' L2 s2 h3
    refine ⟨by simp only [Prog.ty, h1, Option.bind_some, t], fun E => ?_⟩
    simp only [Prog.ev, h1]
    rw [e, Op.ev_rops, runR_append]
  | .loop .., _, _, _, h => by simp [Prog.lin] at h
  | .sel .., _, _, _, h => by simp [Prog.lin] at h
  | .xit g s' cc sh l k, st, L, s, h => by
    simp only [Prog.lin] at h
    split at h
    · rename_i st2 h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp only [Prog.ty, h1], fun E => by simp only [Prog.ev, h1]; rfl⟩
    · rename_i st2 h1
      obtain ⟨t, e⟩ := Prog.lin_ev k st2 L s h
      exact ⟨by simp only [Prog.ty, h1, t], fun E => by simp only [Prog.ev, h1, e]⟩
    · exact absurd h (by simp)
  | .hd b g k, st, L, s, h => by
    simp only [Prog.lin] at h
    split at h
    · rename_i L1 s1 h1
      obtain ⟨t1, e1⟩ := Prog.lin_ev b st L1 s1 h1
      split at h
      · rename_i hx
        obtain ⟨⟨L2, s2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨t2, e2⟩ := Prog.lin_ev k s1 L2 s2 h2
        exact ⟨by simp only [Prog.ty, t1, hx, t2], fun E => by simp only [Prog.ev, t1, hx]; rw [e2, e1, runR_append]⟩
      · rename_i hx
        split at h
        · rename_i L2 s2 h2
          obtain ⟨t2, e2⟩ := Prog.lin_ev g _ L2 s2 h2
          split at h
          · rename_i hn
            obtain ⟨⟨L3, s3⟩, h3, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
            obtain ⟨t3, e3⟩ := Prog.lin_ev k s2 L3 s3 h3
            refine ⟨by simp only [Prog.ty, t1, hx, t2, hn, ↓reduceIte, t3], fun E => ?_⟩
            simp only [Prog.ev, t1, hx, t2, hn, ↓reduceIte]
            rw [e3, e2, e1, runR_append, runR_append]
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨by simp only [Prog.ty, t1, hx, t2, hn, ↓reduceIte], fun E => ?_⟩
            simp only [Prog.ev, t1, hx, t2, hn, ↓reduceIte]
            rw [e2, e1, runR_append]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | .wh n b k, st, L, s, h => by
    simp only [Prog.lin] at h
    exact ⟨whLin_ty (fun st L s h => (Prog.lin_ev b st L s h).1) (fun st L s h => (Prog.lin_ev k st L s h).1) n st L s h,
      fun E => whLin_ev bE G semA semB c m0 (fun st L s h => Prog.lin_ev b st L s h)
        (fun st L s h => (Prog.lin_ev k st L s h).2) n st L s h E⟩

end

end M0Crypto.Release.Ed25519CallProg
