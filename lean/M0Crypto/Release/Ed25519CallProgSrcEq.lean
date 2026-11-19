import M0Crypto.Release.Ed25519CallProgStitchRun
import M0Crypto.Release.Ed25519CallProgGood

/-!
# The values from the entry memory read through their sources

A program's values read the entry memory only through the buffer sources its typing resolves
(`.ext`, `.extF`): each an `ok`, readable region of an external buffer (`SrcX`). Two entry memories
that agree there (`XAgree`) give the same values (`Prog.ev_congr`), the same inputs at a stitched
call (`ioVs_congr`) and the same values after it (`xcallEv_congr`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg Mem)
open M0Crypto.Release
open M0Crypto.Release.Footprint

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- **Two entry memories agree on the buffers' readable regions.** -/
def XAgree (c : Ctx) (m0 m0' : Mem) : Prop :=
  ∀ r : SR, r.ok G = true → r.loc.isEx = true → r.acc G false = true →
    bytesAt m0 (r.loc.addr c (G.fsp c)) (r.len.v c) = bytesAt m0' (r.loc.addr c (G.fsp c)) (r.len.v c)

/-- A source reads the entry memory only in an `ok`, readable buffer region. -/
def SrcX : Src → Prop
  | .ext r => r.ok G = true ∧ r.loc.isEx = true ∧ r.acc G false = true
  | .extF r => r.len = .k 32 ∧ r.ok G = true ∧ r.loc.isEx = true ∧ r.acc G false = true
  | _ => True

variable {G}

theorem findSlice_x {Γ : List (Loc × Kd)} {l : Loc} {n : Nat} {s : Src} (h : findSlice Γ l n = some s) : SrcX G s := by
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  split at hp
  · split at hp
    · split at hp
      · simp only [Option.some.injEq] at hp; subst hp; trivial
      · simp at hp
    · simp at hp
  · simp at hp

theorem or_x {o e : Option Src} (ho : ∀ s, o = some s → SrcX G s) (he : ∀ s, e = some s → SrcX G s) {s : Src}
    (h : o.or e = some s) : SrcX G s := by
  cases o with
  | some s' => simp only [Option.some_or, Option.some.injEq] at h; subst h; exact ho _ rfl
  | none => exact he _ (by simpa using h)

theorem inSrc_x {st : St} {σ : List (Reg × SV)} {x : Reg × Nat × In} {s : Src} (h : inSrc G st σ x = some s) :
    SrcX G s := by
  unfold inSrc at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; trivial
    · split at h
      · obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; trivial
      · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; trivial
      · split at h
        · exact findSlice_x h
        · split at h
          · rename_i hc; simp only [Option.some.injEq] at h; subst h
            exact ⟨rfl, hc.2.2.1, hc.2.1, hc.2.2.2⟩
          · simp at h
        · unfold refSrc at h; split at h
          · split at h
            · rename_i hc; simp only [Option.some.injEq] at h; subst h
              exact ⟨hc.2.2.1, rfl, hc.2.2.2⟩
            · simp at h
          · simp at h
        · unfold refSrc at h; split at h
          · split at h
            · rename_i hc; simp only [Option.some.injEq] at h; subst h
              exact ⟨hc.2.2.1, rfl, hc.2.2.2⟩
            · simp at h
          · simp at h
        · simp at h
    · split at h
      · simp at h
      · simp only at h
        split at h
        · refine or_x (fun _ hf => findSlice_x hf) (fun _ he => ?_) h
          split at he
          · rename_i hc; cases he; exact ⟨hc.2.2.1, hc.2.1, hc.2.2.2⟩
          · cases he
        · split at h
          · rename_i hc; cases h; exact ⟨hc.2.2.1, hc.2.1, hc.2.2.2⟩
          · cases h

variable {c : Ctx} {m0 m0' : Mem}

/-- **A source's value** is the same from agreeing entry memories. -/
theorem val_congr (hA : XAgree G c m0 m0') (E : Loc → V) {s : Src} (hs : SrcX G s) :
    s.val G c m0 E = s.val G c m0' E := by
  cases s with
  | ext r => simp only [Src.val, hA r hs.1 hs.2.1 hs.2.2]
  | extF r =>
    obtain ⟨l, n⟩ := r
    obtain ⟨rfl, ho, hx, ha⟩ := hs
    have hb := hA _ ho hx ha
    simp only [XLen.v] at hb
    simp only [Src.val, feVal_bytes hb.symm]
  | _ => rfl

theorem srcs_congr (hA : XAgree G c m0 m0') (E : Loc → V) {st : St} {σ : List (Reg × SV)} {io : Iface} {r : IoR}
    (h : ioRes G st σ io = some r) : r.srcs.map (Src.val G c m0 E) = r.srcs.map (Src.val G c m0' E) := by
  have h2 := mapM_forall₂ (ioRes_parts h).1
  generalize io.ins = l at h2
  generalize r.srcs = l' at h2
  induction l generalizing l' with
  | nil => cases l' with | nil => rfl | cons => exact h2.elim
  | cons x l ih =>
    cases l' with
    | nil => exact h2.elim
    | cons s l' => simp only [List.map_cons, val_congr hA E (inSrc_x h2.1), ih l' h2.2]

theorem ioVs_congr (hA : XAgree G c m0 m0') (st : St) (σ : List (Reg × SV)) (io : Iface) (E : Loc → V) :
    ioVs G c m0 st σ io E = ioVs G c m0' st σ io E := by
  unfold ioVs; split
  · exact srcs_congr hA E (by assumption)
  · rfl

theorem xcallEv_congr (hA : XAgree G c m0 m0') (st : St) (σ : List (Reg × SV)) (io : Iface)
    (sem : List V → List V) (E : Loc → V) :
    xcallEv G c m0 st σ io sem E = xcallEv G c m0' st σ io sem E := by
  unfold xcallEv; split
  · rw [srcs_congr hA E (by assumption)]
  · rfl

variable (semA : A → List V → List V) (semB : Bk → List V → List V)

theorem Op.ev_congr (hA : XAgree G c m0 m0') (st : St) (x : Op A Bk) (E : Loc → V) :
    x.ev cE bE G semA semB c m0 st E = x.ev cE bE G semA semB c m0' st E := by
  cases x with
  | call a as => simp only [Op.ev]; split
                 · rw [srcs_congr hA E (by assumption)]
                 · rfl
  | blk b as => simp only [Op.ev]; split
                · rw [srcs_congr hA E (by assumption)]
                · rfl
  | ldb rd rb ri =>
    simp only [Op.ev]; split
    · split
      · rw [val_congr hA E (findSlice_x (by assumption))]
      · rfl
    · rfl
  | _ => rfl

theorem loopIt_congr {f f' : (Loc → V) → Loc → V} (hf : ∀ E, f E = f' E) (cnt : Nat) :
    ∀ n E, loopIt f cnt n E = loopIt f' cnt n E
  | 0, _ => rfl
  | n + 1, E => by simp only [loopIt, hf, loopIt_congr hf cnt n]

theorem whEv_congr (tb : St → Option St) {eb eb' ek ek' : St → (Loc → V) → Loc → V}
    (hb : ∀ s E, eb s E = eb' s E) (hk : ∀ s E, ek s E = ek' s E) :
    ∀ n st E, whEv tb eb ek n st E = whEv tb eb' ek' n st E
  | 0, _, _ => rfl
  | n + 1, st, E => by
    simp only [whEv, hb]
    split
    · split
      · exact whEv_congr tb hb hk n _ _
      · exact hk _ _
      · rfl
    · rfl

/-- **A program's values** are the same from agreeing entry memories. -/
theorem Prog.ev_congr (hA : XAgree G c m0 m0') :
    ∀ (P : Prog A Bk) st E, P.ev cE bE G semA semB c m0 st E = P.ev cE bE G semA semB c m0' st E
  | .nil, _, _ => rfl
  | .op x k, st, E => by
    simp only [Prog.ev]; split
    · rw [Op.ev_congr cE bE semA semB hA, Prog.ev_congr hA k]
    · rfl
  | .loop cnt n b k, st, E => by
    simp only [Prog.ev]
    rw [loopIt_congr (fun E => Prog.ev_congr hA b _ E), Prog.ev_congr hA k]
  | .sel w i p₀ p₁ k, st, E => by
    simp only [Prog.ev]; split
    · rw [Prog.ev_congr hA p₀, Prog.ev_congr hA p₁, Prog.ev_congr hA k]
    · rfl
  | .xit g s cc sh l k, st, E => by
    simp only [Prog.ev]; split
    · exact Prog.ev_congr hA k _ _
    · rfl
  | .hd b h k, st, E => by
    simp only [Prog.ev]
    rw [Prog.ev_congr hA b]
    split
    · split
      · exact Prog.ev_congr hA k _ _
      · split
        · split
          · rw [Prog.ev_congr hA h, Prog.ev_congr hA k]
          · exact Prog.ev_congr hA h _ _
        · rfl
      · rfl
    · rfl
  | .wh n b k, st, E => by
    simp only [Prog.ev]
    exact whEv_congr _ (fun s E => Prog.ev_congr hA b s E) (fun s E => Prog.ev_congr hA k s E) n st E

end

end M0Crypto.Release.Ed25519CallProg
