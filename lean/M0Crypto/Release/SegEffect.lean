import M0Crypto.Release.StackEffectGP
import M0Crypto.Release.RoutineLoopFar

/-!
# Framed routines of segments

A routine `push {mask, lr}; sub sp, #4k`, a body, `add sp, #4k; pop {mask, pc}` has its `TE` with
the byte effect `EffT` from `frame_te`: the body's `ReachFT` (`ReachFT.segs`, `segLoop`,
`segLoopFar`) and a `GP` of its trace from the written set `U` of the caller plus the saved words,
adding the bytes `Wd` it writes.

The `GP` of segments is `segsTr_gp`: pass `i` of segment `k` reads below the entry only bytes of
`R` or of the segments before it (`WS`) and writes there only at or above SP (`PassOk`, at the
atoms' values `vs k i`). The bytes the segments write are `WS`. `inRD_wins` places a block's
regions in windows from its atoms (`winsChk`, decided). A far loop's branches access nothing
(`farPass_gp`). Each trace condition is met by some trace (`ex_segsTr`).

Blocks are split before a shift by a register: `nf` keeps the carry argument of `lsrR` in raw
`awc` form, so a block whose effect writes that carry starts at the shift.
-/

namespace M0Crypto.Release.StackEffect

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
open M0Crypto.Release.Routine (segsTr sloopTr blockTrE addrE)

variable {sp0 : Word} {n : Nat}

theorem SIR.mono {sp : Word} {R R' : Word → Prop} {q : Ef} (hq : SIR sp0 sp R q) (h : ∀ y, R' y → R y) :
    SIR sp0 sp R' q := ⟨hq.hs, fun y hy => hq.r y (h y hy), hq.ab⟩

theorem GP.post {I J J' : Ef → Prop} {Φ : TrP} (g : GP sp0 n I Φ J) (h : ∀ q, J q → J' q) :
    GP sp0 n I Φ J' := fun q hq tr ht => let ⟨a, b⟩ := g q hq tr ht; ⟨a, h _ b⟩

/-! ## Passes of segments -/

/-- The passes of a segment: `m` for a loop, else one. -/
def segN (s : Routine.Seg) (m : Nat) : Nat := if s.br.isSome then m else 1

/-- The offset of segment `k` of `ss` from `o`. -/
def segPc (o : Nat) (ss : List Routine.Seg) (k : Nat) : Nat := o + Routine.segsSize (ss.take k)

/-- The blocks have their decided effects. -/
def segsEffOk (ss : List Routine.Seg) : Bool := ss.all fun s => blkChk s.rg s.wg (s.rg ++ s.wg) s.g

/-- **A pass**: the bytes of its block's regions under `d`, its atoms' values: those it reads below
the entry lie in `R`, those it writes below the entry at or above SP. -/
structure PassOk (sp0 : Word) (n : Nat) (sp : Word) (R : Word → Prop) (s : Routine.Seg) (d : SExpr → Word) :
    Prop where
  rd : ∀ y, InRD d s.rg y → BelowEntry sp0 n y → R y
  wr : ∀ y, InRD d s.wg y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y

theorem PassOk.mono {sp : Word} {R R' : Word → Prop} {s : Routine.Seg} {d : SExpr → Word}
    (h : PassOk sp0 n sp R s d) (hR : ∀ y, R y → BelowEntry sp0 n y → R' y) : PassOk sp0 n sp R' s d :=
  ⟨fun y hy hb => hR y (h.rd y hy hb) hb, h.wr⟩

/-- The bytes pass `i` of segment `s`, the `k`th of `ss` from `o`, writes. -/
def segW (base : Word) (o : Nat) (ss : List Routine.Seg) (vs : Nat → Nat → List Word) (k i : Nat)
    (s : Routine.Seg) : Word → Prop :=
  InRD (addrE (base + BitVec.ofNat 32 (segPc o ss k)) s.As (vs k i)) s.wg

/-- The bytes the segments before the `K`th write. -/
def WS (base : Word) (o : Nat) (ss : List Routine.Seg) (vs : Nat → Nat → List Word) (nn : Nat → Nat)
    (K : Nat) (y : Word) : Prop :=
  ∃ k < K, ∃ s i, ss[k]? = some s ∧ i < segN s (nn k) ∧ segW base o ss vs k i s y

theorem segPc_succ (o : Nat) (s : Routine.Seg) (ss : List Routine.Seg) (k : Nat) :
    segPc o (s :: ss) (k + 1) = segPc (o + s.size) ss k := by
  simp only [segPc, List.take_succ_cons, Routine.segsSize, Nat.add_assoc]

theorem ws_succ {base : Word} {o : Nat} {s : Routine.Seg} {ss : List Routine.Seg} {vs : Nat → Nat → List Word}
    {nn : Nat → Nat} {K : Nat} {y : Word} : WS base o (s :: ss) vs nn (K + 1) y ↔
      (∃ i < segN s (nn 0), segW base o (s :: ss) vs 0 i s y) ∨
      WS base (o + s.size) ss (fun k => vs (k + 1)) (fun k => nn (k + 1)) K y := by
  have e := segPc_succ o s ss
  constructor
  · rintro ⟨_ | k, hk, s', i, h1, h2, h3⟩
    · cases h1; exact .inl ⟨i, h2, h3⟩
    · exact .inr ⟨k, by omega, s', i, h1, h2, by simpa only [segW, e] using h3⟩
  · rintro (⟨i, h2, h3⟩ | ⟨k, hk, s', i, h1, h2, h3⟩)
    · exact ⟨0, by omega, s, i, rfl, h2, h3⟩
    · exact ⟨k + 1, by omega, s', i, h1, h2, by simpa only [segW, e] using h3⟩

/-- Every region of `rs` lies in a window `(i, N)` of `W`: the `N` bytes from atom `i`. -/
def winsChk (As : List SExpr) (W : List (Nat × Nat)) (rs : List (SExpr × Nat)) : Bool :=
  rs.all fun r => match atomOf As r.1 with
    | some (i, d) => W.any fun w => w.1 == i && decide (d.toNat + r.2 ≤ w.2)
    | none => false

/-- **The windows of a block's regions** at its atoms' values. -/
theorem inRD_wins {pc y : Word} {As : List SExpr} {vs : List Word} {rs : List (SExpr × Nat)} {W : List (Nat × Nat)}
    (hl : vs.length = As.length) (hc : winsChk As W rs = true) (hy : InRD (addrE pc As vs) rs y) :
    ∃ w ∈ W, ∃ v, vs[w.1]? = some v ∧ Region v w.2 y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  have h := List.all_eq_true.mp hc r hr
  revert h; split
  · next i d ha =>
    intro h
    obtain ⟨w, hw, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨v, hv, e⟩ := addrE_atom (pc := pc) hl ha
    exact ⟨w, hw, v, h.1 ▸ hv, by rw [e]; simp only [Region]; bv_omega⟩
  · simp

/-- **A pass from windows**: its reads lie in the windows `Wr` of its atoms, its writes in `Ww`. -/
theorem pass_of {sp : Word} {R : Word → Prop} {s : Routine.Seg} {pc : Word} {vs : List Word}
    {Wr Ww : List (Nat × Nat)} (hl : vs.length = s.As.length) (hr : winsChk s.As Wr s.rg = true)
    (hw : winsChk s.As Ww s.wg = true)
    (h1 : ∀ w ∈ Wr, ∀ v, vs[w.1]? = some v → ∀ y, Region v w.2 y → BelowEntry sp0 n y → R y)
    (h2 : ∀ w ∈ Ww, ∀ v, vs[w.1]? = some v → ∀ y, Region v w.2 y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    PassOk sp0 n sp R s (addrE pc s.As vs) :=
  ⟨fun y hy => let ⟨w, hw, v, hv, h⟩ := inRD_wins hl hr hy; h1 w hw v hv y h,
   fun y hy => let ⟨w, hw, v, hv, h⟩ := inRD_wins hl hw hy; h2 w hw v hv y h⟩

/-- The goals of `pass_of` per window, at the atoms' values. -/
macro "pass_tac" " [" l:term,* "]" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, forall_eq', Nat.reduceAdd,
    Nat.reduceEqDiff, ↓reduceIte, $[$l:term],*]))

/-- **One pass** of a block from its atoms' values. -/
theorem sir_pass {s : Routine.Seg} {pc : Word} {vs : List Word} {sp : Word} {R : Word → Prop}
    (hb : blkChk s.rg s.wg (s.rg ++ s.wg) s.g = true) (h : PassOk sp0 n sp R s (addrE pc s.As vs)) :
    GP sp0 n (SIR sp0 sp R) (Tr.is (blockTrE s.g pc s.As vs))
      (SIR sp0 sp fun y => R y ∨ InRD (addrE pc s.As vs) s.wg y ∧ BelowEntry sp0 n y) :=
  sir_segR (fun hR => blkE_seg hb (fun _ h => h) fun y hy hb' =>
    (inR_append.mp hy).elim (fun h' => hR y (h.rd y h' hb')) fun h' => h.wr y h' hb') h.rd fun _ h => h

/-- **The segments of `segsTr`** from `SIR sp R`, then `Ψ` with the bytes they write. -/
theorem segsTr_gp (base : Word) {sp : Word} {J : Ef → Prop} {Ψ : TrP} :
    ∀ (o : Nat) (ss : List Routine.Seg) (vs : Nat → Nat → List Word) (nn : Nat → Nat) (R : Word → Prop),
    segsEffOk ss = true →
    (∀ k s i, ss[k]? = some s → i < segN s (nn k) →
      PassOk sp0 n sp (fun y => R y ∨ WS base o ss vs nn k y) s
        (addrE (base + BitVec.ofNat 32 (segPc o ss k)) s.As (vs k i))) →
    GP sp0 n (SIR sp0 sp fun y => R y ∨ WS base o ss vs nn ss.length y ∧ BelowEntry sp0 n y) Ψ J →
    GP sp0 n (SIR sp0 sp R) (segsTr base o ss vs nn Ψ) J
  | _, [], _, _, _, _, _, h => GP.pre (fun _ hq => hq.mono fun _ h => h.elim id fun ⟨⟨_, hk, _⟩, _⟩ =>
      absurd hk (Nat.not_lt_zero _)) h
  | o, s :: ss, vs, nn, R, hok, hp, h => by
    simp only [segsEffOk, List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hb, hok⟩ := hok
    have no0 : ∀ y, R y ∨ WS base o (s :: ss) vs nn 0 y → R y := fun _ h => h.elim id fun ⟨_, hk, _⟩ =>
      absurd hk (Nat.not_lt_zero _)
    have IH := segsTr_gp base (o + s.size) ss (fun k => vs (k + 1)) (fun k => nn (k + 1))
      (fun y => R y ∨ (∃ i < segN s (nn 0), segW base o (s :: ss) vs 0 i s y) ∧ BelowEntry sp0 n y) hok
      (fun k s' i hk hi => (segPc_succ o s ss k ▸ hp (k + 1) s' i hk hi).mono fun y h hb' =>
        h.elim (.inl <| .inl ·) fun h => (ws_succ.mp h).elim (fun h => .inl (.inr ⟨h, hb'⟩)) .inr)
      (GP.pre (fun _ hq => hq.mono fun y h => h.elim (.inl <| .inl ·) fun ⟨h, hb'⟩ => (ws_succ.mp h).elim
        (fun h => .inl (.inr ⟨h, hb'⟩)) fun h => .inr ⟨h, hb'⟩) h)
    unfold segsTr
    cases hbr : s.br with
    | none =>
      have h1 : segN s (nn 0) = 1 := by simp [segN, hbr]
      refine GP.cat (sir_pass hb ((hp 0 s 0 rfl (by omega)).mono fun y h _ => no0 y h))
        (GP.pre (fun _ hq => hq.mono fun y h => ?_) IH)
      rcases h with h | ⟨⟨i, hi, h⟩, hb'⟩
      · exact .inl h
      · exact .inr ⟨by rwa [show i = 0 by omega] at h, hb'⟩
    | some c =>
      have hn : segN s (nn 0) = nn 0 := by simp [segN, hbr]
      refine GP.pre (fun _ hq => hq.mono fun y h => h.elim id fun ⟨⟨_, hk, _⟩, _⟩ => absurd hk (Nat.not_lt_zero _))
        (GP.repI (I := fun i => SIR sp0 sp fun y => R y ∨
          (∃ i' < i, segW base o (s :: ss) vs 0 i' s y) ∧ BelowEntry sp0 n y) (nn 0) 0 (fun i _ hi => ?_)
          (GP.pre (fun _ hq => hq.mono fun y h => h.imp_right fun ⟨⟨i, hi, h⟩, hb'⟩ =>
            ⟨⟨i, by rw [hn] at hi; omega, h⟩, hb'⟩) IH))
      unfold sloopTr
      refine GP.cat (GP.cat ((sir_pass hb ((hp 0 s i rfl (by omega)).mono fun y h hb' =>
        .inl (no0 y h))).post fun _ hq => hq.mono fun y h => ?_) (GP.nil fun _ h => h)) (sir_quietC rfl rfl rfl)
      rcases h with h | ⟨⟨i', hi', h⟩, hb'⟩
      · exact .inl (.inl h)
      · by_cases e : i' = i
        · exact .inr ⟨e ▸ h, hb'⟩
        · exact .inl (.inr ⟨⟨i', by omega, h⟩, hb'⟩)

/-- A pass of a far loop: the body, then its branches. -/
theorem farPass_gp {base : Word} {ob : Nat} {c : BitVec 4} {i8 : BitVec 8} {i11 : BitVec 11} {Φb : Nat → TrP}
    {m j : Nat} {sp : Word} {R R' : Word → Prop} (h : GP sp0 n (SIR sp0 sp R) (Φb j) (SIR sp0 sp R')) :
    GP sp0 n (SIR sp0 sp R) (Routine.farPass base ob c i8 i11 Φb m j) (SIR sp0 sp R') := by
  refine GP.cat h (GP.cons (sir_quietC rfl rfl rfl) ?_)
  split
  · exact GP.cons (sir_quietC rfl rfl rfl) (GP.nil fun _ h => h)
  · exact GP.nil fun _ h => h

/-! ## Traces exist -/

theorem ex_cat {Φ Ψ : TrP} (h1 : ∃ a, Φ a) (h2 : ∃ b, Ψ b) : ∃ tr, Tr.cat Φ Ψ tr :=
  let ⟨a, ha⟩ := h1; let ⟨b, hb⟩ := h2; ⟨a ++ b, a, b, rfl, ha, hb⟩

theorem ex_rep {Φ : Nat → TrP} {Ψ : TrP} (h : ∀ j, ∃ a, Φ j a) (hΨ : ∃ b, Ψ b) :
    ∀ j k, ∃ tr, Tr.rep Φ j k Ψ tr
  | _, 0 => hΨ
  | j, k + 1 => ex_cat (h j) (ex_rep h hΨ (j + 1) k)

theorem ex_segsTr (base : Word) : ∀ (o : Nat) (ss : List Routine.Seg) vs nn {Ψ : TrP}, (∃ b, Ψ b) →
    ∃ tr, segsTr base o ss vs nn Ψ tr
  | _, [], _, _, _, h => h
  | o, s :: ss, vs, nn, _, h => by
    unfold segsTr
    split
    · exact ex_cat ⟨_, rfl⟩ (ex_segsTr base _ ss _ _ h)
    · refine ex_rep (fun _ => ?_) (ex_segsTr base _ ss _ _ h) _ _
      unfold sloopTr; exact ex_cat (ex_cat ⟨_, rfl⟩ ⟨_, rfl⟩) ⟨_, rfl⟩

/-! ## The frame -/

section frame
open M0Crypto.Release M0Crypto.Release.Routine M0Crypto.Release.Footprint
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The trace of a framed routine at `o` with epilogue at `epi` and entry SP `sp`, around `Ψ`. -/
def frameTr (base : Word) (o epi : Nat) (mask : BitVec 8) (k : Nat) (sp : Word) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .push mask true,
      wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
    (Tr.cat (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + 2), .subSp (BitVec.ofNat 7 k), []⟩])
        (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 epi, .addSp (BitVec.ofNat 7 k), []⟩])))
      (Tr.is [⟨base + BitVec.ofNat 32 (epi + 2), .pop mask true,
        wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))

/-- **A framed routine with its byte effect**: the frame at the entry and at `epi`, the body's
`ReachFT` from the state after `sub sp`, its trace `Ψ` unique and inhabited, and a `GP` of `Ψ` at
the lowered SP adding the bytes `Wd`. The entry SP is `spP` of the public values. -/
noncomputable def frame_te {α : Type} {f : Routine} {pub : Word → State → α} {mask : BitVec 8}
    {k epi : Nat} {Ψ : Word → α → TrP} {Fp Rq Wd : Word → α → Word → Prop} {spP : α → Word}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hen : seqAt B f.entry [.push mask true, .subSp (BitVec.ofNat 7 k)] = true)
    (hpo : seqAt B epi [.addSp (BitVec.ofNat 7 k), .pop mask true] = true)
    (hcode : rangesSub [(f.entry, f.entry + 4), (epi, epi + 4)] f.code = true)
    (hchk : f.entry % 2 = 0 ∧ epi % 2 = 0 ∧ epi + 4 ≤ BS ∧ f.entry + 4 ≤ BS ∧ k < 128 ∧
      4 * nSaved mask + 4 * k ≤ f.stack)
    (hsp : ∀ base s, spP (pub base s) = s.regs 13)
    (body : ∀ base s, f.Entry base s → Caller base (s.regs 13) f.stack (lowWin f mask s :: f.wr s) →
      ∀ t : State, t.pc = base + BitVec.ofNat 32 (f.entry + 4) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ f.clob → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) (Ψ base (pub base s)))
    (hu : ∀ b p, Tr.Uniq (Ψ b p)) (hx : ∀ b p, ∃ tr, Ψ b p tr) (hWF : ∀ b p y, Wd b p y → Fp b p y)
    (he : ∀ b p sp0 n (U : Word → Prop), (sp0 - spP p).toNat + f.stack ≤ n → n < 2 ^ 32 →
      (∀ y, Fp b p y → BelowEntry sp0 n y → AtOrAboveSp sp0 (spP p) y) →
      (∀ y, Rq b p y → BelowEntry sp0 n y → U y) →
      GP sp0 n (SIR sp0 (spP p - BitVec.ofNat 32 (4 * nSaved mask + 4 * k))
        (fun y => U y ∨ Region (spP p - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)) (Ψ b p)
        (SIR sp0 (spP p - BitVec.ofNat 32 (4 * nSaved mask + 4 * k)) fun y =>
          (U y ∨ Region (spP p - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) ∨
            Wd b p y ∧ BelowEntry sp0 n y)) :
    f.TE pub fun b p => EffT f.stack (Fp b p) (Rq b p) (Wd b p) (spP p) := by
  obtain ⟨he2, hep2, hepi, hent, hk, hst⟩ := hchk
  have i0 := instrAt_of_seqAt hen
  have i2 := instrAt_of_seqAt hpo
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq] at hen hpo
  have i1 : instrAt B (f.entry + 2) = some (.subSp (BitVec.ofNat 7 k)) := hen.2.1.1
  have i3 : instrAt B (epi + 2) = some (.pop mask true) := hpo.2.1.1
  refine Routine.te_by (Φ := fun b p => frameTr b f.entry epi mask k (spP p) (Ψ b p))
    (fun base s e => ?_) (fun b p => ?_) (fun b p => ex_cat ⟨_, rfl⟩ (ex_cat (ex_cat ⟨_, rfl⟩
      (ex_cat (hx b p) ⟨_, rfl⟩)) ⟨_, rfl⟩)) (fun b p tr h => ?_)
  · exact ReachFT.frameK hmask i0 i1 i2 i3 he2 hep2 hepi hent hcode hk hst e (hsp base s).symm
      (body base s e (Caller.of_entry e))
  · exact Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_cat (Tr.uniq_is _)
      (Tr.uniq_cat (hu b p) (Tr.uniq_is _))) (Tr.uniq_is _))
  · refine effT_of_gp fun sp0 n U hroom hn hF hR => GP.is_of (frameK_gp (R2 := fun y =>
      (U y ∨ Region (spP p - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) ∨ Wd b p y ∧ BelowEntry sp0 n y)
      (R' := fun y => U y ∨ Wd b p y ∧ BelowEntry sp0 n y) hk (by omega) ?_
      (fun y h => .inl (.inr h)) (fun y h => h.elim .inl fun h => .inr ⟨hF y (hWF b p y h.1) h.2, .inr h⟩)
      (fun y h => .inl (.inl h))) h
    rw [sub_sub_ofNat]; exact he b p sp0 n U hroom hn hF hR

end frame

end M0Crypto.Release.StackEffect
