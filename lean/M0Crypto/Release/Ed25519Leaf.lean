import M0Crypto.Release.Ed25519Routines
import M0Crypto.Release.Ed25519CallProgAdapt


/-!
# Leaf routines `push {lr}; body; pop {pc}`

A leaf has a straight-line body, public registers `L` (with `sp` its public values), aligned
expressions `al`, and writes `W` and reads `R`, each an expression of the entry registers and the
bytes from it. `leaf_te` is its call lemma with the byte effect of its trace (`Routine.TE`), from
decided checks of the body (`leafOk`: accesses, trace, and the block effect `blkChk ini wo fp`)
and the body's value lemma.
The effect is stated at the state `blkSt` from which the trace of the body is a function of the
public values.
-/

namespace M0Crypto.Release.Ed25519Leaf

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Sym (SExpr alignChkE rgnChk alignChkE_sound rgnChk_sound)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519Routines (hiRegs mem_hiRegs saved0_eq)
open M0Crypto.Release.Ed25519CallProg (CalleeS PubW effOk ioRegs)

/-- `push {lr}`, `body`, `pop {pc}`. -/
def wrap (body : List Instr) : List Instr := .push 0 true :: body ++ [.pop 0 true]

/-- The registers below `sp`. -/
def lowR : List Reg := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- A leaf at `o`, with its entry condition and result. -/
def leafR (o : Nat) (body : List Instr) (W R : List (SExpr × Nat)) (Pre : State → Prop)
    (Post : State → Mem → Word → Prop) : Routine where
  entry := o
  code := [(o, o + seqSize (wrap body))]
  stack := 4
  Pre := fun _ s => Pre s
  wr := fun s => sregions s W
  rd := fun s => sregions s R
  Post := Post
  clob := hiRegs

/-- The public values: the pointers `L`, then `sp`. -/
def leafPub (L : List Reg) (_ : Word) (s : State) : Nat → Word := pubOf ((L ++ [13]).map s.regs)

/-- The state of the body's trace: its pc, the pointers from the public values `P`. -/
def blkSt (L : List Reg) (pc : Word) (P : Nat → Word) : State := regState pc L ((List.range L.length).map P)

/-- **The effect of a leaf**: the bytes `fp` it accesses, `ini` it reads first, `wo` it writes. -/
def leafE (o : Nat) (L : List Reg) (ini wo fp : List (SExpr × Nat)) (base : Word) (P : Nat → Word) : TrP :=
  let t := blkSt L (base + BitVec.ofNat 32 (o + 2)) P
  EffT 4 (InR t fp) (InR t ini) (InR t wo) (P L.length)

/-- The decided checks of a body: it falls through and keeps `sp`, `L` are low registers and the
expressions read only those, its accesses are aligned (`al`), it writes within `W`, reads within
`R`, its trace reads `L`, and its byte effect. -/
def leafOk (body : List Instr) (L : List Reg) (al W R ini wo fp : List (SExpr × Nat)) : Bool :=
  body.all Instr.falls && keepsSp body && seqSize body % 2 == 0 && L.all (·.val < 13) &&
  (al ++ W ++ R).all (·.1.regsIn lowR) && alignChkE al body && rgnChk .write W body &&
  rgnChk .read R body && traceOk body L && blkChk ini wo fp body && wo.all fp.contains

theorem range_pub (L l : List Reg) (f : Reg → Word) :
    (List.range L.length).map (pubOf ((L ++ l).map f)) = L.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, pubOf, List.map_append,
    List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1), List.getElem?_map,
    List.getElem?_eq_getElem h1]
  simp

theorem sregions_eq {s t : State} {rs : List (SExpr × Nat)} (h : ∀ r : Reg, r.val < 13 → t.regs r = s.regs r)
    (hr : rs.all (·.1.regsIn lowR) = true) : sregions t rs = sregions s rs :=
  List.map_congr_left fun r hm => by
    rw [SExpr.denote_regsIn (fun q hq => h q (by revert q; decide)) _ (List.all_eq_true.mp hr r hm)]

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- A block whose accesses lie in expression regions `W`, `R` of its entry state. -/
theorem ReachFT.blockE {base : Word} {Pc Rd Wr Sp : Word → Prop} {s : State} {Q : State → Prop}
    {Ψ : TrP} {G : List Event} (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hseq : seqAt B off is = true)
    (hf : is.all Instr.falls = true) (hk : keepsSp is = true) (hr : InRegion Pc base off (seqSize is))
    (al W R : List (SExpr × Nat)) (ha : alignChkE al is = true) (hwc : rgnChk .write W is = true)
    (hrc : rgnChk .read R is = true) (hal : ∀ r ∈ al, (r.1.denote s).toNat % r.2 = 0)
    (hw : ∀ y, Has (sregions s W) y → Wr y) (hrd : ∀ y, Has (sregions s R) y → Rd y)
    (hsp : Sp (s.regs 13)) (hG : traceAll is s = G) (hq : ReachFT base Pc Rd Wr Sp (execAll is s) Q Ψ) :
    ReachFT base Pc Rd Wr Sp s Q (Tr.cat (Tr.is G) Ψ) := by
  rw [← hG]
  refine ReachT.block hb is off s hpc ho hseq hf (alignChkE_sound hf s hal ha) ?_ hq
  refine BlockOk.mono (fun x e h => ⟨h.1.1, h.1.2.1, h.1.2.2, by rw [h.2]; exact hsp⟩) is s
    (blockOk_keepsSp (p := fun e => Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧
      ∀ y, Reads e.accesses y → Rd y) is s hk fun e he => ⟨?_, ?_, ?_⟩)
  · obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
    rw [hep, hpc, ofNat_add_assoc]; exact hr j hj
  · rintro y ⟨a, ha, hk, j, hj, rfl⟩
    exact hw _ (has_sregions (rgnChk_sound hf s hwc e he a ha hk j hj))
  · rintro y ⟨a, ha, hk, j, hj, rfl⟩
    exact hrd _ (has_sregions (rgnChk_sound hf s hrc e he a ha hk j hj))

/-- **A leaf's call lemma with its effect**, from the checks and the body's value: from the entry
state `s`, whose written regions do not wrap, and the state `t` at the body, with the registers
but `sp`, `pc` and the read bytes of `s`, the body ends with the result. -/
noncomputable def leaf_te {o : Nat} {body : List Instr} {L : List Reg} {al W R ini wo fp : List (SExpr × Nat)}
    {Pre : State → Prop} {Post : State → Mem → Word → Prop}
    (hok : leafOk body L al W R ini wo fp = true) (hseq : seqAt B o (wrap body) = true) (ho : o % 2 = 0)
    (hal : ∀ s, Pre s → ∀ r ∈ al, (r.1.denote s).toNat % r.2 = 0)
    (hex : ∀ s t : State, Pre s → (∀ r ∈ sregions s W, r.a.toNat + r.n ≤ 2 ^ 32) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      (∀ y, Has (sregions s R) y → t.mem y = s.mem y) → Post s (execAll body t).mem ((execAll body t).regs 0)) :
    (leafR o body W R Pre Post).TE (leafPub L) (leafE o L ini wo fp) := by
  simp only [leafOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, hk⟩, hev⟩, hlo⟩, hx⟩, ha⟩, hw⟩, hr⟩, htr⟩, hblk⟩, hwf⟩ := hok
  replace hlo := fun r hr => of_decide_eq_true (List.all_eq_true.mp hlo r hr)
  simp only [List.all_append, Bool.and_eq_true] at hx
  replace hwf := fun x hx => List.contains_iff_mem.mp (List.all_eq_true.mp hwf x hx)
  have e2 : seqSize [Instr.push 0 true] = 2 := rfl
  have hs := hseq
  rw [wrap, ← List.singleton_append, seqAt_append, seqAt_append, seqSize_append, e2, ← Nat.add_assoc] at hs
  simp only [Bool.and_eq_true] at hs
  have hpush : instrAt B o = some (.push 0 true) := instrAt_of_seqAt hs.1.1
  have hpop : instrAt B (o + 2 + seqSize body) = some (.pop 0 true) := instrAt_of_seqAt hs.2
  have hsz : seqSize (wrap body) = seqSize body + 4 := by
    simp [wrap, seqSize, Instr.size]; omega
  have hlen : o + seqSize (wrap body) ≤ BS := by
    have := seqAt_size B o _ hseq
    rw [B_len] at this
    exact this.resolve_right (by simp [wrap])
  rw [hsz] at hlen
  trefine Routine.te_by (fun base s e => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun b P tr h => ?_)
  · generalize hP : leafPub L base s = P
    have q13 : s.regs 13 = P L.length := by subst hP; simp [leafPub, pubOf, List.getD]
    have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
    have hcode : rangesSub [(o, o + 2), (o + 2 + seqSize body, o + 2 + seqSize body + 2)]
        [(o, o + seqSize (wrap body))] = true := by
      simp only [rangesSub, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, hsz]; omega
    trefine ReachFT.push_popK (f := leafR o body W R Pre Post) (mask := 0) (epi := o + 2 + seqSize body)
      (by decide) hpush hpop ho (by omega) (by simp only [leafR]; omega) (by omega) hcode
      (by show 4 * nSaved 0 ≤ 4; decide) e q13 ?_
    intro t tpc t13 tr hm hc
    have tlo : ∀ r : Reg, r.val < 13 → t.regs r = s.regs r := fun r h => tr r (by omega) (by omega)
    have tL : ∀ r ∈ L, t.regs r = s.regs r := fun r hr => tlo r (hlo r hr)
    have hsW := e.sepWr
    trefine ReachFT.blockE hb2 body (o + 2) tpc (by omega) hs.1.2 hf hk
      (PcIn.region (cs := [(o, o + seqSize (wrap body))]) (List.mem_singleton_self _) (by omega)
        (by rw [hsz]; omega)) al W R ha hw hr
      (fun p hp => by
        rw [SExpr.denote_regsIn (fun q hq => tlo q (by revert q; decide)) _ (List.all_eq_true.mp hx.1.1 p hp)]
        exact hal s e.pre p hp)
      ?_ ?_ ⟨4, by simp [leafR], t13⟩
      (traceAll_blockTr (L := L) (vs := (List.range L.length).map P) hf htr tpc (by
        rw [← hP, leafPub, range_pub]; exact List.map_congr_left tL)) ?_
    · rw [sregions_eq tlo hx.1.2]
      exact fun y ⟨r, hr, hy⟩ => ⟨r, List.mem_cons_of_mem _ hr, hy⟩
    · rw [sregions_eq tlo hx.2]
      exact fun y ⟨r, hr, hy⟩ => ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hy⟩
    refine ReachT.done ⟨?_, ?_, fun r h4 h11 _ hK => absurd (mem_hiRegs h4 h11) hK, ?_⟩
    · rw [execAll_pc _ _ hf, tpc, ofNat_add_assoc]; rfl
    · exact execAll_regs_other _ _ 13 (by decide) hk
    · have hsv := saved0_eq (f := leafR o body W R Pre Post) (s := s) rfl
      exact hex s t e.pre (fun p hp => (e.sepWr _ hp _ List.mem_cons_self).1)
        (fun r h13 h15 => tr r h13 h15)
        fun y hy => hm y (Sep.not_has (hsv ▸ e.sepRd) hy)
  · uniq_tac
  · simp only [Tr.cat_is_is, List.append_nil]; exact ⟨_, rfl⟩
  · simp only [Tr.cat_is_is, List.append_nil, List.singleton_append] at h
    subst h
    refine eff_frame (by decide) (fun y ⟨x, hx, hy⟩ => ⟨x, hwf x hx, hy⟩) rfl rfl rfl rfl
      (by simp only [spAfter, Bool.toNat_true, BitVec.sub_add_cancel]) rfl fun sp0 n hroom hn hF => ?_
    exact blk_seg hblk _ (fun y hy => hy) fun y hy hb =>
      above_sub (hF y hy hb) (by have h1 : bitCount 0 + true.toNat = 1 := (by decide); omega)

/-! ## As a callee's effect -/

theorem lookup_zip {r : Reg} : ∀ {L : List Reg} {vs : List Word}, r ∈ L → L.length ≤ vs.length →
    (L.zip vs).lookup r = vs[L.idxOf r]?
  | a :: L, v :: vs, h, hl => by
    by_cases e : r = a
    · subst e; simp
    · simp only [List.zip_cons_cons, List.lookup, List.idxOf_cons, beq_false_of_ne e, beq_false_of_ne (Ne.symm e)]
      exact lookup_zip ((List.mem_cons.1 h).resolve_left e) (by simpa using hl)

theorem blkSt_reg {L : List Reg} {pc : Word} {P : Nat → Word} {r : Reg} (hr : r ∈ L) (h15 : r ≠ 15) :
    (blkSt L pc P).regs r = P (L.idxOf r) := by
  simp only [blkSt, regState, h15, ↓reduceIte]; rw [lookup_zip hr (by simp)]; simp [List.idxOf_lt_length_of_mem hr]

/-- The interface registers of `s` are leaf registers `L` at their positions among its public
values, and `sp` follows them. -/
def regsOk (s : CalleeS) (L : List Reg) : Bool :=
  (ioRegs s.io).all (fun r => r ∈ L && r != 15 && s.pubs.idxOf (.r r) == L.idxOf r) &&
    s.pubs.idxOf (.r 13) == L.length

/-- **An effect at `blkSt` is its callee's**, by the decided `effOk` and `regsOk`, for any frame
`stk` within the callee's stack. -/
theorem blk_eff {stk : Nat} {pc : Word} {L : List Reg} {ini wo fp : List (SExpr × Nat)} {s : CalleeS}
    {base : Word} {p : Nat → Word} {tr : List Event}
    (h : EffT stk (fun y => Has [codeR base] y ∨ InR (blkSt L pc p) fp y)
      (fun y => Has [codeR base] y ∨ InR (blkSt L pc p) ini y) (InR (blkSt L pc p) wo) (p L.length) tr)
    (hc : effOk s.io fp ini wo = true) (hr : regsOk s L = true) (hs : stk ≤ s.stack) : s.Eff p base tr := by
  simp only [regsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
  refine CalleeS.eff_of (by unfold CalleeS.reg; rw [hr.2]; exact h) hc hs fun r m => ?_
  obtain ⟨⟨hL, h15⟩, hi⟩ := hr.1 r m
  rw [blkSt_reg hL h15]; unfold CalleeS.reg; rw [hi]

/-- **A leaf's effect is its callee's**, by the decided `effOk` and `regsOk`. -/
theorem leaf_eff {o : Nat} {L : List Reg} {ini wo fp : List (SExpr × Nat)} {s : CalleeS} {base : Word}
    {p : Nat → Word} {tr : List Event} (h : leafE o L ini wo fp base p tr) (hc : effOk s.io fp ini wo = true)
    (hr : regsOk s L = true) (hs : 4 ≤ s.stack) : s.Eff p base tr :=
  blk_eff (Ed25519CallProg.EffT.mono h (Nat.le_refl _) (fun _ => .inr) (fun _ => .inr) fun _ h => h) hc hr hs

end M0Crypto.Release.Ed25519Leaf
