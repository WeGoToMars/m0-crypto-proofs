import M0Crypto.Release.Routine

set_option linter.unusedSimpArgs false

/-!
# Blocks with footprints in their entry state

`ReachFT.glue` checks a block's accesses against regions `(r, k, n)`, an entry register plus a
constant. A block that loads a pointer from memory and then accesses through it must be cut after
the load, and every cut is one more glue piece with its own side conditions. Here a region is
`(e, n)`: the `n` bytes from `e`, a symbolic expression of the block's entry state (a register, a
slot load, a sum of them). A run of glue pieces is then one block, `ReachFT.sglue`, with one set of
side conditions on the regions' values at entry (`SGlueSides`). An access lies in a region when the
two addresses have the same base after `norm` and `split` and its constant offset lies within.

The block's trace is `blockTrE` of the values of its address bases (the atoms `As`): a
constant-time proof states those values, not the trace (`traceAll_blockTrE`).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release (regState)

/-- The access at `a`, `w` bytes, lies in the `r.2` bytes from `r.1`. -/
def inRgn (a : SExpr) (w : Nat) (r : SExpr × Nat) : Bool :=
  (split (norm a)).1 == (split (norm r.1)).1 &&
    decide (((split (norm a)).2 - (split (norm r.1)).2).toNat + w ≤ r.2)

/-- An access is aligned: a literal (`accAligned []`), or at a multiple of its width from an
expression `r.1` aligned to `r.2`. -/
def accAlignedE (al : List (SExpr × Nat)) (a : SAccess) : Bool :=
  accAligned [] a || ((a.width == 1 || a.width == 2 || a.width == 4) && al.any fun r =>
    (split (norm a.addr)).1 == (split (norm r.1)).1 && r.2 % a.width == 0 &&
      ((split (norm a.addr)).2 - (split (norm r.1)).2).toNat % a.width == 0)

def alignChkE (al : List (SExpr × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all (accAlignedE al)

/-- Every access of kind `k` lies in a region of `rg`. -/
def rgnChk (k : Kind) (rg : List (SExpr × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all fun a => a.kind != k || rg.any (inRgn a.addr a.width)

theorem base_split (s : State) (e : SExpr) :
    (split (norm e)).1.denote s + (split (norm e)).2 = e.denote s := by
  rw [split_sound, norm_sound]

theorem inRgn_sound (s : State) {a : SExpr} {w : Nat} {r : SExpr × Nat} (h : inRgn a w r = true)
    {k : Nat} (hk : k < w) :
    ∃ o < r.2, a.denote s + BitVec.ofNat 32 k = r.1.denote s + BitVec.ofNat 32 o := by
  simp only [inRgn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨((split (norm a)).2 - (split (norm r.1)).2).toNat + k, by omega, ?_⟩
  rw [← base_split s a, ← base_split s r.1, h.1, BitVec.ofNat_add, BitVec.ofNat_toNat]
  exact add_sub_rearr _ _ _ _

theorem accAlignedE_sound (s : State) {al : List (SExpr × Nat)}
    (hal : ∀ r ∈ al, (r.1.denote s).toNat % r.2 = 0) (a : SAccess) (h : accAlignedE al a = true) :
    (a.denote s).aligned = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact accAligned_sound s [] (by simp) a h
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hw, r, hr, ⟨hb, hrw⟩, hk⟩ := h
  have hdiv : a.width ∣ 2 ^ 32 := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with (h3 | h3) | h3 <;> rw [h3] <;> decide
  simp only [Access.aligned, SAccess.denote, beq_iff_eq]
  rw [← base_split s a.addr, hb, ← BitVec.add_zero (_ + (split (norm a.addr)).2),
    add_sub_rearr _ (split (norm r.1)).2, BitVec.add_zero, base_split]
  exact add_toNat_mod_of_dvd _ _ _ hdiv (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans
    (Nat.dvd_of_mod_eq_zero hrw) (Nat.dvd_of_mod_eq_zero (hal r hr)))) hk

theorem alignChkE_sound {al : List (SExpr × Nat)} {is : List Instr} (hf : is.all Instr.falls = true)
    (s : State) (hal : ∀ r ∈ al, (r.1.denote s).toNat % r.2 = 0) (h : alignChkE al is = true) :
    alignedAll is s = true := by
  have hA := alignedAll_sym is (sound_all hf) s SState.init
  rw [SState.init_denote] at hA
  rw [hA]
  simp only [alignChkE, List.all_eq_true] at h ⊢
  exact fun e he a ha => accAlignedE_sound s hal a (h e he a ha)

/-- Each byte of an access of kind `k` lies in a region of `rg` at the block's entry. -/
theorem rgnChk_sound {k : Kind} {rg : List (SExpr × Nat)} {is : List Instr}
    (hf : is.all Instr.falls = true) (s : State) (h : rgnChk k rg is = true) :
    ∀ e ∈ traceAll is s, ∀ a ∈ e.accesses, a.kind = k → ∀ j < a.width,
      ∃ r ∈ rg, ∃ o < r.2, a.addr + BitVec.ofNat 32 j = r.1.denote s + BitVec.ofNat 32 o := by
  have hT := symTrace_sound is (sound_all hf) s SState.init
  rw [SState.init_denote] at hT
  intro e he a ha hk j hj
  rw [← hT, List.mem_map] at he
  obtain ⟨⟨pc, i, acc⟩, hse, rfl⟩ := he
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp h _ hse) a' ha'
  simp only [SAccess.denote] at hk hj ⊢
  simp only [hk, bne_self_eq_false, Bool.false_or, List.any_eq_true] at h2
  obtain ⟨r, hr, hin⟩ := h2
  exact ⟨r, hr, inRgn_sound s hin hj⟩

theorem zip_map_self {α : Type} (f : SExpr → α) :
    ∀ (As : List SExpr), ∀ p ∈ As.zip (As.map f), p.2 = f p.1
  | [], _, h => nomatch h
  | x :: As, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact zip_map_self f As p h

theorem mem_zip_map_self {α : Type} (f : SExpr → α) {x : SExpr} :
    ∀ {As : List SExpr}, x ∈ As → (x, f x) ∈ As.zip (As.map f)
  | y :: As, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_map_self f h)

end M0Crypto.Sym

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The regions `(e, n)` at the state `s`. -/
def sregions (s : State) (rg : List (SExpr × Nat)) : List Rgn := rg.map fun r => ⟨r.1.denote s, r.2⟩

theorem has_sregions {s : State} {rg : List (SExpr × Nat)} {y : Word}
    (h : ∃ r ∈ rg, ∃ o < r.2, y = r.1.denote s + BitVec.ofNat 32 o) : Has (sregions s rg) y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  exact ⟨⟨r.1.denote s, r.2⟩, List.mem_map_of_mem hr, o, ho, rfl⟩

/-- The side conditions of a block at `t`: its aligned expressions are aligned and its regions
lie in the caller's footprints. -/
def SGlueSides (t : State) (Rc Wc : List Rgn) (al wg rg : List (SExpr × Nat)) : Prop :=
  (∀ r ∈ al, (r.1.denote t).toNat % r.2 = 0) ∧ Sub (sregions t wg) Wc ∧ Sub (sregions t rg) Rc

/-- The decided checks of a block `g` at `o`: it falls through, keeps `sp`, lies in the caller's
code `cs`, and has its accesses aligned (`al`) and its writes in `wg`, its reads in `rg`. -/
def sglueOk (cs : List (Nat × Nat)) (g : List Instr) (o d N : Nat) (al wg rg : List (SExpr × Nat)) :
    Bool :=
  o % 2 == 0 && g.all Instr.falls && keepsSp g && alignChkE al g && rgnChk .write wg g &&
  rgnChk .read rg g && rangesSub [(o, o + seqSize g)] cs && decide (d ≤ N)

/-- The frame of a checked block: memory outside its write regions is unchanged. -/
theorem execAll_memEqE {g : List Instr} {wg : List (SExpr × Nat)} (s : State)
    (hf : g.all Instr.falls = true) (hw : rgnChk .write wg g = true) :
    MemEq (sregions s wg) s.mem (execAll g s).mem := fun y hy =>
  execAll_mem_other g s y fun e he ⟨a, ha, hk, j, hj, hy'⟩ =>
    hy (has_sregions (hy' ▸ rgnChk_sound hf s hw e he a ha hk j hj))

/-- **A block** whose footprints are expressions of its entry state, at the caller's `sp`
offset `d`, with trace `G`. -/
theorem ReachFT.sglue {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {t : State} {Q : State → Prop} {Ψ : TrP} {G : List Event} {o d : Nat}
    (F : Caller base sp0 N Wc) (g : List Instr) (al wg rg : List (SExpr × Nat))
    (hseq : seqAt B o g = true) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SGlueSides t Rc Wc al wg rg) (hG : traceAll g t = G)
    (k : (execAll g t).pc = base + BitVec.ofNat 32 (o + seqSize g) →
      (execAll g t).regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt (execAll g t).mem base B →
      MemEq (sregions t wg) t.mem (execAll g t).mem →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) (execAll g t) Q Ψ)
    (hok : sglueOk cs g o d N al wg rg = true) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) Ψ) := by
  simp only [sglueOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho, hfa, hks, ha, hwc, hrc, hcs, hd⟩ := hok
  obtain ⟨hal, hw, hrd⟩ := hs
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have hm := execAll_memEqE t hfa hwc
  rw [← hG]
  refine ReachT.block hb2 g o t hpc ho hseq hfa (alignChkE_sound hfa t hal ha) ?_ (k
    (by rw [execAll_pc _ _ hfa, hpc, ofNat_add_assoc]) (by rw [execAll_regs_other g t 13 (by decide) hks, h13])
    (CodeAt.of_memEq hcode hm (hw.sep F.codeW.symm).symm) hm)
  refine BlockOk.mono (fun x e h => ⟨h.1.1, h.1.2.1, h.1.2.2, by rw [h.2, h13]; exact ⟨d, hd, rfl⟩⟩) g t
    (blockOk_keepsSp (p := fun e => PcIn base cs e.pc ∧ (∀ y, Writes e.accesses y → Has Wc y) ∧
      ∀ y, Reads e.accesses y → Has Rc y) g t hks fun e he => ⟨?_, ?_, ?_⟩)
  · obtain ⟨j, hj, hep⟩ := traceAll_pc_offset g t hfa e he
    rw [hep, hpc, ofNat_add_assoc]
    exact PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega))
  · rintro y ⟨a, ha, hk, j, hj, rfl⟩
    exact hw.has (has_sregions (rgnChk_sound hfa t hwc e he a ha hk j hj))
  · rintro y ⟨a, ha, hk, j, hj, rfl⟩
    exact hrd.has (has_sregions (rgnChk_sound hfa t hrc e he a ha hk j hj))

/-- `glue_tac [h, …]` closes the `GlueSides` or `SGlueSides` of a block: its regions at the entry
state, rewritten by `h, …` (the values of registers and atoms), each part by `fp_tac`. It does
not run the block. -/
macro "glue_tac" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  ((simp only [GlueSides, SGlueSides, regions, sregions, List.map_cons, List.map_nil,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, SExpr.denote, and_true,
    Routine.win, codeR, BitVec.add_zero, $ts,*]); repeat' apply And.intro) <;> fp_tac)

/-- `tr_block L pc [h, …]` proves `traceAll g t = blockTr g pc L vs` for a block `g` whose
addresses read the registers `L`: the values `vs` come from `h, …`. -/
macro "tr_block " L:term:max pc:term:max " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : term =>
  `(traceAll_blockTr (L := $L) (by decide +kernel) (by decide +kernel) $pc
    (by simp only [List.map_cons, List.map_nil, $ts,*] <;> rfl))

/-! ## The trace from the atoms -/

/-- The pcs read only the pc, and each access address is pc-relative or an atom of `As` plus a
constant. -/
def traceOkE (is : List Instr) (As : List SExpr) : Bool :=
  (symTrace is SState.init).all fun e => e.1.regsIn [15] && e.2.2.all fun a =>
    a.addr.regsIn [15] || As.any fun x => (split (norm x)).1 == (split (norm a.addr)).1

/-- The value of a base: an atom's value less its offset, or else the base at the pc. -/
def baseE (pc : Word) (As : List SExpr) (vs : List Word) (b : SExpr) : Word :=
  match (As.zip vs).find? fun p => (split (norm p.1)).1 == b with
  | some p => p.2 - (split (norm p.1)).2
  | none => b.denote (regState pc [] [])

/-- An address from the pc `pc` and the values `vs` of the atoms `As`: its base's value plus its
offset. -/
def addrE (pc : Word) (As : List SExpr) (vs : List Word) (e : SExpr) : Word :=
  baseE pc As vs (split (norm e)).1 + (split (norm e)).2

/-- The trace of the block `is` from pc `pc` with the atoms `As` at the values `vs`. -/
def blockTrE (is : List Instr) (pc : Word) (As : List SExpr) (vs : List Word) : List Event :=
  (symTrace is SState.init).map fun e => ⟨e.1.denote (regState pc [] []), e.2.1,
    e.2.2.map fun a => ⟨a.kind, addrE pc As vs a.addr, a.width⟩⟩

/-- **A block's trace from its atoms**: from `s` with pc `pc` and the atoms `As` at `vs`. -/
theorem traceAll_blockTrE {is : List Instr} {As : List SExpr} {s : State} {pc : Word}
    {vs : List Word} (hf : is.all Instr.falls = true) (hok : traceOkE is As = true)
    (hpc : s.pc = pc) (hv : As.map (·.denote s) = vs) : traceAll is s = blockTrE is pc As vs := by
  have hag := regState_agree (s := s) (L := []) hpc
  have h1 := symTrace_sound is (sound_all hf) s SState.init
  rw [SState.init_denote] at h1
  rw [blockTrE, ← h1]
  apply List.map_congr_left
  rintro ⟨pc', i, acc⟩ he
  have hk := List.all_eq_true.mp hok _ he
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  simp only [SEvent.denote, SExpr.denote_regsIn hag pc' hk.1, Event.mk.injEq, true_and]
  refine ⟨rfl, List.map_congr_left ?_⟩
  intro a ha
  simp only [SAccess.denote, Access.mk.injEq, true_and, and_true, addrE, baseE]
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have he := List.find?_some hp
    simp only [beq_iff_eq] at he
    rw [← hv] at hm
    rw [zip_map_self _ As p hm, ← base_split s p.1, ← base_split s a.addr, ← he]
    simp only [BitVec.add_sub_cancel]
  · rename_i hn
    have hany := hk.2 a ha
    rcases Bool.or_eq_true _ _ ▸ hany with hr | hany
    · rw [base_split]; exact SExpr.denote_regsIn hag a.addr hr
    · obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
      have := List.find?_eq_none.mp hn _ (hv ▸ mem_zip_map_self (fun x => x.denote s) hx)
      simp [hxe] at this

end M0Crypto.Release.Routine
