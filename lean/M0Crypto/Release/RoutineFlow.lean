import M0Crypto.Release.SegEffect

/-!
# Branches, while loops and call sites for the segment template

* `ReachFT.jif`: the generator's `jump_if`, `b<inv> +0; b tgt`, with its outcome `p` a public
  value: on `p` the run falls through past the pair, else it reaches `tgt`. Trace `jifTr`.
* `ReachT.wloop`: a while loop as passes in continuation form. A pass `body s Ψ` from `I s`
  either leaves the loop to `Q` or, when `go s`, reaches `I (next s)` and runs `Ψ` from there;
  the measure `μ` decreases. The trace `wTr` is a function of the public loop state `s`.
* `ReachFT.siteE`: `ReachFT.siteK` with the glue a segment (`SExpr` footprints and trace atoms).
* `ReachFT.seg1`: one segment. `ReachFT.jmp`: `b tgt`. `ReachFT.cjif`: a compare, then `jif`; their
  continuations take any state with the same memory and registers below `pc` (`Same`).
  `cmp_signed`: `blt`, `bgt` after `cmp` of values below `2^31`.

Each has its `GP` rule: `jif_gp`, `GP.wloop`, `site_gp`, `cjif_gp`, `jmp_gp`.
-/

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-! ## `b<c> +0; b tgt` -/

/-- The trace of `b<c> +0; b tgt` at `o`: the `b` only when `c` fails. -/
def jifTr (base : Word) (o : Nat) (c : BitVec 4) (i8 : BitVec 8) (i11 : BitVec 11) (p : Bool) : List Event :=
  ⟨base + BitVec.ofNat 32 o, .bcond c i8, []⟩ :: if p then [] else [⟨base + BitVec.ofNat 32 (o + 2), .b i11, []⟩]

/-- **`b<c> +0; b tgt` at `o`** with outcome `p = condPassed c`: on `p` to `o + 4`, else to
`tgt`. The checks are `loopFarOk` with the `b` to `tgt`. -/
theorem ReachFT.jif {cs : List (Nat × Nat)} {sp0 : Word} {N d o tgt : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {ΨT ΨF : TrP} (F : Caller base sp0 N Wc) {c : BitVec 4} {i8 : BitVec 8}
    {i11 : BitVec 11} (hbr : instrAt B o = some (.bcond c i8)) (hb : instrAt B (o + 2) = some (.b i11))
    (hok : loopFarOk cs tgt o d N i8 i11 = true) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (p : Bool) (hc : condPassed c t = p)
    (kT : p = true → ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N)
      (t.setReg 15 (base + BitVec.ofNat 32 (o + 4))) Q ΨT)
    (kF : p = false → ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N)
      (t.setReg 15 (base + BitVec.ofNat 32 tgt)) Q ΨF) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is (jifTr base o c i8 i11 p)) (Tr.cond p ΨT ΨF)) := by
  simp only [loopFarOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hob, hcs⟩, hsz⟩, ht⟩, ht2⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have quiet : ∀ (u : State) (i : Instr) k, k < 4 → u.pc = base + BitVec.ofNat 32 (o + k) →
      u.regs 13 = sp0 - BitVec.ofNat 32 d →
      Step (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u ⟨u.pc, i, []⟩ :=
    fun u i k hk hpu hu13 => ⟨by rw [hpu]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega)),
      fun y hy => absurd hy (writes_nil y), fun y hy => absurd hy (reads_nil y), by rw [hu13]; exact ⟨d, hd, rfl⟩⟩
  have e15 : ∀ (u : State) (v w : Word), (u.setReg 15 v).setReg 15 w = u.setReg 15 w := fun u v w => by
    simp only [State.setReg]; congr 1; funext i; split <;> rfl
  refine ReachT.mono (ReachT.bcond (b := p) hb2 o (o + 4) c i8 hpc hob hbr (by omega) ht
    (quiet t _ 0 (by omega) hpc h13) hc (ΨT := ΨT) (ΨF := Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + 2), .b i11, []⟩]) ΨF)
    (fun h => kT (hc ▸ h)) fun h => ?_) (fun _ _ h => h) (fun _ h => h) ?_
  · have hp : (t.setReg 15 (base + BitVec.ofNat 32 (o + 2))).pc = base + BitVec.ofNat 32 (o + 2) := by
      simp [State.setReg, State.pc]
    have := ReachT.b hb2 (o + 2) tgt i11 hp (by omega) hb (by omega) ht2
      (quiet _ _ 2 (by omega) hp (by simp [State.setReg, h13])) (by rw [e15]; exact kF (hc ▸ h))
    exact this
  · rintro _ ⟨a, w, rfl, rfl, hd⟩
    cases p
    · obtain ⟨_, x, rfl, rfl, hx⟩ := hd.2 rfl
      refine ⟨_, x, ?_, rfl, ?_⟩
      · simp [jifTr]
      · exact ⟨fun h => (nomatch h), fun _ => hx⟩
    · refine ⟨_, w, ?_, rfl, ?_⟩
      · simp [jifTr]
      · exact ⟨fun _ => hd.1 rfl, fun h => (nomatch h)⟩

/-! ## While loops -/

section wloop
variable {σ : Type}

/-- The trace of a while loop with fuel `f` from `s`: pass `body s` continued by the rest. -/
def wTr (body : σ → TrP → TrP) (next : σ → σ) : Nat → σ → TrP
  | 0, s => body s (Tr.is [])
  | f + 1, s => body s (wTr body next f (next s))

/-- **A while loop**: a pass from `I s` runs `body s Ψ`, given that `Ψ` runs from every
`I (next s)` when `go s`; `μ` decreases on `go`. With fuel above `μ s` the loop reaches `Q`. -/
theorem ReachT.wloop {P : State → Event → Prop} {I : σ → State → Prop} {Q : State → Prop}
    {body : σ → TrP → TrP} {go : σ → Bool} {next : σ → σ} (μ : σ → Nat)
    (hμ : ∀ s, go s = true → μ (next s) < μ s)
    (hp : ∀ s t Ψ, I s t → (go s = true → ∀ u, I (next s) u → ReachT base P u Q Ψ) →
      ReachT base P t Q (body s Ψ)) :
    ∀ f s t, μ s < f → I s t → ReachT base P t Q (wTr body next f s)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, s, t, h, hI => hp s t _ hI fun hg u hu => ReachT.wloop μ hμ hp f (next s) u (by have := hμ s hg; omega) hu

theorem wTr_uniq {body : σ → TrP → TrP} {next : σ → σ} (h : ∀ s Ψ, Tr.Uniq Ψ → Tr.Uniq (body s Ψ)) :
    ∀ f s, Tr.Uniq (wTr body next f s)
  | 0, s => h s _ (Tr.uniq_is _)
  | f + 1, s => h s _ (wTr_uniq h f (next s))

theorem wTr_ex {body : σ → TrP → TrP} {next : σ → σ} (h : ∀ s Ψ, Tr.Ex Ψ → Tr.Ex (body s Ψ)) :
    ∀ f s, Tr.Ex (wTr body next f s)
  | 0, s => h s _ (Tr.ex_is _)
  | f + 1, s => h s _ (wTr_ex h f (next s))

end wloop

/-! ## Call sites with segment glue -/

/-- The decided checks of a call site with glue `s`: the glue's (`sglueOk`, `traceOkE`, `r4`-`r11`
kept), and those of the `bl` to `f` as in `siteOk`. -/
def siteOkE (cs : List (Nat × Nat)) (f : Routine) (s : Seg) (o d N : Nat) (imm : BitVec 25) : Bool :=
  sglueOk cs s.g o d N s.al s.wg s.rg && traceOkE s.g s.As && keepsHi s.g &&
  (o + seqSize s.g) % 2 == 0 && rangesSub [(o, o + seqSize s.g + 4)] cs && rangesSub f.code cs &&
  outside f.code (o + seqSize s.g + 4) && decide (o + seqSize s.g + 4 ≤ BS) &&
  decide (BitVec.ofNat 32 (o + seqSize s.g) + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 f.entry) &&
  decide (d + f.stack ≤ N) && d % 4 == 0

/-- The side conditions of a call site with glue `s`. -/
def SiteSidesE (f : Routine) (base : Word) (s : Seg) (o : Nat) (t : State) (Rc Wc : List Rgn) : Prop :=
  SGlueSides t Rc Wc s.al s.wg s.rg ∧
  Sub (f.win (atCall base f s.g o t) :: f.wr (atCall base f s.g o t)) Wc ∧
  Sub (codeR base :: f.win (atCall base f s.g o t) :: f.rd (atCall base f s.g o t)) Rc ∧
  Sep (f.wr (atCall base f s.g o t)) [f.win (atCall base f s.g o t)] ∧
  Sep (f.rd (atCall base f s.g o t)) [f.win (atCall base f s.g o t)]

/-- **A call site with segment glue `s`**, the atoms at `vs`: as `ReachFT.siteK`, the glue's
trace `blockTrE`. -/
theorem ReachFT.siteE {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf)
    {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {R : Reg → Word} {t : State}
    {Q : State → Prop} {Ψ : TrP} {o d : Nat} {imm : BitVec 25} {vs : List Word} (F : Caller base sp0 N Wc)
    (s : Seg) (hseq : seqAt B o s.g = true) (hi : instrAt B (o + seqSize s.g) = some (.bl imm))
    (hok : siteOkE (BS := BS) cs f s o d N imm = true) (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSidesE f base s o t Rc Wc) (hv : s.As.map (·.denote t) = vs) (hpre : f.Pre base (atCall base f s.g o t))
    {Φ : TrP} (hΦ : Φf base (atCall base f s.g o t) = Φ)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize s.g + 4) → HiK f.clob R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B →
      MemEq (sregions t s.wg ++ f.win (atCall base f s.g o t) :: f.wr (atCall base f s.g o t)) t.mem u.mem →
      MemEq (f.win (atCall base f s.g o t) :: f.wr (atCall base f s.g o t)) (atCall base f s.g o t).mem u.mem →
      f.Post (atCall base f s.g o t) u.mem (u.regs 0) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is (blockTrE s.g (base + BitVec.ofNat 32 o) s.As vs))
        (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize s.g), .bl imm, []⟩])
          (Tr.cat Φ Ψ))) := by
  subst hΦ
  simp only [siteOkE, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, htr⟩, hk⟩, ho'⟩, hcs⟩, hfc⟩, hout⟩, hsz⟩, ht⟩, hd⟩, hd4⟩ := hok
  obtain ⟨hgs, hW, hRd, hsw, hsr⟩ := hs
  have hfa : s.g.all Instr.falls = true := by
    simp only [sglueOk, Bool.and_eq_true] at hg; exact hg.1.1.1.1.1.1.2
  have hR13 : R 13 = t.regs 13 := (hR.r 13).symm
  have hsp4 : (sp0 - BitVec.ofNat 32 d).toNat % 4 = 0 := by
    have := F.sp4; have := F.room; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hroom : f.stack ≤ (sp0 - BitVec.ofNat 32 d).toNat := by
    have := F.room; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ReachFT.sglue F s.g s.al s.wg s.rg hseq hpc h13 hcode hgs (traceAll_blockTrE hfa htr hpc hv)
    (fun hpx hx13 hcx hm => ?_) hg
  exact ReachFT.callK hf F.b4 hpx ho' hi hsz ht (PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega)))
    ⟨d, by omega, hx13⟩ hcx (hR.execAll hk) F.codeW (fun _ h => PcIn.mono hfc h) hout
    (by rw [hx13]; exact sp_sub rfl hd) (by rw [hx13]; exact hsp4) (by rw [hx13]; exact hroom) hW hRd hsw hsr hpre
    fun u hu hRu hcu hm' hp => k u hu hRu (by rw [hRu.1, hR13, h13]) hcu (hm.trans hm') hm' hp

/-! ## Single segments, `b`, compare and branch -/

/-- `u` has the memory and the registers other than `pc` of `t`. -/
def Same (t u : State) : Prop := u.mem = t.mem ∧ ∀ r : Reg, r.val ≠ 15 → u.regs r = t.regs r

theorem same_pc (t : State) (v : Word) : Same t (t.setReg 15 v) :=
  ⟨rfl, fun r h => by simp [State.setReg, show r ≠ 15 from fun e => h (by rw [e]; rfl)]⟩

/-- **One segment** `s` at `o`, its atoms at `vs`. -/
theorem ReachFT.seg1 {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {Ψ : TrP} {o d : Nat} {vs : List Word} (F : Caller base sp0 N Wc) (s : Seg)
    (hseq : seqAt B o s.g = true) (hok : (sglueOk cs s.g o d N s.al s.wg s.rg && traceOkE s.g s.As) = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SGlueSides t Rc Wc s.al s.wg s.rg) (hv : s.As.map (·.denote t) = vs)
    (k : (execAll s.g t).pc = base + BitVec.ofNat 32 (o + seqSize s.g) → (execAll s.g t).regs 13 = sp0 - BitVec.ofNat 32 d →
      CodeAt (execAll s.g t).mem base B → MemEq (sregions t s.wg) t.mem (execAll s.g t).mem →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) (execAll s.g t) Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is (blockTrE s.g (base + BitVec.ofNat 32 o) s.As vs)) Ψ) := by
  rw [Bool.and_eq_true] at hok
  have hfa : s.g.all Instr.falls = true := by simp only [sglueOk, Bool.and_eq_true] at hok; exact hok.1.1.1.1.1.1.1.2
  exact ReachFT.sglue F s.g s.al s.wg s.rg hseq hpc h13 hcode hs (traceAll_blockTrE hfa hok.2 hpc hv) k hok.1

/-- The decided checks of `b tgt` at `o`. -/
def jmpOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt d N : Nat) (i11 : BitVec 11) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (o + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 o + 4#32 + (i11 ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt) && decide (d ≤ N)

/-- **`b tgt` at `o`**. -/
theorem ReachFT.jmp {cs : List (Nat × Nat)} {sp0 : Word} {N d o tgt : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {Ψ : TrP} {i11 : BitVec 11} (F : Caller base sp0 N Wc) (hb : instrAt B o = some (.b i11))
    (hok : jmpOk cs o tgt d N i11 = true) (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (k : ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 tgt →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .b i11, []⟩]) Ψ) := by
  simp only [jmpOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨ho, hcs⟩, hsz⟩, ht⟩, hd⟩ := hok
  exact ReachT.b (by have := F.b4; omega) o tgt i11 hpc ho hb hsz ht
    ⟨by rw [hpc]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega)),
      fun y hy => absurd hy (writes_nil y), fun y hy => absurd hy (reads_nil y), by rw [h13]; exact ⟨d, hd, rfl⟩⟩
    (k _ (same_pc t _) (by simp [State.setReg, State.pc]))

/-- The decided checks of `b<c> tgt` at `o`. -/
def brOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt d N : Nat) (i8 : BitVec 8) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (o + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 o + 4#32 + (i8 ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt) && decide (d ≤ N)

/-- **`b<c> tgt` at `o`** with outcome `p = condPassed c`: on `p` to `tgt`, else to `o + 2`. -/
theorem ReachFT.br {cs : List (Nat × Nat)} {sp0 : Word} {N d o tgt : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {ΨT ΨF : TrP} {c : BitVec 4} {i8 : BitVec 8} (F : Caller base sp0 N Wc)
    (hb : instrAt B o = some (.bcond c i8)) (hok : brOk cs o tgt d N i8 = true) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (p : Bool) (hc : condPassed c t = p)
    (kT : p = true → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 tgt →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q ΨT)
    (kF : p = false → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (o + 2) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q ΨF) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .bcond c i8, []⟩]) (Tr.cond p ΨT ΨF)) := by
  simp only [brOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨ho, hcs⟩, hsz⟩, ht⟩, hd⟩ := hok
  exact ReachFT.bcond (by have := F.b4; omega) tgt c i8 hpc ho hb hsz ht
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega))) (by rw [h13]; exact ⟨d, hd, rfl⟩) hc
    (fun h => kT (hc ▸ h) _ (same_pc t _) (by simp [State.setReg, State.pc]))
    (fun h => kF (hc ▸ h) _ (same_pc t _) (by simp [State.setReg, State.pc]))

/-- The decided checks of a compare `i` at `o` and `b<c> +0; b tgt` after it. -/
def cjifOk [CodeBytes B BS] (cs : List (Nat × Nat)) (i : Instr) (o tgt d N : Nat) (i8 : BitVec 8) (i11 : BitVec 11) :
    Bool :=
  sglueOk cs [i] o d N [] [] [] && i.dsts.isEmpty && i.size == 2 && loopFarOk cs tgt (o + 2) d N i8 i11

/-- **A compare `i` at `o`, then `b<c> +0; b tgt`**, with outcome `p = condPassed c` after `i`. -/
theorem ReachFT.cjif {cs : List (Nat × Nat)} {sp0 : Word} {N d o tgt : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {ΨT ΨF : TrP} (F : Caller base sp0 N Wc) {i : Instr} {c : BitVec 4} {i8 : BitVec 8}
    {i11 : BitVec 11} (hseq : seqAt B o [i, .bcond c i8, .b i11] = true) (hok : cjifOk cs i o tgt d N i8 i11 = true)
    (hacc : i.accesses t = []) (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B) (p : Bool) (hc : condPassed c (i.next t) = p)
    (kT : p = true → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (o + 6) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q ΨT)
    (kF : p = false → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 tgt →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q ΨF) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, i, []⟩])
        (Tr.cat (Tr.is (jifTr base (o + 2) c i8 i11 p)) (Tr.cond p ΨT ΨF))) := by
  simp only [cjifOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hg, hd⟩, hz⟩, hl⟩ := hok
  rw [show [i, .bcond c i8, .b i11] = [i] ++ [.bcond c i8, .b i11] from rfl, seqAt_append, Bool.and_eq_true,
    show seqSize [i] = 2 by simp [seqSize, hz]] at hseq
  obtain ⟨h1, h2⟩ := hseq
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq] at h2
  have hn : ∀ r : Reg, r.val ≠ 15 → (i.next t).regs r = t.regs r := fun r h =>
    execAll_regs_other [i] t r h (by simp [List.isEmpty_iff.mp hd])
  have hs : ∀ u v, u = (i.next t).setReg 15 v → Same t u := fun u v e => by
    subst e
    refine ⟨?_, fun r h => by rw [(same_pc _ v).2 r h, hn r h]⟩
    have hm := execAll_memEqE (wg := []) t (by simp only [sglueOk, Bool.and_eq_true] at hg; exact hg.1.1.1.1.1.1.2)
      (by simp only [sglueOk, Bool.and_eq_true] at hg; exact hg.1.1.1.2)
    funext y; show (execAll [i] t).mem y = t.mem y; exact (hm y fun ⟨_, h, _⟩ => nomatch h)
  refine ReachFT.sglue F [i] [] [] [] h1 hpc h13 hcode ⟨fun _ h => (nomatch h),
    fun _ h => (nomatch h), fun _ h => (nomatch h)⟩ (by simp [traceAll, hacc, hpc]) (fun hp h13' _ _ => ?_) hg
  exact ReachFT.jif F h2.1.1 h2.2.1.1 hl (by rw [hp]; simp [seqSize, hz]) h13' p hc
    (fun h => kT h _ (hs _ _ rfl) (by simp [State.setReg, State.pc, Nat.add_assoc]))
    (fun h => kF h _ (hs _ _ rfl) (by simp [State.setReg, State.pc]))

/-- `blt`, `bgt` after `cmp a, b` of values below `2^31`. -/
theorem cmp_signed (a b : M0Crypto.Armv6M.LowReg) (s : State) (ha : (s.regs a.toReg).toNat < 2 ^ 31)
    (hb : (s.regs b.toReg).toNat < 2 ^ 31) :
    condPassed 11 ((Instr.dp .cmp a b).next s) = decide ((s.regs a.toReg).toNat < (s.regs b.toReg).toNat) ∧
    condPassed 12 ((Instr.dp .cmp a b).next s) = decide ((s.regs b.toReg).toNat < (s.regs a.toReg).toNat) := by
  simp [condPassed, Instr.next, Instr.exec, addFlags, State.setNZCV, State.setNZ, State.reg,
    M0Crypto.Armv6M.addWithCarry, BitVec.msb_eq_toNat, BitVec.toInt_eq_toNat_cond]
  constructor <;> grind

end M0Crypto.Release.Routine

namespace M0Crypto.Release.StackEffect

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
open M0Crypto.Release.Routine (jifTr wTr)

variable {sp0 : Word} {n : Nat}

/-- `b<c> +0; b tgt` keeps `SIR`. -/
theorem jif_gp {sp : Word} {R : Word → Prop} {base : Word} {o : Nat} {c : BitVec 4} {i8 : BitVec 8}
    {i11 : BitVec 11} (p : Bool) : GP sp0 n (SIR sp0 sp R) (Tr.is (jifTr base o c i8 i11 p)) (SIR sp0 sp R) := by
  cases p
  · exact GP.cons (sir_quietC rfl rfl rfl) (GP.cons (sir_quietC rfl rfl rfl) (GP.nil fun _ h => h))
  · exact GP.cons (sir_quietC rfl rfl rfl) (GP.nil fun _ h => h)

/-- **A while loop's GP**: each pass `body s Ψ` from `K s`, given `Ψ` from `K (next s)` when `go s`. -/
theorem GP.wloop {σ : Type} {K : σ → Ef → Prop} {J : Ef → Prop} {body : σ → TrP → TrP} {go : σ → Bool}
    {next : σ → σ} (μ : σ → Nat) (hμ : ∀ s, go s = true → μ (next s) < μ s)
    (hp : ∀ s Ψ, (go s = true → GP sp0 n (K (next s)) Ψ J) → GP sp0 n (K s) (body s Ψ) J) :
    ∀ f s, μ s < f → GP sp0 n (K s) (wTr body next f s) J
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, s, h => hp s _ fun hg => GP.wloop μ hμ hp f (next s) (by have := hμ s hg; omega)

/-- **A call site's GP**: the glue's pass, the quiet `bl`, the callee's effect at the same SP. -/
theorem site_gp {sp : Word} {R R' : Word → Prop} {G : List Event} {e : Event} {tr : List Event} {stk : Nat}
    {Fp Rq Wd : Word → Prop} {Ψ : TrP} {J : Ef → Prop} (hg : GP sp0 n (SIR sp0 sp R) (Tr.is G) (SIR sp0 sp R'))
    (he : spExact e.instr = true) (hs : spAfter e.instr sp = sp) (ha : e.accesses = []) (hE : EffT stk Fp Rq Wd sp tr)
    (hroom : (sp0 - sp).toNat + stk ≤ n) (hn : n < 2 ^ 32)
    (hF : ∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) (hR : ∀ y, Rq y → BelowEntry sp0 n y → R' y)
    (hk : GP sp0 n (SIR sp0 sp fun y => R' y ∨ Wd y ∧ BelowEntry sp0 n y) Ψ J) :
    GP sp0 n (SIR sp0 sp R) (Tr.cat (Tr.is G) (Tr.cat (Tr.is [e]) (Tr.cat (Tr.is tr) Ψ))) J :=
  GP.cat hg (GP.cat (sir_quietC he hs ha) (GP.cat (gp_effT hE hroom hn hF hR) hk))

/-- A compare and `b<c> +0; b tgt` keep `SIR`: the GP of the side taken. -/
theorem cjif_gp {sp : Word} {R : Word → Prop} {J : Ef → Prop} {base pc : Word} {o : Nat} {i : Instr} {c : BitVec 4}
    {i8 : BitVec 8} {i11 : BitVec 11} {ΨT ΨF : M0Crypto.Release.TrP} (hx : spExact i = true) (hs : spAfter i sp = sp)
    (p : Bool) (hT : p = true → GP sp0 n (SIR sp0 sp R) ΨT J) (hF : p = false → GP sp0 n (SIR sp0 sp R) ΨF J) :
    GP sp0 n (SIR sp0 sp R) (Tr.cat (Tr.is [⟨pc, i, []⟩]) (Tr.cat (Tr.is (jifTr base o c i8 i11 p)) (Tr.cond p ΨT ΨF))) J :=
  GP.cat (sir_quietC hx hs rfl) (GP.cat (jif_gp p) (GP.cond hT hF))

/-- `b<c> tgt` keeps `SIR`: the GP of the side taken. -/
theorem br_gp {sp : Word} {R : Word → Prop} {J : Ef → Prop} {pc : Word} {c : BitVec 4} {i8 : BitVec 8}
    {ΨT ΨF : M0Crypto.Release.TrP} (p : Bool) (hT : p = true → GP sp0 n (SIR sp0 sp R) ΨT J)
    (hF : p = false → GP sp0 n (SIR sp0 sp R) ΨF J) :
    GP sp0 n (SIR sp0 sp R) (Tr.cat (Tr.is [⟨pc, .bcond c i8, []⟩]) (Tr.cond p ΨT ΨF)) J :=
  GP.cat (sir_quietC rfl rfl rfl) (GP.cond hT hF)

theorem jmp_gp {sp : Word} {R : Word → Prop} {J : Ef → Prop} {pc : Word} {i11 : BitVec 11} {Ψ : M0Crypto.Release.TrP}
    (h : GP sp0 n (SIR sp0 sp R) Ψ J) : GP sp0 n (SIR sp0 sp R) (Tr.cat (Tr.is [⟨pc, .b i11, []⟩]) Ψ) J :=
  GP.cat (sir_quietC rfl rfl rfl) h

end M0Crypto.Release.StackEffect
