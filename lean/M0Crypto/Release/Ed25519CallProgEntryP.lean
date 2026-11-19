import M0Crypto.Release.Ed25519CallProgEntryRun
import M0Crypto.Release.Ed25519CallProgEntryGood

set_option linter.unusedSimpArgs false

/-!
# Call programs: entries with a public leave

An entry on public data leaves without a wipe (`abi_leave` with `wipe=False`): `sp` back over
the frame, `r1` and `r12` cleared, `r4`-`r11` restored, and the return. `leaveP_run` runs it,
`entry_runP` runs an entry with a given body and this leave, and `entry_goodP` gives its trace
the stack effect.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)

/-- `abi_leave` without a wipe: `sp` up by the frame `fs`, the restores, `pop {r4-r7, pc}`. -/
def abiLeaveP (fs : Nat) : List Piece := [.seq (addSps fs ++ restoreHi), .seq [.pop 0xf0 true]]

/-- The trace of `abiLeaveP fs` at `o`. -/
def leavePTr (base sp0 : Word) (fs o : Nat) (Ψ : TrP) : TrP :=
  let ot := o + 2 * (chunks fs fs).length
  Tr.cat (Tr.is (spTr base true o (chunks fs fs))) <|
  Tr.cat (Tr.is (blockTr restoreHi (base + BitVec.ofNat 32 ot) [13] [sp0 - 36#32])) <|
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (ot + 14), .pop 0xf0 true, wordAccesses .read (sp0 - 20#32) 5⟩]) Ψ

section leave
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base sp0 : Word} {N : Nat}
variable {Pc Rd Wr : Word → Prop}

/-- **`abi_leave` without a wipe**: `sp` back, `r1` and `r12` cleared, `r4`-`r11` restored from the
saved words, `r0` kept, and the return through the saved `lr`. -/
theorem leaveP_run (hb : base.toNat % 2 = 0) {fs o : Nat} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0) (hseq : piecesAt B o (abiLeaveP fs) = true)
    (hr : InRegion Pc base o (piecesSize (abiLeaveP fs)))
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 (36 + fs)) (h4 : sp0.toNat % 4 = 0)
    (hroom : 36 + fs ≤ sp0.toNat) (hfs : fs % 4 = 0) (hN : 36 + fs ≤ N)
    (hRd : ∀ j < 36, Rd (sp0 - 36#32 + BitVec.ofNat 32 j))
    (hlr : (read32 t.mem (sp0 - 4#32)).getLsbD 0 = true)
    (k : ∀ u, u.pc = read32 t.mem (sp0 - 4#32) &&& ~~~1#32 → u.regs 13 = sp0 → u.regs 0 = t.regs 0 →
      u.regs 1 = 0 → u.regs 12 = 0 →
      (∀ i < 8, u.regs Ed25519.savedRegs[i]! = read32 t.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i))) →
      u.mem = t.mem → ReachFT base Pc Rd Wr (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base Pc Rd Wr (InStackWindow sp0 N) t Q (leavePTr base sp0 fs o Ψ) := by
  simp only [abiLeaveP, piecesAt, Piece.instrs, Piece.size, Bool.and_eq_true] at hseq
  simp only [abiLeaveP, piecesSize_cons, piecesSize_nil, Piece.size] at hr
  have hTl : addSps fs ++ restoreHi = (chunks fs fs).map (spI true) ++ restoreHi := by simp [addSps_eq]
  have hszT : seqSize (addSps fs ++ restoreHi) = 2 * (chunks fs fs).length + 14 := by
    rw [hTl, seqSize_append, seqSize_sps]; rfl
  obtain ⟨ot, hot⟩ : ∃ ot, ot = o + 2 * (chunks fs fs).length := ⟨_, rfl⟩
  rw [hszT] at hseq hr
  obtain ⟨hT, hP, -⟩ := hseq
  rw [show o + (2 * (chunks fs fs).length + 14) = ot + 14 by omega] at hP
  rw [hTl, seqAt_append, seqSize_sps, Bool.and_eq_true, ← hot] at hT
  obtain ⟨hT2, hT3⟩ := hT
  have hsf : (chunks fs fs).sum = fs := chunks_sum fs fs (by omega)
  simp only [leavePTr]
  rw [← hot]
  rw [show seqSize [Instr.pop 240 true] = 2 from rfl] at hr
  have reg : ∀ a n, o ≤ a → a + n ≤ ot + 16 → InRegion Pc base a n := fun a n h1 h2 j hj => by
    have := hr (a - o + j) (by omega)
    rwa [show o + (a - o + j) = a + j by omega] at this
  have hsp := sp0.isLt
  refine sps_run hb true (chunks fs fs) o (36 + fs) t
    (fun x hx => ⟨(chunks_le fs fs x hx).1, chunks_four fs fs hfs x hx⟩)
    hpc ho hT2 (reg _ _ (Nat.le_refl _) (by omega)) h13 hN (by simp only [↓reduceIte, hsf]; omega)
    fun u5 hpu5 hu5 hur5 hum5 => ?_
  have e5 : u5.regs 13 = sp0 - 36#32 := by
    rw [hu5]; simp only [↓reduceIte, hsf, Nat.add_sub_cancel]
  have hpc5 : u5.pc = base + BitVec.ofNat 32 ot := by rw [hpu5, hot]
  have hT3' : traceAll restoreHi u5 = blockTr restoreHi (base + BitVec.ofNat 32 ot) [13] [sp0 - 36#32] :=
    traceAll_blockTr (by decide) restore_trOk hpc5 (by simp [e5])
  rw [← hT3']
  obtain ⟨r1, r12, r13, r8, r9, r10, r11, rR, rm, rpc⟩ := restore_facts u5
  refine ReachT.block hb restoreHi ot u5 hpc5 (by omega) hT3 (by decide) ?_
    (restore_ok u5 hpc5 (reg _ _ (by omega) (by omega)) (d := 36) e5 (by omega) (by omega)
      (fun j hj => hRd j (by omega))) ?_
  · simp [alignedAll, restoreHi, Instr.accesses, Instr.next, Instr.exec, lr_f0, State.setReg, State.setNZ,
      State.sp, State.reg, lr1, e5]
    exact List.all_eq_true.mp (words_aligned _ _ _ (by rw [BitVec.toNat_sub]; simp; omega))
  have hA : ∀ i < 9, ∀ x, x = sp0 - 36#32 + BitVec.ofNat 32 (4 * i) →
      read32 u5.mem x = read32 t.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) := fun i _ x hx => by
    rw [hx, hum5]
  have e6 : (execAll restoreHi u5).regs 13 = sp0 - 20#32 := by rw [r13, e5, ad_sp]
  have bc : bitCount (240 : BitVec 8) = 4 := by decide
  have hlr6 : (read32 (execAll restoreHi u5).mem ((execAll restoreHi u5).regs 13 +
      BitVec.ofNat 32 (4 * bitCount (240 : BitVec 8)))).getLsbD 0 = true := by
    rw [rm, bc, e6, hA 8 (by omega) _ (ad_lr sp0), ad_lr']
    exact hlr
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hP
  refine ReachFT.step hb (.pop 240 true) (off := ot + 14) (by rw [rpc, hpc5, ofNat_add_assoc]) (by omega)
    hP.1.1 hP.1.2 ?_ (pop_exec _ _ hlr6)
    (by simpa using reg (ot + 14) 2 (by omega) (by omega) 0 (by omega))
    (fun y hy => by simp only [Instr.accesses] at hy; exact absurd hy words_no_writes)
    (fun y hy => ?_) ⟨20, by omega, e6⟩ ?_ ?_
  · simp only [Instr.accesses, State.sp, e6]
    exact words_aligned _ _ _ (ad_al sp0 h4)
  · simp only [Instr.accesses, State.sp, e6] at hy
    obtain ⟨o', ho', rfl⟩ := words_reads hy
    have := hRd (16 + o') (by simp [bc] at ho'; omega)
    rwa [ad_rd] at this
  · have hp6 : (execAll restoreHi u5).regs 15 = base + BitVec.ofNat 32 (ot + 14) := by
      have := rpc; rw [hpc5, ofNat_add_assoc] at this; exact this
    simp only [Instr.accesses, State.sp, e6, bc, State.pc, hp6]; rfl
  obtain ⟨p4, p5, p6, p7, ppc, p13, pR, pm⟩ := pop_facts (execAll restoreHi u5)
  refine k _ ?_ (by rw [p13, e6, ad_top]) ?_ (by rw [pR 1 (by decide), r1]) (by rw [pR 12 (by decide), r12])
    ?_ (by rw [pm, rm, hum5])
  · rw [ppc, rm, e6, hA 8 (by omega) _ (ad_lr sp0), ad_lr']
  · rw [pR 0 (by decide), rR 0 (by decide) (by decide), hur5 0 (by decide) (by decide)]
  · intro i hi
    have s8 : Ed25519.savedRegs[0]! = 8 := rfl
    have s9 : Ed25519.savedRegs[1]! = 9 := rfl
    have s10 : Ed25519.savedRegs[2]! = 10 := rfl
    have s11 : Ed25519.savedRegs[3]! = 11 := rfl
    have s4 : Ed25519.savedRegs[4]! = 4 := rfl
    have s5 : Ed25519.savedRegs[5]! = 5 := rfl
    have s6 : Ed25519.savedRegs[6]! = 6 := rfl
    have s7 : Ed25519.savedRegs[7]! = 7 := rfl
    obtain _ | _ | _ | _ | _ | _ | _ | _ | i := i
    · rw [s8, pR 8 (by decide), r8, e5, hA 0 (by omega) _ (by simp)]
    · rw [s9, pR 9 (by decide), r9, e5, hA 1 (by omega) _ rfl]
    · rw [s10, pR 10 (by decide), r10, e5, hA 2 (by omega) _ rfl]
    · rw [s11, pR 11 (by decide), r11, e5, hA 3 (by omega) _ rfl]
    · rw [s4, p4, rm, e6, hA 4 (by omega) _ (by simpa using ad_hi sp0 0)]
    · rw [s5, p5, rm, e6, hA 5 (by omega) _ (ad_hi sp0 1)]
    · rw [s6, p6, rm, e6, hA 6 (by omega) _ (ad_hi sp0 2)]
    · rw [s7, p7, rm, e6, hA 7 (by omega) _ (ad_hi sp0 3)]
    · omega

end leave

/-! ## The entry -/

/-- The decided facts of an entry with a body of `bsz` bytes and a public leave. -/
def entryOkP (G : Geo) (bsz oE : Nat) : Bool :=
  let ol := bodyAt G oE + bsz
  G.xv.isEmpty && G.top % 4 == 0 && decide (G.top ≤ G.N) && decide (G.N < 2048) && oE % 2 == 0 && ol % 2 == 0 &&
    rangesSub [(oE, oE + seqSize (abiEnter G.top))] G.cs && rangesSub [(ol, ol + piecesSize (abiLeaveP G.top))] G.cs

/-- The trace of an entry at `oE` whose body of `bsz` bytes has the trace `Ψ`, with a public leave. -/
def entryTrP (G : Geo) (c : Ctx) (sp0 : Word) (oE bsz : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTr saveHi (c.base + BitVec.ofNat 32 oE) [13] [sp0]))
    (Tr.cat (Tr.is (spTr c.base false (oE + 12) (chunks G.top G.top)))
      (Tr.cat Ψ (leavePTr c.base sp0 G.top (bodyAt G oE + bsz) (Tr.is []))))

theorem entryTrP_uniq {G : Geo} {c : Ctx} {sp0 : Word} {oE bsz : Nat} {Ψ : TrP} (h : Tr.Uniq Ψ) :
    Tr.Uniq (entryTrP G c sp0 oE bsz Ψ) :=
  Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat h
    (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_is _))))))

section
variable (Rs : Rels)
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn}

/-- **An entry with a given body and a public leave**: from its entry state, an entry whose body
of `bsz` bytes runs from the program state `st0` to the leave with the trace `Ψ`, keeping the
saved words, with `R`, returns with `sp` and `r4`-`r11` restored, `r0` the body's, `r1` and `r12`
zero and the saved words in place; memory is the body's final memory. -/
theorem entry_runP {bsz : Nat} {Ψ : TrP} {st0 : St} {oE : Nat} {s : State} {sp0 : Word} {R Q : State → Prop}
    (F : Caller c.base c.sp0 G.N Wc) (hok : entryOkP G bsz oE = true) (hen : seqAt B oE (abiEnter G.top) = true)
    (hsp : c.sp0 = sp0 - 36#32) (hroom : 36 + G.N ≤ sp0.toNat) (hs13 : s.regs 13 = sp0) (hpc : s.pc = c.base + BitVec.ofNat 32 oE)
    (hc : CodeAt s.mem c.base B) (hcs : ∀ i < B.length, ¬ Region (sp0 - 36#32) 36 (c.base + BitVec.ofNat 32 i))
    (hΓ : st0.Γ = []) (hρ0 : st0.ρ = []) (hσ : ∀ p ∈ st0.σ, (p.1.val < 4 ∧ s.regs p.1 = p.2.val c (G.fsp c)) ∨ p = (13, .sp 0))
    (hlr : (s.regs 14).getLsbD 0 = true)
    (hbody : ∀ t, At Rs B c G (enterMem s sp0) (bodyAt G oE) st0 (fun _ => .none) t →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t
        (fun u => u.pc = c.base + BitVec.ofNat 32 (bodyAt G oE + bsz) ∧ u.regs 13 = G.fsp c ∧
          piecesAt B (bodyAt G oE + bsz) (abiLeaveP G.top) = true ∧
          (∀ y, Region (sp0 - 36#32) 36 y → u.mem y = enterMem s sp0 y) ∧ R u) Ψ)
    (k : ∀ u1 u, R u1 →
      u.pc = s.regs 14 &&& ~~~1#32 → u.regs 13 = sp0 → u.regs 0 = u1.regs 0 →
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = s.regs r) → u.regs 1 = 0 → u.regs 12 = 0 →
      (∀ i < 9, read32 u.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) = s.regs Ed25519.savedRegs[i]!) →
      u.mem = u1.mem → Q u) :
    ReachFT c.base (PcIn c.base G.cs) (Has (savedR sp0 :: Rc)) (Has (savedR sp0 :: Wc))
      (InStackWindow sp0 (36 + G.N)) s Q (entryTrP G c sp0 oE bsz Ψ) := by
  simp only [entryOkP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hxv, h4⟩, hle⟩, h2048⟩, hoE⟩, hol⟩, hrE⟩, hrL⟩ := hok
  have hb : c.base.toNat % 2 = 0 := by have := F.b4; omega
  have hsp4 : sp0.toNat % 4 = 0 := by
    have := F.sp4; rw [hsp, BitVec.toNat_sub] at this; simp at this; omega
  refine enter_run hb hpc hoE hen (inRegion_of hrE) hs13 hsp4 h4 (by omega)
    (fun j hj => Has.cons ⟨j, hj, rfl⟩ _) fun t hpt ht13 htr htm => ?_
  have hat : At Rs B c G (enterMem s sp0) (bodyAt G oE) st0 (fun _ => .none) t := by
    refine ⟨hpt, by rw [ht13, Geo.fsp, hsp, ad_sub36], ?_, fun p hp => ?_, ⟨fun p hp => ?_,
      fun y _ _ => by rw [htm]; rfl, fun p hp => by simp [List.isEmpty_iff.mp hxv] at hp⟩,
      fun r h => by rw [hρ0] at h; cases h⟩
    · intro i hi; rw [htm, show storeWords _ _ _ = enterMem s sp0 from rfl, enterMem_other _ _ (hcs i hi)]
      exact hc i hi
    · rcases hσ p hp with ⟨h4', hv⟩ | rfl
      · exact ⟨by omega, by rw [htr p.1 (Or.inl h4'), hv]⟩
      · refine ⟨by decide, ?_⟩
        simp only [SV.val, ht13, Geo.fsp, hsp, ad_sub36]; simp
    · simp [hΓ] at hp
  refine ReachT.seq (ReachT.mono (hbody t hat)
      (fun x e ⟨a1, a2, a3, a4⟩ => ⟨a1, fun y hy => Has.tail (a2 y hy), fun y hy => Has.tail (a3 y hy),
        win_mono (hsp ▸ a4)⟩) (fun _ h => h) (fun _ h => h)) fun u1 hu1 => ?_
  obtain ⟨hp1, h131, hpl, hsv1, hR1⟩ := hu1
  have hs1 := saved_of (by omega) hsv1
  refine leaveP_run hb hp1 hol hpl (inRegion_of hrL)
    (by rw [h131, Geo.fsp, hsp, ad_sub36]) hsp4 (by omega) h4 (by omega)
    (fun j hj => Has.cons ⟨j, hj, rfl⟩ _)
    (by rw [← ad_lr', hs1 8 (by omega)]; exact hlr) fun u hpu hu13 hr0 hr1 hr12 hcal hum => ?_
  have hsu : ∀ y, Region (sp0 - 36#32) 36 y → u.mem y = enterMem s sp0 y := fun y hy => by
    rw [hum]; exact hsv1 y hy
  refine ReachT.done (k u1 u hR1 ?_ hu13 hr0 (callee_of fun i hi => ?_) hr1 hr12 (saved_of (by omega) hsu) hum)
  · rw [hpu, ← ad_lr', hs1 8 (by omega)]; rfl
  · rw [hcal i hi, hs1 i (by omega)]

end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {c : Ctx} {G : Geo} {sp0 : Word}

/-- **An entry with a given body and a public leave has a good trace**: the enter, the body's
trace `Ψ`, which keeps the frame's invariant from the program state `st0` to the leave, and the
leave. -/
theorem entry_goodP (hsp : c.sp0 = sp0 - 36#32) {bsz : Nat} {Ψ : TrP} {st0 : St} {oE : Nat}
    (hok : entryOkP G bsz oE = true) (hΓ : st0.Γ = [])
    (hb : GP sp0 (36 + G.N) (BI c G sp0 (36 + G.N) (Sv sp0) st0) Ψ (SIR sp0 (G.fsp c) (Sv sp0))) :
    ∀ tr, entryTrP G c sp0 oE bsz Ψ tr → Good sp0 (36 + G.N) ⟨sp0, fun _ => False⟩ tr := by
  simp only [entryOkP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, ht4⟩, hle⟩, hN⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have sT := chunks_sum G.top G.top (by omega)
  have hf : G.fsp c = sp0 - BitVec.ofNat 32 (36 + G.top) := by rw [Geo.fsp, hsp, ad_sub36]
  have d1 := sp_down (n := 36 + G.N) (sp0 := sp0) c.base _ (oE + 12) 36 (chunks_ok ht4) (by omega) (by omega)
  have u1 := sp_up (n := 36 + G.N) (sp0 := sp0) c.base (chunks G.top G.top) (bodyAt G oE + bsz) (36 + G.top)
    (chunks_ok ht4) (by omega) (by omega)
  rw [sT] at d1 u1
  rw [show 36 + G.top - G.top = 36 by omega] at u1
  have pop : GP sp0 (36 + G.N) (SIR sp0 (sp0 - BitVec.ofNat 32 20) (Region (sp0 - BitVec.ofNat 32 20) 20))
      (Tr.is [⟨c.base + BitVec.ofNat 32 (bodyAt G oE + bsz + 2 * (chunks G.top G.top).length + 14),
        .pop 0xf0 true, wordAccesses .read (sp0 - 20#32) 5⟩]) (fun _ => True) :=
    fun q hq tr htr => ⟨(sir_ev (R' := fun _ => False) rfl rfl (fun y h => .inl (reg_above (h.elim
      (reads_words (by omega)) (absurd · no_writes)) (by omega) (by omega) (by omega))) (fun y h => reads_words (k := 5)
      (by omega) h) nofun q hq tr htr).1, trivial⟩
  have hL : GP sp0 (36 + G.N) (SIR sp0 (G.fsp c) (Sv sp0))
      (leavePTr c.base sp0 G.top (bodyAt G oE + bsz) (Tr.is [])) (fun _ => True) :=
    GP.pre (fun q h => ⟨h.hs.trans hf, h.r, fun y hy => hf ▸ h.ab y hy⟩)
      (GP.cat u1 (GP.cat (rest_gp _) (GP.cat pop (GP.nil fun _ _ => trivial))))
  intro tr htr
  exact (GP.cat (save_gp _) (GP.cat d1 (GP.cat (GP.pre (fun q h => ⟨h.hs.trans hf.symm, fun y hy => hf ▸ h.ab y hy,
    h.r, fun y hy => by rw [hΓ] at hy; obtain ⟨_, hp, _⟩ := hy; cases hp⟩) hb) hL)) ⟨sp0, fun _ => False⟩ ⟨rfl, fun _ h => h, fun _ h => h.elim⟩ tr htr).1

end

end M0Crypto.Release.Ed25519CallProg
