import M0Crypto.Release.RoutineBlock

/-!
# Counted loops whose body is one block

`ReachFT.sloop`: a loop `g; b<cond> g` whose body `g` is one straight-line block with footprints
given as expressions of its entry state (`ReachFT.sglue`) and its trace from the values of its
address atoms (`traceAll_blockTrE`). The caller states, per pass `j`, the side conditions, the
atoms' values `vs j`, and the effect of `g` on the invariant; the rule does the branch, the glue
and the trace. Pass `j`'s trace is the block's at `vs j`, then the branch.
-/

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The trace of pass `j` of `sloop`. -/
def sloopTr (base : Word) (g : List Instr) (o : Nat) (As : List SExpr) (vs : Nat → List Word)
    (cond : BitVec 4) (imm : BitVec 8) (j : Nat) : TrP :=
  Tr.cat (Tr.cat (Tr.is (blockTrE g (base + BitVec.ofNat 32 o) As (vs j))) (Tr.is []))
    (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize g), .bcond cond imm, []⟩])

/-- **A counted loop of one block** `g` at `o`, its branch `b<cond>` back to `o` right after it:
`n` passes from `I 0`, pass `j` taking `I j` to `I (j + 1)` and the branch exactly while
`j + 1 < n`; then `hexit` from `I n` after the branch. -/
theorem ReachFT.sloop {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Ψx : TrP} {o d : Nat} (F : Caller base sp0 N Wc) (g : List Instr)
    (al wg rg : List (SExpr × Nat)) (As : List SExpr) (cond : BitVec 4) (imm : BitVec 8)
    (hseq : seqAt B o g = true) (hbr : instrAt B (o + seqSize g) = some (.bcond cond imm))
    (n : Nat) (I : Nat → State → Prop) (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v))
    (vs : Nat → List Word)
    (hside : ∀ j t, j < n → I j t → SGlueSides t Rc Wc al wg rg ∧ As.map (·.denote t) = vs j)
    (hstep : ∀ j t, j < n → I j t → MemEq (sregions t wg) t.mem (execAll g t).mem →
      I (j + 1) (execAll g t) ∧ condPassed cond (execAll g t) = decide (j + 1 < n))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (o + seqSize g + 2) → I n t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (hok : (sglueOk cs g o d N al wg rg && traceOkE g As && loopOk cs o (o + seqSize g) d N imm) = true)
    (t : State) (hn : 0 < n) (hpc : t.pc = base + BitVec.ofNat 32 o) (hI : I 0 t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hc : CodeAt t.mem base B) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.rep (sloopTr base g o As vs cond imm) 0 n Ψx) := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hg, htr⟩, hl⟩ := hok
  have hf : g.all Instr.falls = true := by
    simp only [sglueOk, Bool.and_eq_true] at hg; exact hg.1.1.1.1.1.1.2
  have h := ReachFT.loop (Φb := fun j => Tr.cat (Tr.is (blockTrE g (base + BitVec.ofNat 32 o) As (vs j)))
    (Tr.is [])) F cond imm hbr n I hpcI (fun j u hj hpu hIu h13u hcu =>
    ReachFT.sglue F g al wg rg hseq hpu h13u hcu (hside j u hj hIu).1
      (traceAll_blockTrE hf htr hpu (hside j u hj hIu).2) (fun hp' h13' hc' hm =>
        ReachT.done ⟨hp', h13', hc', hstep j u hj hIu hm⟩) hg) hexit hl 0 t hn hpc hI h13 hc
  rwa [Nat.sub_zero] at h

end M0Crypto.Release.Routine
