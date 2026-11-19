import M0Crypto.Release.Ed25519Routines
import M0Crypto.Release.RoutinePieces

set_option linter.unusedSimpArgs false

/-!
# A field call on frame slots

`fop(g, fn, S(d), S(a), S(b))` of the generator: `add r0, sp, #d; add r1, sp, #a;
add r2, sp, #b; bl m0c_fe_<fn>`. `fop_site` is its rule, proved once for any slots, callee and
offset: the continuation receives the slot `d` congruent to `fn` of the slots `a` and `b`, and
the memory equal outside slot `d` and the callee's window. The trace is `fopTr`, a function of the
code base, `sp` and the slots.
-/

namespace M0Crypto.Release.Ed25519FieldSite

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- `add r, sp, #off`. -/
def spAdd (r : LowReg) (off : Nat) : Instr := .addRdSp r (BitVec.ofNat 8 (off / 4))

/-- The operand loads of `fop` on frame slots `d`, `a`, `b`. -/
def fopG (d a b : Nat) : List Instr := [spAdd 0 d, spAdd 1 a, spAdd 2 b]

/-- The pieces of `fop` on frame slots, calling the routine at `f`. -/
def fopP (f d a b : Nat) : List Piece := [.seq (fopG d a b), .call f]

theorem fopP_size (f d a b : Nat) : piecesSize (fopP f d a b) = seqSize (fopG d a b) + blSize := by
  simp [piecesSize, fopP]; rfl

/-- A frame slot: word-aligned, within `add rd, sp, #imm` range and below `top`. -/
def SlotOk (top off : Nat) : Prop := off % 4 = 0 ∧ off + 32 ≤ top ∧ off < 1024

/-- Two slots are the same or lie apart. -/
def Apart (x y : Nat) : Prop := x = y ∨ x + 32 ≤ y ∨ y + 32 ≤ x

theorem spAdd_val {off : Nat} (h : off % 4 = 0) (h1 : off < 1024) :
    BitVec.ofNat 32 ((BitVec.ofNat 8 (off / 4)).toNat * 4) = BitVec.ofNat 32 off := by
  congr 1; simp only [BitVec.toNat_ofNat]; omega

theorem fopG_regs {d a b : Nat} (hd : d % 4 = 0 ∧ d < 1024) (ha : a % 4 = 0 ∧ a < 1024)
    (hb : b % 4 = 0 ∧ b < 1024) (t : State) :
    (execAll (fopG d a b) t).regs 0 = t.regs 13 + BitVec.ofNat 32 d ∧
    (execAll (fopG d a b) t).regs 1 = t.regs 13 + BitVec.ofNat 32 a ∧
    (execAll (fopG d a b) t).regs 2 = t.regs 13 + BitVec.ofNat 32 b ∧
    (execAll (fopG d a b) t).regs 13 = t.regs 13 ∧ (execAll (fopG d a b) t).mem = t.mem := by
  have ed : d / 4 % 256 * 4 = d := by omega
  have ea : a / 4 % 256 * 4 = a := by omega
  have eb : b / 4 % 256 * 4 = b := by omega
  simp [fopG, spAdd, execAll, Instr.next, Instr.exec, State.setReg, State.sp, ed, ea, eb,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2]

/-- The trace of a field call on slots: the operand loads, the `bl`, the callee's trace at its
public values, then `Ψ`. -/
def fopTr (T : Word → (Nat → Word) → List Event) (base sp : Word) (o f d a b : Nat) (Ψ : TrP) :
    TrP :=
  Tr.cat (Tr.is (blockTr (fopG d a b) (base + BitVec.ofNat 32 o) [] []))
    (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize (fopG d a b)), .bl (blImm (o + seqSize (fopG d a b)) f), []⟩])
      (Tr.cat (Tr.is (T base (pubOf [sp + BitVec.ofNat 32 d, sp + BitVec.ofNat 32 a,
        sp + BitVec.ofNat 32 b, sp]))) Ψ))

/-- **A field call on frame slots.** The caller's window (`N` bytes below `sp0`) lies in its write
and read footprints, `sp = sp0 - top`, and the slots lie in `[sp, sp + top)`. -/
theorem fop_site {oF szF stF : Nat} {fn : Int → Int → Int}
    (hf : Routine.TSpec (fun _ : Unit => fieldR oF szF stF true fn) (fieldPub true))
    {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {R : Reg → Word}
    {t : State} {Q : State → Prop} {Ψ : TrP} {o top d a b : Nat} {rest : List Piece}
    (F : Caller base sp0 N Wc) (hWc : Sub [⟨sp0 - BitVec.ofNat 32 N, N⟩] Wc)
    (hRc : Sub [codeR base, ⟨sp0 - BitVec.ofNat 32 N, N⟩] Rc)
    (hd : SlotOk top d) (ha : SlotOk top a) (hb : SlotOk top b) (hda : Apart d a) (hdb : Apart d b)
    (hp : piecesAt B o (fopP oF d a b ++ rest) = true)
    (hok : siteOk cs (fieldR oF szF stF true fn) (fopG d a b) o top N (blImm (o + seqSize (fopG d a b)) oF) [] [] []
      = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 top) (hcode : CodeAt t.mem base B)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + piecesSize (fopP oF d a b)) → HiK hiRegs R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 top → CodeAt u.mem base B →
      MemEq [⟨sp0 - BitVec.ofNat 32 top - BitVec.ofNat 32 stF, stF⟩,
        ⟨sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 d, 32⟩] t.mem u.mem →
      ModP (feVal u.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 d))
        (fn (feVal t.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 a))
          (feVal t.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 b))) →
      piecesAt B (o + piecesSize (fopP oF d a b)) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (fopTr hf.T base (sp0 - BitVec.ofNat 32 top) o oF d a b Ψ) := by
  rw [← h13]
  have ok := hok
  simp only [siteOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  have hN : top + stF ≤ N := ok.1.2
  have ht4 : top % 4 = 0 := ok.2
  have := F.room; have := F.sp4; have := sp0.isLt
  obtain ⟨g0, g1, g2, g13, gm⟩ := fopG_regs ⟨hd.1, hd.2.2⟩ ⟨ha.1, ha.2.2⟩ ⟨hb.1, hb.2.2⟩ t
  have hsp : (t.regs 13).toNat = sp0.toNat - top := by
    rw [h13, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have ap : ∀ {x y : Nat}, Apart x y → SlotOk top x → SlotOk top y →
      EqOrDisj (t.regs 13 + BitVec.ofNat 32 x) (t.regs 13 + BitVec.ofNat 32 y) 32 := by
    intro x y hxy hx hy
    obtain ⟨-, _, _⟩ := hx; obtain ⟨-, _, _⟩ := hy
    rcases hxy with rfl | h | h
    · exact Or.inl rfl
    all_goals right; simp only [Frame.Disj, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [fopP, List.cons_append, List.nil_append] at hp
  unfold fopTr
  refine RoutinePieces.siteTK (hf.specT ()) F (fopG d a b) [] [] [] hp hok hpc hR h13 hcode ?_ ?_
    (traceAll_blockTr (L := []) (vs := []) rfl rfl hpc rfl) (Routine.tr_pub ?_)
    (fun u hu hRu h13u hcu hm hpost hrest => k u (by rw [hu, fopP_size, Nat.add_assoc]; rfl) hRu (by rw [h13u])
      hcu (by simpa [← h13, atCall, regions, Routine.win, fieldR, g0, g13, blState_regs _ _ _ 13] using hm)
      (by simpa [← h13, atCall, fieldR, g0, g1, g2, gm] using hpost) (by rw [fopP_size, ← Nat.add_assoc]; exact hrest))
  all_goals simp only [SiteSides, GlueSides, atCall, Routine.win, fieldR, fieldPub, ite_true, regions,
    List.map_nil, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
    blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, g0, g1, g2, g13]
  all_goals have := hd.1; have := hd.2; have := ha.1; have := ha.2; have := hb.1; have := hb.2
  · have hW1 : Sub [⟨sp0 - BitVec.ofNat 32 N, N⟩] Rc := fun r hr => hRc r (List.mem_cons_of_mem _ hr)
    refine ⟨by simp [Footprint.Sub],
      sub_trans (by fp_tac) hWc, ?_, by fp_tac, by fp_tac⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hRc _ List.mem_cons_self
    all_goals exact sub_trans (f := [_]) (by fp_tac) hW1 _ List.mem_cons_self
  · refine ⟨?_, ?_, ?_, ap hda hd ha, fun _ => ap hdb hd hb⟩ <;>
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

end M0Crypto.Release.Ed25519FieldSite
