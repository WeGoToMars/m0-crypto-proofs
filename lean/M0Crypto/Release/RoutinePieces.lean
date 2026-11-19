import M0Crypto.Release.Routine
import M0Crypto.Release.Layout

set_option linter.unusedSimpArgs false

/-!
# Routines as lists of pieces

A routine's code is a sequence of pieces: straight-line blocks, calls, conditional branches and
unconditional branches.
`piecesAt B o ps` checks all of them against the artifact bytes at once, so a routine's code is
one decided fact, and each piece lies at the routine's entry plus the sizes of the pieces before
it (`piecesSize`). A lemma about an assembly macro takes the check of the macro's pieces at any
offset `o`: it is proved once and used wherever the macro occurs.

Also here, for such lemmas:
- `site`, the call-site rule from a piece check;
- `cmp_bne`, the status test `cmp r, #0; bne tgt`;
- `ptrOff`, the idiom `movs rd, rs; adds rd, #off` (no `adds` when `off = 0`), with the register
  it leaves for any `off`;
- `Holds`, bytes a caller carries across calls apart from what they write;
- `site_once`, which evaluates a call site's side conditions once and closes them against
  abstract caller footprints: a containment in the caller's footprint goes through a containment
  the caller states (`fp_via`).
-/

namespace M0Crypto.Release.RoutinePieces

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release (brImm11)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

variable {base : Word}

/-! ## Footprints -/

theorem sub_trans {f g h : List Rgn} (h1 : Sub f g) (h2 : Sub g h) : Sub f h := by
  intro r hr
  obtain ⟨q, hq, a1, a2, -⟩ := h1 r hr
  obtain ⟨p, hp, b1, b2, b3⟩ := h2 q hq
  exact ⟨p, hp, by omega, by omega, b3⟩

theorem sub_append {f g h : List Rgn} (h1 : Sub f h) (h2 : Sub g h) : Sub (f ++ g) h := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · exact h2 r hr

/-- The byte lists `ks` lie in memory `m`: facts a chain of rules carries along. -/
def Holds (m : Mem) (ks : List (Rgn × List (BitVec 8))) : Prop :=
  ∀ p ∈ ks, Footprint.bytesAt m p.1.a p.1.n = p.2

/-- One more fact for `Holds`, and the facts back. -/
theorem Holds.cons {m : Mem} {ks : List (Rgn × List (BitVec 8))} {r : Rgn} {v : List (BitVec 8)}
    (h : Holds m ks) (hv : Footprint.bytesAt m r.a r.n = v) : Holds m ((r, v) :: ks) :=
  fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hv
    · exact h p hp
theorem Holds.head {m : Mem} {ks : List (Rgn × List (BitVec 8))} {r : Rgn} {v : List (BitVec 8)}
    (h : Holds m ((r, v) :: ks)) : Footprint.bytesAt m r.a r.n = v :=
  h _ (List.mem_cons_self ..)
theorem Holds.tail {m : Mem} {ks : List (Rgn × List (BitVec 8))} {p : Rgn × List (BitVec 8)}
    (h : Holds m (p :: ks)) : Holds m ks := fun q hq => h q (List.mem_cons_of_mem _ hq)
theorem Holds.nil {m : Mem} : Holds m [] := fun _ h => nomatch h

/-- `Holds` across a frame inside `V`, the regions of `ks` lying apart from `V`. -/
theorem Holds.carry {m m' : Mem} {ks : List (Rgn × List (BitVec 8))} {W V : List Rgn}
    (h : Holds m ks) (hm : MemEq W m m') (hk : Sep (ks.map Prod.fst) V) (hs : Sub W V) :
    Holds m' ks := fun p hp => by
  have hp' : p.1 ∈ ks.map Prod.fst := List.mem_map_of_mem hp
  have h1 : Sep [p.1] V := fun r hr q hq => by
    rw [List.mem_singleton.mp hr]; exact hk _ hp' q hq
  rw [hm.bytes (hs.sep h1.symm).symm]; exact h p hp

/-- Bytes apart from a word store are unchanged. -/
theorem bytesAt_write32_disj {m : Mem} {a v b : Word} {n : Nat} (h : Frame.Disj a 4 b n) :
    Footprint.bytesAt (M0Crypto.Armv6M.write32 m a v) b n = Footprint.bytesAt m b n :=
  Footprint.bytesAt_congr fun i hi => M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => by
    obtain ⟨h1, h2, h3⟩ := h
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := a.isLt; have := b.isLt
    omega

/-! ## Pieces -/

/-- A piece of a routine's code. -/
inductive Piece where
  /-- A straight-line block. -/
  | seq (g : List Instr)
  /-- `bl tgt`. -/
  | call (tgt : Nat)
  /-- `b<cond> tgt`. -/
  | bcond (cond : BitVec 4) (tgt : Nat)
  /-- `b tgt`. -/
  | b (tgt : Nat)
  /-- `b` over the block `g` and `n` data bytes (a literal pool in the code), then `g`; the data
  bytes are not instructions. -/
  | over (g : List Instr) (n : Nat)

/-- The instructions of a piece at offset `o`. -/
def Piece.instrs (o : Nat) : Piece → List Instr
  | .seq g => g
  | .call tgt => [.bl (blImm o tgt)]
  | .bcond c tgt => [.bcond c (brImm8 o tgt)]
  | .b tgt => [.b (brImm11 o tgt)]
  | .over g n => .b (brImm11 o (o + brSize + seqSize g + n)) :: g

def Piece.size : Piece → Nat
  | .seq g => seqSize g
  | .call _ => blSize
  | .bcond _ _ => brSize
  | .b _ => brSize
  | .over g n => brSize + seqSize g + n

def piecesSize (ps : List Piece) : Nat := (ps.map Piece.size).sum

@[simp] theorem Piece.size_seq (g : List Instr) : (Piece.seq g).size = seqSize g := rfl
@[simp] theorem Piece.size_call (tgt : Nat) : (Piece.call tgt).size = 4 := rfl
@[simp] theorem Piece.size_bcond (c : BitVec 4) (tgt : Nat) : (Piece.bcond c tgt).size = 2 := rfl
@[simp] theorem Piece.size_b (tgt : Nat) : (Piece.b tgt).size = 2 := rfl
@[simp] theorem Piece.size_over (g : List Instr) (n : Nat) : (Piece.over g n).size = 2 + seqSize g + n := rfl

@[simp] theorem piecesSize_nil : piecesSize [] = 0 := rfl

@[simp] theorem piecesSize_cons (p : Piece) (ps : List Piece) :
    piecesSize (p :: ps) = p.size + piecesSize ps := by
  simp [piecesSize]

theorem piecesSize_append (ps qs : List Piece) :
    piecesSize (ps ++ qs) = piecesSize ps + piecesSize qs := by
  simp [piecesSize]

/-- The pieces `ps` lie one after the other from offset `o` of `bytes`. -/
def piecesAt (bytes : List (BitVec 8)) : Nat → List Piece → Bool
  | _, [] => true
  | o, p :: ps => seqAt bytes o (p.instrs o) && piecesAt bytes (o + p.size) ps

/-- `piecesAt` on the bytes from the first piece on (see `seqScan`). -/
def piecesScan : List (BitVec 8) → Nat → List Piece → Bool
  | _, _, [] => true
  | bs, o, p :: ps => seqScan bs (p.instrs o) && piecesScan (bs.drop p.size) (o + p.size) ps

theorem piecesAt_eq_scan (bytes : List (BitVec 8)) :
    ∀ (ps : List Piece) (o : Nat), piecesAt bytes o ps = piecesScan (bytes.drop o) o ps
  | [], _ => rfl
  | p :: ps, o => by
    have e : (bytes.drop o).drop p.size = bytes.drop (o + p.size) := by
      simp [List.drop_drop, Nat.add_comm]
    simp only [piecesAt, piecesScan, seqAt_eq_scan, e, piecesAt_eq_scan bytes ps]

theorem piecesAt_append (bytes : List (BitVec 8)) :
    ∀ (ps qs : List Piece) (o : Nat),
      piecesAt bytes o (ps ++ qs) = (piecesAt bytes o ps && piecesAt bytes (o + piecesSize ps) qs)
  | [], _, _ => by simp [piecesAt]
  | p :: ps, qs, o => by
    simp only [List.cons_append, piecesAt, piecesSize_cons, Bool.and_assoc]
    rw [piecesAt_append bytes ps qs, Nat.add_assoc]

theorem piecesAt_cons {bytes : List (BitVec 8)} {o : Nat} {p : Piece} {ps : List Piece}
    (h : piecesAt bytes o (p :: ps) = true) :
    seqAt bytes o (p.instrs o) = true ∧ piecesAt bytes (o + p.size) ps = true := by
  simpa [piecesAt] using h

/-! ## Rules that consume pieces

Each rule takes the check of its pieces followed by any `rest`, and hands the check of `rest` at
the next offset to its continuation, so a chain of rules walks a routine's code without naming an
offset. -/

theorem blSize_eq : blSize = 4 := rfl

/-- **A call site** `g; bl f`, the first two pieces, with its trace, for a callee that may change
the registers `f.clob` (`ReachFT.siteK`). -/
theorem siteTK {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf) {cs : List (Nat × Nat)}
    {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop}
    {Ψ Φc : TrP} {G : List Event} {o d : Nat} {rest : List Piece}
    (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hp : piecesAt B o (.seq g :: .call f.entry :: rest) = true)
    (hok : siteOk cs f g o d N (blImm (o + seqSize g) f.entry) al wg rg = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (hG : traceAll g t = G) (hΦ : Φf base (atCall base f g o t) = Φc)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → HiK f.clob R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B →
      MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) → piecesAt B (o + seqSize g + 4) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize g),
        .bl (blImm (o + seqSize g) f.entry), []⟩]) (Tr.cat Φc Ψ))) := by
  obtain ⟨h1, h2⟩ := piecesAt_cons hp
  obtain ⟨h2, h3⟩ := piecesAt_cons h2
  simp only [Piece.instrs, Piece.size, blSize_eq] at h1 h2 h3
  exact ReachFT.siteK hf F g al wg rg h1 (instrAt_of_seqAt h2) hpc hR h13 hcode hs hpre hG hΦ
    (fun u a b c d e f => k u a b c d e f h3) hok

/-- **A call site** `g; bl f`, the first two pieces, with its trace (`ReachFT.site`). -/
theorem siteT {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf) {cs : List (Nat × Nat)}
    {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop}
    {Ψ Φc : TrP} {G : List Event} {o d : Nat} {rest : List Piece}
    (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hp : piecesAt B o (.seq g :: .call f.entry :: rest) = true)
    (hok : siteOk cs f g o d N (blImm (o + seqSize g) f.entry) al wg rg = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (hG : traceAll g t = G) (hΦ : Φf base (atCall base f g o t) = Φc)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → Hi R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B →
      MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) → piecesAt B (o + seqSize g + 4) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ)
    (hcl : f.clob = [] := by rfl) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize g),
        .bl (blImm (o + seqSize g) f.entry), []⟩]) (Tr.cat Φc Ψ))) :=
  siteTK hf F g al wg rg hp hok hpc hR h13 hcode hs hpre hG hΦ
    fun u a h c d e f g => k u a (hcl ▸ h).hi c d e f g

/-- **A call site** `g; bl f`, the first two pieces (`ReachF.site`). -/
theorem site {f : Routine} (hf : f.Spec) {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat}
    {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop} {o d : Nat}
    {rest : List Piece}
    (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hp : piecesAt B o (.seq g :: .call f.entry :: rest) = true)
    (hok : siteOk cs f g o d N (blImm (o + seqSize g) f.entry) al wg rg = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → Hi R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B →
      MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) → piecesAt B (o + seqSize g + 4) rest = true →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q)
    (hcl : f.clob = [] := by rfl) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q :=
  (siteT hf.specT F g al wg rg hp hok hpc hR h13 hcode hs hpre rfl rfl
    (fun u a b c d e f g => ReachS.toT (k u a b c d e f g)) hcl).toS

/-- **A glue block** `g`, the first piece (`ReachF.glue`). -/
theorem glue {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {o d : Nat} {rest : List Piece} (F : Caller base sp0 N Wc) (g : List Instr)
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat))
    (hp : piecesAt B o (.seq g :: rest) = true) (hok : glueOk cs g o d N al wg rg = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : GlueSides t Rc Wc al wg rg)
    (k : (execAll g t).pc = base + BitVec.ofNat 32 (o + seqSize g) →
      (execAll g t).regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt (execAll g t).mem base B →
      MemEq (regions t wg) t.mem (execAll g t).mem → piecesAt B (o + seqSize g) rest = true →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) (execAll g t) Q) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q := by
  obtain ⟨h1, h2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at h1 h2
  exact ReachF.glue F g al wg rg h1 hpc h13 hcode hs (fun a b c d => k a b c d h2) hok

/-! ## The status test -/

/-- The decided checks of `cmp r, #0; bne tgt` at `o`: the compare as a glue block, the branch in
the caller's code and the artifact, reaching `tgt`. -/
def bneOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt d N : Nat) (r : LowReg) : Bool :=
  glueOk cs [.cmpImm r 0] o d N [] [] [] && rangesSub [(o + 2, o + 4)] cs &&
  decide (o + 4 ≤ BS) &&
  decide (BitVec.ofNat 32 (o + 2) + 4#32 + (brImm8 (o + 2) tgt ++ 0#1).signExtend 32 =
    BitVec.ofNat 32 tgt)

theorem cmp0_z (r : LowReg) (t : State) :
    (execAll [.cmpImm r 0] t).z = (t.regs r.toReg == 0#32) := by
  have e : t.regs r.toReg + 4294967295#32 + 1#32 = t.regs r.toReg := by bv_omega
  simp [execAll, Instr.next, Instr.exec, addFlags, State.setNZCV, State.setNZ, State.reg,
    State.setReg, addWithCarry_true_fst, e]

theorem cmp0_regs (r : LowReg) (t : State) (i : Reg) (h15 : i.val ≠ 15) :
    (execAll [.cmpImm r 0] t).regs i = t.regs i :=
  execAll_regs_other _ t i h15 (by simp [Instr.dsts])

/-- **`cmp r, #0; bne tgt`**: a zero `r` falls through to `o + 4`, any other value branches to
`tgt`. Each continuation receives a state with the registers other than `pc`, and the memory, of
`t`; the fall-through also receives the check of `rest`. -/
theorem cmp_bne {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {o d tgt : Nat} {rest : List Piece} (F : Caller base sp0 N Wc) (r : LowReg)
    (hp : piecesAt B o (.seq [.cmpImm r 0] :: .bcond 1 tgt :: rest) = true)
    (hok : bneOk cs o tgt d N r = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B)
    (kz : t.regs r.toReg = 0#32 → ∀ u, u.pc = base + BitVec.ofNat 32 (o + 4) →
      (∀ i : Reg, i.val ≠ 15 → u.regs i = t.regs i) → u.mem = t.mem →
      piecesAt B (o + 4) rest = true →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q)
    (knz : t.regs r.toReg ≠ 0#32 → ∀ u, u.pc = base + BitVec.ofNat 32 tgt →
      (∀ i : Reg, i.val ≠ 15 → u.regs i = t.regs i) → u.mem = t.mem →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q := by
  obtain ⟨h1, h2⟩ := piecesAt_cons hp
  obtain ⟨h2, h3⟩ := piecesAt_cons h2
  simp only [Piece.instrs, Piece.size] at h1 h2 h3
  have hs2 : seqSize [Instr.cmpImm r 0] = 2 := rfl
  rw [hs2] at h2 h3
  have hb : brSize = 2 := rfl
  rw [hb] at h3
  simp only [bneOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hg, hcs⟩, hsz⟩, ht⟩ := hok
  have hd : d ≤ N := by
    simp only [glueOk, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.2
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  refine ReachF.glue F [.cmpImm r 0] [] [] [] h1 hpc h13 hcode
    ⟨by simp, by simp [regions, Footprint.Sub], by simp [regions, Footprint.Sub]⟩ (fun p1 s1 c1 _ => ?_) hg
  rw [hs2] at p1
  have hreg := cmp0_regs r t
  have ho2 : (o + 2) % 2 = 0 := by
    simp only [glueOk, Bool.and_eq_true, beq_iff_eq] at hg; omega
  refine ReachF.bcond hb2 tgt 1 _ p1 ho2 (instrAt_of_seqAt h2) hsz ht
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega))) ⟨d, hd, s1⟩
    (fun hT => ?_) (fun hF => ?_)
  · have hz : t.regs r.toReg ≠ 0#32 := by
      simp only [condPassed, cmp0_z] at hT
      simpa using hT
    refine knz hz _ (by simp [State.setReg, State.pc]) (fun i hi => ?_) rfl
    rw [← hreg i hi]; simp [State.setReg, show i ≠ 15 from fun h => hi (by rw [h]; rfl)]
  · have hz : t.regs r.toReg = 0#32 := by
      simp only [condPassed, cmp0_z] at hF
      simpa using hF
    refine kz hz _ (by simp [State.setReg, State.pc]) (fun i hi => ?_) rfl h3
    rw [← hreg i hi]; simp [State.setReg, show i ≠ 15 from fun h => hi (by rw [h]; rfl)]

/-! ## `rd = rs + off` -/

/-- `movs rd, rs`, then `adds rd, #off` unless `off = 0`. -/
def ptrOff (rd rs : LowReg) (off : Nat) : List Instr :=
  .lslImm rd rs 0 :: if off = 0 then [] else [.addImm8 rd (BitVec.ofNat 8 off)]

theorem setWidth_ofNat8 {n : Nat} (h : n < 256) :
    (BitVec.ofNat 8 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ptrOff_regs (rd rs : LowReg) {off : Nat} (hoff : off < 256) (s : State) (r : Reg)
    (h15 : r ≠ 15) :
    (execAll (ptrOff rd rs off) s).regs r =
      if r = rd.toReg then s.regs rs.toReg + BitVec.ofNat 32 off else s.regs r := by
  have h15' : (15 : Reg) ≠ r := fun h => h15 h.symm
  by_cases h0 : off = 0
  · subst h0
    by_cases hr : r = rd.toReg <;>
      simp [ptrOff, execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.reg, lslC, hr,
        h15, h15']
  · by_cases hr : r = rd.toReg <;>
      simp [ptrOff, h0, execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZCV,
        State.reg, lslC, addFlags, M0Crypto.Proofs.addWithCarry_fst, hr, h15, h15', setWidth_ofNat8 hoff]

theorem ptrOff_mem (rd rs : LowReg) (off : Nat) (s : State) :
    (execAll (ptrOff rd rs off) s).mem = s.mem := by
  by_cases h0 : off = 0
  · subst h0; simp [ptrOff, execAll, Instr.next, Instr.exec, State.setReg, State.setNZC]
  · simp [ptrOff, h0, execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZCV,
      addFlags]

/-! ## Side conditions against abstract caller footprints -/

open Lean in
/-- Terms as `simp` arguments. -/
def lemmaArgs (ts : Syntax.TSepArray `term ",") :
    MacroM (Array (TSyntax [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
      ``Lean.Parser.Tactic.simpLemma])) :=
  ts.getElems.mapM fun t => do
    let l ← `(Lean.Parser.Tactic.simpLemma| $t:term)
    return ⟨l.raw⟩

/-- `fp_via [us] [h₁, …]` closes one footprint goal whose terms are already evaluated: a
containment through one of the stated containments `hᵢ`, anything else directly, each by
`simp only [us]` and `fp_tac`. -/
syntax "fp_via" " [" term,* "]" " [" term,* "]" : tactic

macro_rules
  | `(tactic| fp_via [$us,*] []) => do
    let a ← lemmaArgs us
    `(tactic| ((try simp only [List.cons_append, List.nil_append, $a,*]) <;> fp_tac))
  | `(tactic| fp_via [$us,*] [$h]) => do
    let a ← lemmaArgs us
    `(tactic| first
      | (refine RoutinePieces.sub_trans ?_ $h; (try simp only [List.cons_append, List.nil_append, $a,*]) <;> fp_tac)
      | ((try simp only [List.cons_append, List.nil_append, $a,*]) <;> fp_tac))
  | `(tactic| fp_via [$us,*] [$h, $hs,*]) => do
    let a ← lemmaArgs us
    `(tactic| first
      | (refine RoutinePieces.sub_trans ?_ $h; (try simp only [List.cons_append, List.nil_append, $a,*]) <;> fp_tac)
      | fp_via [$us,*] [$hs,*])

/-- `site_once [ts] [us] [h₁, …]` closes the `SiteSides` or `GlueSides` of a call site or glue
block: one `site_simp [ts]` evaluates the site for all conditions at once, then each condition
closes by `fp_via [us] [h₁, …]`. -/
macro "site_once" " [" ts:term,* "]" " [" us:term,* "]" " [" hs:term,* "]" : tactic => `(tactic|
  (((try simp only [SiteSides, GlueSides]); site_simp [$ts,*]) <;> (repeat' apply And.intro) <;>
    fp_via [$us,*] [$hs,*]))

/-- `store_simp at h` removes word stores from the bytes `h` reads, each store's disjointness
from the bytes proved by `fp_tac`. -/
macro "store_simp" " at " h:ident : tactic => `(tactic|
  simp (disch := fp_tac) only [RoutinePieces.bytesAt_write32_disj] at $h:ident)

end M0Crypto.Release.RoutinePieces
