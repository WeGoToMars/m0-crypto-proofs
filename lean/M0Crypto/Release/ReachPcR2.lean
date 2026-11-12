import M0Crypto.Release.ReachPcR
import M0Crypto.Release.ReachPcL
import M0Crypto.Release.ReachPcL2

/-!
`PLR` / `PL2R`: `PL` / `PL2` together with the read bound of `PNR`, for the prologue of `update`
and of `final`, whose declared public load is itself a load site. Also the load-and-write steps
of the read-bound family that `ReachPcR` leaves out.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

variable {base : Word} {W : Word → Word → Prop} {R : Word → Prop} {Ld : Instr → Bool}

def PLR (Ld : Instr → Bool) (W : Word → Word → Prop) (F : State → Prop) (R : Word → Prop)
    (z : State) (e : Event) : Prop :=
  PL W F z e ∧ (Ld e.instr = true → ∀ y, Reads e.accesses y → R y)

def PL2R (Ld : Instr → Bool) (W : Word → Word → Prop) (F : State → Prop) (R : Word → Prop)
    (z : State) (e : Event) : Prop :=
  PL2 W F z e ∧ (Ld e.instr = true → ∀ y, Reads e.accesses y → R y)

theorem PNR.toPLR (F : State → Prop) {z : State} {e : Event} (h : PNR Ld W R z e) :
    PLR Ld W F R z e := ⟨PN.toPL F h.1, h.2⟩

theorem PNR.toPL2R (F : State → Prop) {z : State} {e : Event} (h : PNR Ld W R z e) :
    PL2R Ld W F R z e := ⟨PN.toPL2 F h.1, h.2⟩

theorem PLR.pl {F : State → Prop} {z : State} {e : Event} (h : PLR Ld W F R z e) : PL W F z e := h.1
theorem PL2R.pl2 {F : State → Prop} {z : State} {e : Event} (h : PL2R Ld W F R z e) :
    PL2 W F z e := h.1

theorem blockOk_and {P Q : State → Event → Prop} :
    ∀ (is : List Instr) (s : State), BlockOk P is s → BlockOk Q is s →
      BlockOk (fun z e => P z e ∧ Q z e) is s
  | [], _, _, _ => trivial
  | i :: is, s, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨⟨h1, h3⟩, blockOk_and is _ h2 h4⟩

/-- The read half of a block: every `Ld` instruction's read is in `R`, given the symbolic check
and the region bound. -/
theorem blockOk_reads (Ld : Instr → Bool) (R : Word → Prop) (rr : List (Reg × Word × Nat))
    (is : List Instr) (hf : is.all Instr.falls = true) (s : State)
    (hrr : ∀ p ∈ rr, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (hrc : M0Crypto.Sym.readChk Ld rr is = true) :
    BlockOk (fun _ e => Ld e.instr = true → ∀ y, Reads e.accesses y → R y) is s := by
  rw [blockOk_events_iff]
  intro e he hld y hy
  obtain ⟨p, hp, o, ho', rfl⟩ :=
    M0Crypto.Sym.readChk_sound Ld rr is (M0Crypto.Sym.sound_all hf) s hrc e he hld y hy
  exact hrr p hp o ho'

theorem ReachS.symBlockWLR {s : State} {Q : State → Prop} (F : State → Prop)
    (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg rr : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (hrr : ∀ p ∈ rr, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hsplit : is = is.dropLast ++ [ldrU1])
    (hn : NoLdrBlock is.dropLast = true)
    (hF : F (execAll is.dropLast s))
    (hrc : M0Crypto.Sym.readChk Ld rr is = true)
    (hq : ReachS base (PLR Ld W F R) (execAll is s) Q) : ReachS base (PLR Ld W F R) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
  have hpl : BlockOk (PL W F) is s := by
    have h1 : ReachS base (PL W F) s Q → True := fun _ => trivial
    clear h1
    -- the `PL` half, as in `symBlockWL`
    have hev : ∀ e ∈ traceAll is s, ∀ y, Writes e.accesses y → W e.pc y := by
      intro e he y hy
      obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
      obtain ⟨p, hp, o, ho', rfl⟩ :=
        M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
      rw [hep, hpc, ofNat_add_assoc]
      exact hrg p hp o ho' j hj
    have key : BlockOk (PL W F) (is.dropLast ++ [ldrU1]) s := by
      rw [blockOk_append]
      have hmem : ∀ e ∈ traceAll is.dropLast s, e ∈ traceAll is s := by
        intro e he
        rw [hsplit, traceAll_append]
        exact List.mem_append_left _ he
      refine ⟨?_, ?_⟩
      · refine BlockOk.mono (P := fun _ e => (∀ y, Writes e.accesses y → W e.pc y) ∧ e.instr ≠ ldrU2 ∧
          e.instr ≠ ldrU1) (fun _ e h => ⟨h.1, h.2.1, fun h1 => absurd h1 h.2.2⟩) _ _ ?_
        rw [blockOk_events_iff (p := fun e => (∀ y, Writes e.accesses y → W e.pc y) ∧ e.instr ≠ ldrU2 ∧
          e.instr ≠ ldrU1)]
        intro e he
        have h := noLdr_of_block hn (traceAll_instr _ _ e he)
        exact ⟨hev e (hmem e he), h.2, h.1⟩
      · refine ⟨⟨?_, ldrU1_ne_ldrU2, fun _ => hF⟩, trivial⟩
        apply hev
        rw [hsplit, traceAll_append]
        refine List.mem_append_right _ ?_
        simp [traceAll]
    rwa [← hsplit] at key
  exact blockOk_and is s hpl (blockOk_reads Ld R rr is hf s hrr hrc)

theorem ReachS.symBlockWL2R {s : State} {Q : State → Prop} (F : State → Prop)
    (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg rr : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (hrr : ∀ p ∈ rr, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hsplit : is = is.dropLast ++ [ldrU2])
    (hn : NoLdrBlock is.dropLast = true)
    (hF : F (execAll is.dropLast s))
    (hrc : M0Crypto.Sym.readChk Ld rr is = true)
    (hq : ReachS base (PL2R Ld W F R) (execAll is s) Q) : ReachS base (PL2R Ld W F R) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
  have hpl : BlockOk (PL2 W F) is s := by
    have hev : ∀ e ∈ traceAll is s, ∀ y, Writes e.accesses y → W e.pc y := by
      intro e he y hy
      obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
      obtain ⟨p, hp, o, ho', rfl⟩ :=
        M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
      rw [hep, hpc, ofNat_add_assoc]
      exact hrg p hp o ho' j hj
    have key : BlockOk (PL2 W F) (is.dropLast ++ [ldrU2]) s := by
      rw [blockOk_append]
      have hmem : ∀ e ∈ traceAll is.dropLast s, e ∈ traceAll is s := by
        intro e he
        rw [hsplit, traceAll_append]
        exact List.mem_append_left _ he
      refine ⟨?_, ?_⟩
      · refine BlockOk.mono (P := fun _ e => (∀ y, Writes e.accesses y → W e.pc y) ∧ e.instr ≠ ldrU1 ∧
          e.instr ≠ ldrU2) (fun _ e h => ⟨h.1, h.2.1, fun h1 => absurd h1 h.2.2⟩) _ _ ?_
        rw [blockOk_events_iff (p := fun e => (∀ y, Writes e.accesses y → W e.pc y) ∧ e.instr ≠ ldrU1 ∧
          e.instr ≠ ldrU2)]
        intro e he
        have h := noLdr_of_block hn (traceAll_instr _ _ e he)
        exact ⟨hev e (hmem e he), h.1, h.2⟩
      · refine ⟨⟨?_, ldrU1_ne_ldrU2.symm, fun _ => hF⟩, trivial⟩
        apply hev
        rw [hsplit, traceAll_append]
        refine List.mem_append_right _ ?_
        simp [traceAll]
    rwa [← hsplit] at key
  exact blockOk_and is s hpl (blockOk_reads Ld R rr is hf s hrr hrc)

theorem ReachS.blPcNR {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat) (imm : BitVec 25)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : Aead.blTarget off imm = BitVec.ofNat 32 tgt)
    (hq : ReachS base (PNR Ld W R) ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachS base (PNR Ld W R) s Q :=
  ReachS.bl hb off tgt imm hpc ho hi hsz ht (PNR.nil (by simp [ldrU1]) (by simp [ldrU2])) hq

/-- An instruction whose writes the bound `W` allows at its own pc, and which is not an `Ld`
instruction. -/
theorem ReachS.stepWNR {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → W (base + BitVec.ofNat 32 off) y)
    (hq : ReachS base (PNR Ld W R) s1 Q) (hn : NoLdrBlock [i] = true := by decide)
    (hl : Ld i = false := by decide) : ReachS base (PNR Ld W R) s Q := by
  have hn' := noLdr_of_block hn (List.mem_singleton_self i)
  refine ReachS.step hb off i hpc ho hi hsz ha hex ⟨⟨fun y hy => ?_, hn'⟩, fun h => ?_⟩ hq
  · show W s.pc y
    rw [hpc]; exact hw y hy
  · have h' : Ld i = true := h
    rw [hl] at h'; exact absurd h' (by decide)

/-- A load that writes nothing: its reads are in `R`. -/
theorem ReachS.stepRNR {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, ¬ Writes (i.accesses s) y)
    (hr : ∀ y, Reads (i.accesses s) y → R y)
    (hq : ReachS base (PNR Ld W R) s1 Q) (hn : NoLdrBlock [i] = true := by decide) :
    ReachS base (PNR Ld W R) s Q := by
  have hn' := noLdr_of_block hn (List.mem_singleton_self i)
  exact ReachS.step hb off i hpc ho hi hsz ha hex
    ⟨⟨fun y hy => absurd hy (hw y), hn'⟩, fun _ y hy => hr y hy⟩ hq

end M0Crypto.Release
