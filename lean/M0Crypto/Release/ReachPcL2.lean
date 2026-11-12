import M0Crypto.Release.ReachPcL

/-! `PL2 W F`: the mirror of `PL` for `ldrU2` (the final prologue's load). -/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

def PL2 (W : Word → Word → Prop) (F : State → Prop) (z : State) (e : Event) : Prop :=
  PcWr W z e ∧ e.instr ≠ ldrU1 ∧ (e.instr = ldrU2 → F z)

theorem PN.toPL2 {W : Word → Word → Prop} (F : State → Prop) {z : State} {e : Event}
    (h : PN W z e) : PL2 W F z e :=
  ⟨h.1, h.2.1, fun e1 => absurd e1 h.2.2⟩

theorem PL2.pcWr {W : Word → Word → Prop} {F : State → Prop} {z : State} {e : Event}
    (h : PL2 W F z e) : PcWr W z e := h.1


variable {base : Word} {W : Word → Word → Prop}

theorem ReachS.symBlockWL2 {s : State} {Q : State → Prop} (F : State → Prop)
    (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hsplit : is = is.dropLast ++ [ldrU2])
    (hn : NoLdrBlock is.dropLast = true)
    (hF : F (execAll is.dropLast s))
    (hq : ReachS base (PL2 W F) (execAll is s) Q) : ReachS base (PL2 W F) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
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

end M0Crypto.Release
