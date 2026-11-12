import M0Crypto.Release.ReachPcN

/-!
`PL W F`: `PN` relaxed at exactly one place. The first-pass `ldr` of a prologue (`ldrU1`) may
execute, provided the state before it satisfies `F`; `ldrU2` stays excluded. `update` uses it for
its own prologue, so a run that satisfies `PL` has exactly one `ldrU1` event, at a state with `F`.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

def PL (W : Word → Word → Prop) (F : State → Prop) (z : State) (e : Event) : Prop :=
  PcWr W z e ∧ e.instr ≠ ldrU2 ∧ (e.instr = ldrU1 → F z)

theorem PN.toPL {W : Word → Word → Prop} (F : State → Prop) {z : State} {e : Event}
    (h : PN W z e) : PL W F z e :=
  ⟨h.1, h.2.2, fun e1 => absurd e1 h.2.1⟩

theorem PL.pcWr {W : Word → Word → Prop} {F : State → Prop} {z : State} {e : Event}
    (h : PL W F z e) : PcWr W z e := h.1

theorem ldrU1_ne_ldrU2 : ldrU1 ≠ ldrU2 := by simp [ldrU1, ldrU2]

theorem blockOk_append {P : State → Event → Prop} :
    ∀ (a b : List Instr) (s : State),
      BlockOk P (a ++ b) s ↔ BlockOk P a s ∧ BlockOk P b (execAll a s)
  | [], b, s => by simp [BlockOk, execAll]
  | i :: a, b, s => by
    simp only [List.cons_append, BlockOk, blockOk_append a b, execAll, and_assoc]

variable {base : Word} {W : Word → Word → Prop}

theorem ReachS.symBlockWL {s : State} {Q : State → Prop} (F : State → Prop)
    (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hsplit : is = is.dropLast ++ [ldrU1])
    (hn : NoLdrBlock is.dropLast = true)
    (hF : F (execAll is.dropLast s))
    (hq : ReachS base (PL W F) (execAll is s) Q) : ReachS base (PL W F) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
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

end M0Crypto.Release
