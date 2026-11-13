import M0Crypto.Release.ReachPc

/-!
`PN W`: the pc-dependent write bound `PcWr W` together with "no executed instruction is one of the
two declared public loads".

`update` and `final` load `ctx.used` once, in their prologues, and the constant-time certificate
treats that load as public (`Env.pubLoads`). Showing the two runs load the same value needs the
state at that load to be the prologue's, so the rest of the function (and the callees) must never
execute it again. Each of the two loads is the only copy of its encoding in the artifact; a block
that does not contain it passes `NoLdrBlock` by `decide`, and `PN` records it per event.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- `ldr r7, [r4, #104]`, the declared public load of `update`. -/
def ldrU1 : Instr := .memImm .ldr 7 4 26
/-- `ldr r6, [r4, #104]`, the declared public load of `final`. -/
def ldrU2 : Instr := .memImm .ldr 6 4 26

def NoLdr (e : Event) : Prop := e.instr ≠ ldrU1 ∧ e.instr ≠ ldrU2

def NoLdrBlock (is : List Instr) : Bool := is.all fun i => i != ldrU1 && i != ldrU2

/-- The pc-dependent write bound, with the public loads excluded. -/
def PN (W : Word → Word → Prop) (z : State) (e : Event) : Prop := PcWr W z e ∧ NoLdr e

variable {base : Word} {W : Word → Word → Prop}

theorem NoLdr.of_ne {e : Event} (h1 : e.instr ≠ ldrU1) (h2 : e.instr ≠ ldrU2) : NoLdr e := ⟨h1, h2⟩

theorem PN.nil {s : State} {pc : Word} {i : Instr} (h1 : i ≠ ldrU1) (h2 : i ≠ ldrU2) :
    PN W s ⟨pc, i, []⟩ := ⟨PcWr.nil W s pc i, h1, h2⟩

theorem PN.pcWr {s : State} {e : Event} (h : PN W s e) : PcWr W s e := h.1

theorem traceAll_instr : ∀ (is : List Instr) (s : State) (e : Event), e ∈ traceAll is s → e.instr ∈ is
  | [], _, _, h => by cases h
  | i :: is, s, e, h => by
    simp only [traceAll, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (traceAll_instr is _ e h)

theorem noLdr_of_block {is : List Instr} (h : NoLdrBlock is = true) {i : Instr} (hi : i ∈ is) :
    i ≠ ldrU1 ∧ i ≠ ldrU2 := by
  simp only [NoLdrBlock, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h i hi

theorem ReachS.symBlockWN {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachS base (PN W) (execAll is s) Q)
    (hn : NoLdrBlock is = true := by decide) : ReachS base (PN W) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
  show BlockOk (fun _ e => (∀ y, Writes e.accesses y → W e.pc y) ∧ NoLdr e) is s
  rw [blockOk_events_iff]
  intro e he
  refine ⟨fun y hy => ?_, noLdr_of_block hn (traceAll_instr is s e he)⟩
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  obtain ⟨p, hp, o, ho', rfl⟩ :=
    M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
  rw [hep, hpc, ofNat_add_assoc]
  exact hrg p hp o ho' j hj

theorem ReachS.bcondPcN {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true →
      ReachS base (PN W) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachS base (PN W) (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachS base (PN W) s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht (PN.nil (by simp [ldrU1]) (by simp [ldrU2])) hT hF

theorem ReachS.blPcN {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat) (imm : BitVec 25)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : Release.blTarget off imm = BitVec.ofNat 32 tgt)
    (hq : ReachS base (PN W) ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachS base (PN W) s Q :=
  ReachS.bl hb off tgt imm hpc ho hi hsz ht (PN.nil (by simp [ldrU1]) (by simp [ldrU2])) hq

theorem ReachS.bPcN {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachS base (PN W) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachS base (PN W) s Q :=
  ReachS.b hb off tgt imm hpc ho hi hsz ht (PN.nil (by simp [ldrU1]) (by simp [ldrU2])) hq

/-- An instruction that writes nothing and is not a declared load. -/
theorem ReachS.stepNWN {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, ¬ Writes (i.accesses s) y)
    (hq : ReachS base (PN W) s1 Q) (hn : NoLdrBlock [i] = true := by decide) :
    ReachS base (PN W) s Q := by
  have hn' := noLdr_of_block hn (List.mem_singleton_self i)
  exact ReachS.step hb off i hpc ho hi hsz ha hex
    ⟨fun y hy => absurd hy (hw y), hn'⟩ hq

/-- An instruction whose writes the bound `W` allows at its own pc. -/
theorem ReachS.stepWN {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → W (base + BitVec.ofNat 32 off) y)
    (hq : ReachS base (PN W) s1 Q) (hn : NoLdrBlock [i] = true := by decide) :
    ReachS base (PN W) s Q := by
  have hn' := noLdr_of_block hn (List.mem_singleton_self i)
  refine ReachS.step hb off i hpc ho hi hsz ha hex ⟨fun y hy => ?_, hn'⟩ hq
  show W s.pc y
  rw [hpc]; exact hw y hy

end M0Crypto.Release
