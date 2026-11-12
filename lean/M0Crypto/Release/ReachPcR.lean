import M0Crypto.Release.ReachPcN
import M0Crypto.Release.SymReadChk

/-!
`PNR Ld W R`: `PN W` together with a read bound on the instructions in `Ld`.

`Ld` is the set of instructions at a routine's *load sites* (loads through a caller pointer, as
the constant-time certificate classifies them). Every byte such an instruction reads satisfies
`R`. Every other read of the routine is bounded by the certificate window (`xfer_reads`), so it
needs no per-block annotation. A block with no `Ld` instruction passes `readChk Ld [] is`.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- `PN W`, and every read of an `Ld` instruction satisfies `R`. -/
def PNR (Ld : Instr → Bool) (W : Word → Word → Prop) (R : Word → Prop) (z : State) (e : Event) :
    Prop :=
  PN W z e ∧ (Ld e.instr = true → ∀ y, Reads e.accesses y → R y)

variable {base : Word} {W : Word → Word → Prop} {R : Word → Prop} {Ld : Instr → Bool}

theorem PNR.pn {z : State} {e : Event} (h : PNR Ld W R z e) : PN W z e := h.1

theorem PNR.nil {s : State} {pc : Word} {i : Instr} (h1 : i ≠ ldrU1) (h2 : i ≠ ldrU2) :
    PNR Ld W R s ⟨pc, i, []⟩ :=
  ⟨PN.nil h1 h2, fun _ y hy => by obtain ⟨a, ha, _⟩ := hy; cases ha⟩

theorem ReachS.symBlockWNR {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg rr : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (hrr : ∀ p ∈ rr, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachS base (PNR Ld W R) (execAll is s) Q)
    (hn : NoLdrBlock is = true := by decide)
    (hrc : M0Crypto.Sym.readChk Ld rr is = true := by decide +kernel) :
    ReachS base (PNR Ld W R) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
  show BlockOk (fun _ e => ((∀ y, Writes e.accesses y → W e.pc y) ∧ NoLdr e) ∧
    (Ld e.instr = true → ∀ y, Reads e.accesses y → R y)) is s
  rw [blockOk_events_iff]
  intro e he
  refine ⟨⟨fun y hy => ?_, noLdr_of_block hn (traceAll_instr is s e he)⟩, fun hld y hy => ?_⟩
  · obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
    obtain ⟨p, hp, o, ho', rfl⟩ :=
      M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
    rw [hep, hpc, ofNat_add_assoc]
    exact hrg p hp o ho' j hj
  · obtain ⟨p, hp, o, ho', rfl⟩ :=
      M0Crypto.Sym.readChk_sound Ld rr is (M0Crypto.Sym.sound_all hf) s hrc e he hld y hy
    exact hrr p hp o ho'

/-- The one-entry read annotation `[(r, k, n)]`. -/
theorem rr_one {s : State} {r : Reg} {k : Word} {n : Nat}
    (h : ∀ o < n, R (s.regs r + k + BitVec.ofNat 32 o)) :
    ∀ p ∈ [(r, k, n)], ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o) := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

theorem ReachS.bPcNR {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachS base (PNR Ld W R) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    ReachS base (PNR Ld W R) s Q :=
  ReachS.b hb off tgt imm hpc ho hi hsz ht (PNR.nil (by simp [ldrU1]) (by simp [ldrU2])) hq

theorem ReachS.bcondPcNR {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true →
      ReachS base (PNR Ld W R) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachS base (PNR Ld W R) (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachS base (PNR Ld W R) s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht (PNR.nil (by simp [ldrU1]) (by simp [ldrU2])) hT hF

/-- An instruction that writes nothing and is neither a declared load nor an `Ld` instruction. -/
theorem ReachS.stepNWNR {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, ¬ Writes (i.accesses s) y)
    (hq : ReachS base (PNR Ld W R) s1 Q) (hn : NoLdrBlock [i] = true := by decide)
    (hl : Ld i = false := by decide) :
    ReachS base (PNR Ld W R) s Q := by
  have hn' := noLdr_of_block hn (List.mem_singleton_self i)
  exact ReachS.step hb off i hpc ho hi hsz ha hex
    ⟨⟨fun y hy => absurd hy (hw y), hn'⟩, fun h => by
      have h' : Ld i = true := h
      rw [hl] at h'; exact absurd h' (by decide)⟩ hq

end M0Crypto.Release
