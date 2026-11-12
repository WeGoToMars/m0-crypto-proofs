import M0Crypto.Release.ReachSteps
import M0Crypto.Release.SymReach

/-!
`ReachS` with a program-counter-dependent write bound.

`PcWr W` says that every byte an instruction at `pc` writes satisfies `W pc`. A site
obligation that only holds at some instructions (the output-hash stores of the BLAKE2s
compression write the chain window, while the other stores write anywhere in the frame or
the chain window) is then a bound on the writes of a run that is stronger at those pcs.
`ReachS.symBlockW` is `Reach.symBlock` for this predicate: the caller shows each symbolic
write region satisfies `W` at every byte offset of the block.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- Every byte written by an instruction at `pc` satisfies `W pc`. -/
def PcWr (W : Word → Word → Prop) (_ : State) (e : Event) : Prop :=
  ∀ y, Writes e.accesses y → W e.pc y

variable {base : Word} {W : Word → Word → Prop}

theorem ReachS.symBlockW {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, ∀ j < seqSize is,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachS base (PcWr W) (execAll is s) Q) : ReachS base (PcWr W) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) ?_ hq
  show BlockOk (fun _ e => ∀ y, Writes e.accesses y → W e.pc y) is s
  rw [blockOk_events_iff]
  intro e he y hy
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  obtain ⟨p, hp, o, ho', rfl⟩ :=
    M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
  rw [hep, hpc, ofNat_add_assoc]
  exact hrg p hp o ho' j hj

/-- The one-entry write annotation `[(r, k, n)]`. -/
theorem ReachS.regionW_one {s : State} {r : Reg} {k : Word} {n : Nat} {off m : Nat}
    (h : ∀ o < n, ∀ j < m, W (base + BitVec.ofNat 32 (off + j)) (s.regs r + k + BitVec.ofNat 32 o)) :
    ∀ p ∈ [(r, k, n)], ∀ o < p.2.2, ∀ j < m,
      W (base + BitVec.ofNat 32 (off + j)) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o) := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

/-- An instruction that writes nothing needs no bound. -/
theorem ReachS.stepNW {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, ¬ Writes (i.accesses s) y) (hq : ReachS base (PcWr W) s1 Q) :
    ReachS base (PcWr W) s Q :=
  ReachS.step hb off i hpc ho hi hsz ha hex (fun y hy => absurd hy (hw y)) hq

/-- A `PcWr` run writes inside `Wr` when `W pc ⊆ Wr` at every pc. -/
theorem ReachS.pcWr_mono {Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachS base (PcWr W) s Q) (hw : ∀ pc y, W pc y → Wr y) : Reach base Wr s Q :=
  (reach_iff_reachS Wr s Q).mpr
    (h.mono (fun _ e hp y hy => hw _ _ (hp y hy)) (fun _ h => h))

end M0Crypto.Release
