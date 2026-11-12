import M0Crypto.Release.ReachPcN
import M0Crypto.Release.SymReach

/-!
`ReachN base Wr`: a `Reach` that also records, per event, that the instruction is neither of the
two declared public loads (`PN`). It has the same combinator names and argument order as `Reach`,
so a `Reach`-based proof of a callee ports by renaming; the write bound is pc-independent.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- `Reach` with the public loads excluded. -/
abbrev ReachN (base : Word) (Wr : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachS base (PN fun _ => Wr) s Q

variable {base : Word} {Wr : Word → Prop}

theorem ReachN.done {s : State} {Q : State → Prop} (h : Q s) : ReachN base Wr s Q := ReachS.done h

theorem ReachN.mono {s : State} {Q Q' : State → Prop} (h : ReachN base Wr s Q)
    (hq : ∀ t, Q t → Q' t) : ReachN base Wr s Q' := ReachS.mono h (fun _ _ p => p) hq

theorem ReachN.monoW {s : State} {Q : State → Prop} {Wr' : Word → Prop} (h : ReachN base Wr s Q)
    (hw : ∀ y, Wr y → Wr' y) : ReachN base Wr' s Q :=
  ReachS.mono h (fun _ _ p => ⟨fun y hy => hw _ (p.1 y hy), p.2⟩) (fun _ h => h)

theorem ReachN.bind {s : State} {Q : State → Prop}
    (h : ReachN base Wr s fun s1 => ReachN base Wr s1 Q) : ReachN base Wr s Q := ReachS.bind h

/-- The write bound of a `ReachN` run is the pc-independent `Reach` bound. -/
theorem ReachN.toReach {s : State} {Q : State → Prop} (h : ReachN base Wr s Q) : Reach base Wr s Q :=
  (reach_iff_reachS Wr s Q).mpr (ReachS.mono h (fun _ _ p => p.1) (fun _ h => h))

theorem ReachN.symBlock {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, Wr (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachN base Wr (execAll is s) Q)
    (hn : NoLdrBlock is = true := by decide) : ReachN base Wr s Q :=
  ReachS.symBlockWN hb al rg is off hpc ho hseq hf hal (fun p hp o ho' _ _ => hrg p hp o ho') ha hwc hq hn

theorem ReachN.step {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y) (hq : ReachN base Wr s1 Q)
    (hn : NoLdrBlock [i] = true := by decide) : ReachN base Wr s Q :=
  ReachS.step hb off i hpc ho hi hsz ha hex ⟨hw, noLdr_of_block hn (List.mem_singleton_self i)⟩ hq

theorem ReachN.bcond {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → ReachN base Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → ReachN base Wr (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachN base Wr s Q :=
  ReachS.bcondPcN hb off tgt cond imm hpc ho hi hsz ht hT hF

theorem ReachN.b {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachN base Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachN base Wr s Q :=
  ReachS.bPcN hb off tgt imm hpc ho hi hsz ht hq

end M0Crypto.Release
