import M0Crypto.Release.Blake2sCopyCode
import M0Crypto.Release.ReachPcR
import M0Crypto.Release.Blake2sLd

/-!
`ReachNR base Wr Rd`: the pc-independent write bound `Wr` of `ReachN`, and the read bound `Rd` on
the loads of `m0c_blake2s_copy` through the source pointer (`kLd`). The combinators keep the
names and argument order of `ReachN`, with the read annotation of a block (`symBlock`) added.
-/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release

/-- The instructions at the copy's load sites: every load through the source pointer. -/
def kLd (i : Instr) : Bool := M0Crypto.Release.Blake2sLd.ldAll i

abbrev ReachNR (base : Word) (Wr Rd : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachS base (PNR kLd (fun _ => Wr) Rd) s Q

variable {base : Word} {Wr Rd : Word → Prop}

theorem ReachNR.done {s : State} {Q : State → Prop} (h : Q s) : ReachNR base Wr Rd s Q :=
  ReachS.done h

theorem ReachNR.mono {s : State} {Q Q' : State → Prop} (h : ReachNR base Wr Rd s Q)
    (hq : ∀ t, Q t → Q' t) : ReachNR base Wr Rd s Q' := ReachS.mono h (fun _ _ p => p) hq

theorem ReachNR.bind {s : State} {Q : State → Prop}
    (h : ReachNR base Wr Rd s fun s1 => ReachNR base Wr Rd s1 Q) : ReachNR base Wr Rd s Q :=
  ReachS.bind h

theorem ReachNR.symBlock {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg rr : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, Wr (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (hrr : ∀ p ∈ rr, ∀ o < p.2.2, Rd (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachNR base Wr Rd (execAll is s) Q)
    (hn : NoLdrBlock is = true := by decide)
    (hrc : M0Crypto.Sym.readChk kLd rr is = true := by decide +kernel) : ReachNR base Wr Rd s Q :=
  ReachS.symBlockWNR hb al rg rr is off hpc ho hseq hf hal (fun p hp o ho' _ _ => hrg p hp o ho')
    hrr ha hwc hq hn hrc

theorem ReachNR.step {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y) (hq : ReachNR base Wr Rd s1 Q)
    (hn : NoLdrBlock [i] = true := by decide) (hl : kLd i = false := by decide) :
    ReachNR base Wr Rd s Q :=
  ReachS.step hb off i hpc ho hi hsz ha hex
    ⟨⟨hw, noLdr_of_block hn (List.mem_singleton_self i)⟩, fun h => by
      have h' : kLd i = true := h
      rw [hl] at h'; exact absurd h' (by decide)⟩ hq

theorem ReachNR.bcond {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true →
      ReachNR base Wr Rd (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachNR base Wr Rd (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachNR base Wr Rd s Q :=
  ReachS.bcondPcNR hb off tgt cond imm hpc ho hi hsz ht hT hF

theorem ReachNR.b {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachNR base Wr Rd (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    ReachNR base Wr Rd s Q :=
  ReachS.bPcNR hb off tgt imm hpc ho hi hsz ht hq

end M0Crypto.Release.Blake2sCopy
