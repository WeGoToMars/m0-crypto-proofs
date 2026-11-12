import M0Crypto.Release.SymReachW
import M0Crypto.Release.AeadCall

/-!
`Reach`-style combinators for `ReachS base (PcWr W)`.

The BLAKE2s `update` proof is a tree of `Reach.bind`/`Reach.bcond`/`Reach.bl` over the
compress and copy callees. To carry a program-counter-dependent write bound through it, each
combinator takes the argument order of its `Reach` namesake, so porting a module is a rename.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

variable {base : Word} {W : Word → Word → Prop}

theorem PcWr.nil (W : Word → Word → Prop) (s : State) (pc : Word) (i : Instr) :
    PcWr W s ⟨pc, i, []⟩ := fun y hy => absurd hy (writes_nil y)

theorem ReachS.monoQ {P : State → Event → Prop} {s : State} {Q Q' : State → Prop}
    (h : ReachS base P s Q) (hq : ∀ t, Q t → Q' t) : ReachS base P s Q' :=
  h.mono (fun _ _ hp => hp) hq

theorem ReachS.bcondPc {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true →
      ReachS base (PcWr W) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachS base (PcWr W) (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachS base (PcWr W) s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht (PcWr.nil W _ _ _) hT hF

theorem ReachS.blPc {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat) (imm : BitVec 25)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : Aead.blTarget off imm = BitVec.ofNat 32 tgt)
    (hq : ReachS base (PcWr W) ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachS base (PcWr W) s Q :=
  ReachS.bl hb off tgt imm hpc ho hi hsz ht (PcWr.nil W _ _ _) hq

end M0Crypto.Release
