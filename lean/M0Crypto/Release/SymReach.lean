import M0Crypto.Release.Reach
import M0Crypto.Sym.Block

/-!
`Reach.symBlock`: `Reach.block` with its two concrete-state side conditions discharged
by the symbolic checks of `M0Crypto.Sym.Block` (approach C, H7).

The caller supplies the base-register alignments `al` and the write regions `rg`, and
shows that the regions lie in `Wr` on the segment's entry state. The checks
`alignChk al is` and `writeChk rg is` are decided on the symbolic trace, so they hold
for every concrete state that satisfies `hal` and `hrg`.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

variable {base : Word} {Wr : Word → Prop}

theorem Reach.symBlock {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, Wr (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : Reach base Wr (execAll is s) Q) : Reach base Wr s Q := by
  have hwt : WritesTo Wr (traceAll is s) := by
    intro e he y hy
    obtain ⟨p, hp, o, ho', rfl⟩ :=
      M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
    exact hrg p hp o ho'
  exact Reach.block hb is off hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) hwt hq

/-- The one-entry alignment annotation `[(r, a)]`: `r` is a multiple of `a`. -/
theorem Reach.alOne {s : State} {r : Reg} {a : Nat} (h : (s.regs r).toNat % a = 0) :
    ∀ p ∈ [(r, a)], (s.regs p.1).toNat % p.2 = 0 := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

/-- The one-entry write annotation `[(r, k, n)]`: `n` bytes from `regs r + k` are in `Wr`. -/
theorem Reach.rgOne {s : State} {r : Reg} {k : Word} {n : Nat}
    (h : ∀ o < n, Wr (s.regs r + k + BitVec.ofNat 32 o)) :
    ∀ p ∈ [(r, k, n)], ∀ o < p.2.2, Wr (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o) := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

/-- `ReachRW.symBlock_rw`: `ReachRW.block_rw` with write side-condition discharged by the
symbolic checks of `M0Crypto.Sym.Block`, leaving read bounds to be discharged directly. -/
theorem ReachRW.symBlock_rw {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (al : List (Reg × Nat)) (rg : List (Reg × Word × Nat))
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hr : ReadsFrom Rd (traceAll is s))
    (hrg : ∀ p ∈ rg, ∀ o < p.2.2, Wr (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o))
    (ha : M0Crypto.Sym.alignChk al is = true)
    (hwc : M0Crypto.Sym.writeChk rg is = true)
    (hq : ReachRW base Rd Wr (execAll is s) Q) : ReachRW base Rd Wr s Q := by
  have hwt : WritesTo Wr (traceAll is s) := by
    intro e he y hy
    obtain ⟨p, hp, o, ho', rfl⟩ :=
      M0Crypto.Sym.writeChk_sound rg is (M0Crypto.Sym.sound_all hf) s hwc e he y hy
    exact hrg p hp o ho'
  exact ReachRW.block_rw hb is off hpc ho hseq hf
    (M0Crypto.Sym.alignChk_sound al is (M0Crypto.Sym.sound_all hf) s hal ha) hr hwt hq

end M0Crypto.Release
