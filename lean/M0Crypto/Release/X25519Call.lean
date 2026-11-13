import M0Crypto.Release.X25519FeMul
import M0Crypto.Release.X25519FeSqr
import M0Crypto.Release.X25519MulcAdd
import M0Crypto.Release.Call

/-!
Calls of the three field routines from `m0c_x25519`.

`RoutineRun` is the shape of the routines' `run` theorems: from a valid entry the routine
reaches its return address with `Post`, executing only its own bytes and writing only its
stack and `dst`. `call_w` steps a `bl` of the entry and runs the callee from the state the
`bl` leaves. The caller supplies the non-trivial `Pre` fields as `CallOk`, phrased on the
state before the `bl`; the continuation receives the state at the instruction after the
`bl` with the callee's `Post`.
-/

namespace M0Crypto.Release.X25519Call
open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region lr_mask lr_odd)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Routines (Call Pre Post feVal mulFrame mulcFrame)
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feMulSize feSqr feSqrSize feMulcAdd feMulcAddSize)

/-- A routine at `off`, `size` bytes, run from a valid entry to its return. -/
def RoutineRun (off size frame : Nat) (useB : Bool) (f : Int → Int → Int) : Prop :=
  ∀ c s, Pre off size frame useB c s →
    ReachW c.base (Region (c.base + BitVec.ofNat 32 off) size)
      (fun y => Region (c.fp frame) frame y ∨ Region c.dst 32 y) s
      fun t => t.pc = c.ret ∧ Post frame f c t

theorem mul_run : RoutineRun feMul feMulSize mulFrame true fun a b => a * b := X25519FeMul.run
theorem sqr_run : RoutineRun feSqr feSqrSize mulFrame false fun a _ => a * a := X25519FeSqr.run
theorem mulcAdd_run : RoutineRun feMulcAdd feMulcAddSize mulcFrame true fun a b => 121666 * a + b :=
  X25519MulcAdd.run

theorem ReachW.bind {base : Word} {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pc Wr s fun t => ReachW base Pc Wr t Q) : ReachW base Pc Wr s Q :=
  ReachS.bind h

/-- The state a `bl` at offset `o` to offset `off` leaves. -/
def blState (base : Word) (s : State) (o off : Nat) : State :=
  (s.setReg 14 ((base + BitVec.ofNat 32 (o + 4)) ||| 1#32)).setReg 15 (base + BitVec.ofNat 32 off)

/-- The callee's view of a call made from `s` by the `bl` at `o`. -/
def callOf (base : Word) (s : State) (o off : Nat) : Call :=
  ⟨base, s.regs 13, s.regs 0, s.regs 1, s.regs 2, s.mem, (blState base s o off).regs⟩

/-- The `Pre` fields of a call that are not fixed by the `bl` itself. -/
structure CallOk (size frame : Nat) (useB : Bool) (base : Word) (s : State) : Prop where
  base4 : base.toNat % 4 = 0
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : frame ≤ (s.regs 13).toNat
  al : (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧ (useB = true → (s.regs 2).toNat % 4 = 0)
  code : Thumb.CodeAt s.mem base B
  codeS : Disj base Artifacts.Release.size (s.regs 13 - BitVec.ofNat 32 frame) frame
  codeD : Disj base Artifacts.Release.size (s.regs 0) 32
  dstS : Disj (s.regs 0) 32 (s.regs 13 - BitVec.ofNat 32 frame) frame
  aS : Disj (s.regs 1) 32 (s.regs 13 - BitVec.ofNat 32 frame) frame
  bS : useB = true → Disj (s.regs 2) 32 (s.regs 13 - BitVec.ofNat 32 frame) frame
  dstA : s.regs 0 = s.regs 1 ∨ Disj (s.regs 0) 32 (s.regs 1) 32
  dstB : useB = true → s.regs 0 = s.regs 2 ∨ Disj (s.regs 0) 32 (s.regs 2) 32

theorem blState_regs (base : Word) (s : State) (o off : Nat) (r : Reg) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    (blState base s o off).regs r = s.regs r := by
  simp [blState, State.setReg, h14, h15]

theorem blState_lr (base : Word) (s : State) (o off : Nat) :
    (blState base s o off).regs 14 = (base + BitVec.ofNat 32 (o + 4)) ||| 1#32 := by
  simp [blState, State.setReg]

theorem blState_pc (base : Word) (s : State) (o off : Nat) :
    (blState base s o off).regs 15 = base + BitVec.ofNat 32 off := by
  simp [blState, State.setReg]

theorem ret_eq (base : Word) (s : State) (o off : Nat) (hb : base.toNat % 4 = 0) (ho : o % 2 = 0) :
    (callOf base s o off).ret = base + BitVec.ofNat 32 (o + 4) := by
  show (blState base s o off).regs 14 &&& ~~~1#32 = _
  rw [blState_lr]
  apply lr_mask
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem pre_of {off size frame : Nat} {useB : Bool} {base : Word} {s : State} {o : Nat}
    (h : CallOk size frame useB base s) (ho : o % 2 = 0)
    (hret : ¬ Region (base + BitVec.ofNat 32 off) size (base + BitVec.ofNat 32 (o + 4))) :
    Pre off size frame useB (callOf base s o off) (blState base s o off) where
  regs := rfl
  mem := rfl
  pc := blState_pc base s o off
  sp := blState_regs base s o off 13 (by decide) (by decide)
  r0 := blState_regs base s o off 0 (by decide) (by decide)
  r1 := blState_regs base s o off 1 (by decide) (by decide)
  r2 := fun _ => blState_regs base s o off 2 (by decide) (by decide)
  thumb := by
    show ((blState base s o off).regs 14).getLsbD 0 = true
    rw [blState_lr]
    exact lr_odd _
  retOut := by rw [ret_eq base s o off h.base4 ho]; exact hret
  base4 := h.base4
  sp4 := h.sp4
  spLo := h.spLo
  al := h.al
  code := h.code
  codeS := h.codeS
  codeD := h.codeD
  dstS := h.dstS
  aS := h.aS
  bS := h.bS
  dstA := h.dstA
  dstB := h.dstB

/-- A `bl` at `o` to a routine at `off` meeting `RoutineRun`, then the continuation. -/
theorem call_w {off size frame : Nat} {useB : Bool} {f : Int → Int → Int}
    (hrun : RoutineRun off size frame useB f)
    {base : Word} {Pc Wr : Word → Prop} {s : State} {Q : State → Prop} {o : Nat} {imm : BitVec 25}
    (hpc : s.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0)
    (hi : instrAt B o = some (.bl imm)) (hsz : o + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 o + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 off)
    (hr : Pc (base + BitVec.ofNat 32 o))
    (hPc : ∀ y, Region (base + BitVec.ofNat 32 off) size y → Pc y)
    (hret : ¬ Region (base + BitVec.ofNat 32 off) size (base + BitVec.ofNat 32 (o + 4)))
    (hok : CallOk size frame useB base s)
    (hW : ∀ y, Region (s.regs 13 - BitVec.ofNat 32 frame) frame y ∨ Region (s.regs 0) 32 y → Wr y)
    (k : ∀ t, t.pc = base + BitVec.ofNat 32 (o + 4) → Post frame f (callOf base s o off) t →
      ReachW base Pc Wr t Q) :
    ReachW base Pc Wr s Q := by
  have hb : base.toNat % 2 = 0 := by have := hok.base4; omega
  refine ReachW.bl hb o off imm hpc ho hi hsz ht hr ?_
  apply ReachW.bind
  have h := (hrun _ _ (pre_of (off := off) hok ho hret)).monoPc hPc
  refine (h.monoW (fun y hy => hW y hy)).mono (fun _ _ h => h) fun t ⟨tp, tq⟩ => ?_
  rw [ret_eq base s o off hok.base4 ho] at tp
  exact k t tp tq

end M0Crypto.Release.X25519Call
