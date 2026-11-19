import M0Crypto.Release.StackEffectSym
import M0Crypto.Release.Ed25519CallProgOp

/-!
# Call programs: the byte effect of a callee

A callee's effect is a property of its trace at every public value `p` (`CalleeS.Eff`): from an
effect state at its entry SP, its trace is `Good` and ends at that SP, given that the window
bytes it reads from its inputs were written before (`Rq`); it adds the bytes of its outputs
(`Wd`). An input or output occupies its kind's size, apart from a SHA-512 context, of which only
the bytes before the block buffer and the pending bytes count. The registers, the stream length
and the input lengths come from `p` by the callee's public-value list.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect

/-- The offset of a SHA-512 context's block buffer. -/
def ctxBuf : Nat := ctxSize - 128

theorem EffT.mono {stk stk' : Nat} {Fp Fp' Rq Rq' Wd Wd' : Word → Prop} {sp : Word} {tr : List Event}
    (h : EffT stk Fp Rq Wd sp tr) (hs : stk ≤ stk') (hF : ∀ y, Fp y → Fp' y) (hR : ∀ y, Rq y → Rq' y)
    (hW : ∀ y, Wd' y → Wd y) : EffT stk' Fp' Rq' Wd' sp tr := fun sp0 n p h1 h2 h3 h4 h5 h6 =>
  let ⟨g, s, u, w⟩ := h sp0 n p h1 (by omega) h3 h4 (fun y hy => h5 y (hF y hy)) fun y hy => h6 y (hR y hy)
  ⟨g, s, u, fun y hy => w y (hW y hy)⟩

/-- The bytes of the raw inputs of `ins`, at registers `f`. -/
def rawSum (f : Reg → Word) : List (Reg × Nat × In) → Nat
  | [] => 0
  | (_, _, .raw l) :: xs => l.val f + rawSum f xs
  | _ :: xs => rawSum f xs

namespace CalleeS
variable (s : CalleeS) (p : Nat → Word)

/-- Register `r` among the public values `p`. -/
def reg (r : Reg) : Word := p (s.pubs.idxOf (.r r))

/-- The stream length among the public values `p`, or `0`. -/
def cnt : Nat := if PubW.n 0 ∈ s.pubs then (p (s.pubs.idxOf (.n 0))).toNat else 0

/-- The bytes of the raw inputs. -/
def rawLen : Nat := rawSum (s.reg p) s.io.ins

/-- The written bytes of an input: a context's bytes before the buffer and its pending bytes. -/
def iniIn : In → Nat
  | .view (.ctx _) => ctxBuf + s.cnt p % 128
  | .view k => k.sz
  | .raw l => l.val (s.reg p)

/-- The written bytes of an output: a context's, with the raw inputs appended to its stream. -/
def iniOut : Kd → Nat
  | .ctx _ => ctxBuf + (s.cnt p + s.rawLen p) % 128
  | k => k.sz

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The bytes a callee accesses outside its stack: the code and its footprints. -/
def Fp (base : Word) : Word → Prop :=
  Has (codeR base :: rgnsC (s.reg p) s.io.rd ++ rgnsC (s.reg p) s.io.wr)

/-- The bytes a callee requires written: the code and the written bytes of its inputs. -/
def Rq (base y : Word) : Prop :=
  Has [codeR base] y ∨ ∃ x ∈ s.io.ins, Region (s.reg p x.1 + BitVec.ofNat 32 x.2.1) (s.iniIn p x.2.2) y

/-- The bytes a callee writes: the written bytes of its outputs. -/
def Wd (y : Word) : Prop :=
  ∃ x ∈ s.io.outs, Region (s.reg p x.1 + BitVec.ofNat 32 x.2.1) (s.iniOut p x.2.2) y

/-- **The effect of a callee's trace** at public values `p`. -/
def Eff (base : Word) : TrP := EffT s.stack (s.Fp p base) (s.Rq p base) (s.Wd p) (s.reg p 13)

end CalleeS

/-- Register `r` plus `off`, over `n` bytes. -/
def rgnE (r : Reg) (off n : Nat) : M0Crypto.Sym.SExpr × Nat := (.add (.reg0 r) (.const (BitVec.ofNat 32 off)), n)

end M0Crypto.Release.Ed25519CallProg
