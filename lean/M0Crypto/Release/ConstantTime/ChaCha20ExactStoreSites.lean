import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ConstantTime.ChaCha20OutputAccess
import M0Crypto.Release.AeadCode

/-! Instruction-exact output store classification for checked certificates. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout
open M0Crypto.Release.Aead

def outputStoreOffset (off : Nat) : Bool :=
  (List.range 16).any (fun i =>
    decide (off = achOff + achSize * i + seqSize (ach i).dropLast)) ||
  decide (off = blOff + seqSize (bl.take 3))

set_option maxRecDepth 100000 in
theorem outputStoreOffset_pc (base : Word) (off : Nat) (h : outputStoreOffset off = true) :
    OutputStorePC base (base + BitVec.ofNat 32 off) := by
  simp only [outputStoreOffset, Bool.or_eq_true, List.any_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  rcases h with ⟨i, hi, rfl⟩ | rfl
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr rfl

def walkExactOutputSites (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    (!untrackedStore st i || (ctx == some decAcceptAt && outputStoreOffset off)) &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out => match out.succs with
      | [(_, next)] => walkExactOutputSites env ctx (off + i.size) next is
      | _ => walkExactOutputSites env ctx (off + i.size) st is

end M0Crypto.Release.ConstantTime
