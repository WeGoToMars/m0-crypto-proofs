import M0Crypto.Sym.Known

/-!
# Symbolic executor: memory bridge after a straight-line block

`mem_execAll_normK` relates the memory after a block to the symbolic memory from
`SState.initK k`, under the same hypotheses as `execAll_regs_normK`. It is the memory
analogue of that register bridge. `read32_execAll_normK` then states that a word load
at a symbolic address after the block equals the normalised symbolic load, so stack
words written by the block can be read through `norm` (via `rdW`).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb

/-- Memory after the straight-line block `is`, from a state whose registers in `k` hold
the listed values, is the denotation of the symbolic memory. -/
theorem mem_execAll_normK (is : List Instr) (hf : is.all Instr.falls = true)
    (k : List (Reg × Word)) (s : State) (h : ∀ p ∈ k, s.regs p.1 = p.2) :
    (execAll is s).mem = ((symExec is (SState.initK k)).mem).denote s := by
  have e := symExec_sound is (sound_all hf) s (SState.initK k)
  rw [initK_denote k s h] at e
  rw [← e]
  rfl

/-- A word load at symbolic address `aS` after the block `is` equals the normalised
symbolic load from the symbolic memory of `symExec is (SState.initK k)`. -/
theorem read32_execAll_normK (is : List Instr) (hf : is.all Instr.falls = true)
    (k : List (Reg × Word)) (s : State) (h : ∀ p ∈ k, s.regs p.1 = p.2) (aS : SExpr) :
    read32 (execAll is s).mem (aS.denote s) =
      (norm (.ld32 (symExec is (SState.initK k)).mem aS)).denote s := by
  rw [norm_sound, mem_execAll_normK is hf k s h]
  rfl

end M0Crypto.Sym
