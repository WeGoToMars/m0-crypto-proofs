import M0Crypto.Release.ConstantTime.BranchConditional
import M0Crypto.Release.ConstantTime.IndexReach

/-! Conditional branches at validated certificate block positions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- A final conditional branch in a validated block executes with matching
observations and reaches a checked successor block. -/
theorem certPoint_bcond_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (cond : BitVec 4) (imm : BitVec 8) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st [.bcond cond imm])
    (hrel : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    ∃ target t₁ t₂ event nextBlock,
      step s₁ = .ok (t₁, event) ∧ step s₂ = .ok (t₂, event) ∧
      findBlk cert target b.ctx = some nextBlock ∧ nextBlock ∈ cert ∧
      LowEq p bytes target nextBlock.st t₁ t₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hf := certPoint_final_successors hc hm hp hx
  have hidx := certPoint_state_indices hi hm hp
  have hsucc : ∀ target nextSt, (.pt target b.ctx, nextSt) ∈ out.succs → nextSt.indicesOk := by
    intro target nextSt hs
    exact certPoint_successor_indices hi hm hp hx hs
  obtain ⟨target, nextSt, t₁, t₂, event, hs₁, hs₂, htarget, hnext⟩ :=
    bcond_checked_step cond imm hx hidx hrel hdeclass hsucc heven hdecode hlen
  obtain ⟨nextBlock, hfind, hmem, hsub⟩ := checked_successor_relation hf htarget hi hnext
  exact ⟨target, t₁, t₂, event, nextBlock, hs₁, hs₂, hfind, hmem, hsub⟩

end M0Crypto.Release.ConstantTime
