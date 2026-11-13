import M0Crypto.Release.ConstantTime.PushSound
import M0Crypto.Release.ConstantTime.PopSound

/-! Alignment of checked instruction positions and return addresses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb

/-- The fixed instruction sizes preserve alignment through a block. -/
theorem blockPoint_aligned {env : Env} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    (hp : BlockPoint env b off st code) (hb : b.off % 2 = 0) : off % 2 = 0 := by
  induction hp with
  | entry => exact hb
  | @next off st i is out next hp hx hs ih =>
    have hi := instr_size_even i
    omega

theorem certPoint_pc_even {env : Env} {cert : Cert} {b : Blk} {off : Nat}
    {st : AbsState} {code : List Instr} (base : Word)
    (hb : base.toNat % 2 = 0) (hc : certAligned cert = true)
    (hm : b ∈ cert) (hp : BlockPoint env b off st code) :
    (base + BitVec.ofNat 32 off).getLsbD 0 = false :=
  pc_even base off hb (blockPoint_aligned hp (certAligned_head hc hm))

/-- Unconditional transfers and returns appear only as the last instruction
in a block. A conditional branch can occur earlier when its only checked
successor is the next instruction. -/
def isTerminalTransfer : Instr → Bool
  | .b _ | .bl _ | .pop _ true => true
  | _ => false

def controlEndsBlock : List Instr → Bool
  | [] => true
  | i :: is => (!isTerminalTransfer i || is.isEmpty) && controlEndsBlock is

/-- Setting and then clearing the Thumb bit recovers an aligned address. -/
theorem clear_thumb_bit (x : Word) (h : x.getLsbD 0 = false) :
    (x ||| 1#32) &&& ~~~1#32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_one]
  by_cases hz : i = 0
  · subst i
    have h' : x[0] = false := by simpa [BitVec.getLsbD_eq_getElem] using h
    simp [h']
  · simp [hz, hi]

/-- A block found at a top-level offset is an aligned block head. -/
theorem findBlk_aligned {cert : Cert} {r : Nat} {blk : Blk}
    (ha : certAligned cert = true) (hfind : findBlk cert r none = some blk) : r % 2 = 0 := by
  have hs := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  simpa [hs.1] using certAligned_head ha (List.mem_of_find?_eq_some hfind)

/-- Internal returns satisfy the paired-step relation using only the artifact
base alignment and checked certificate alignment: every return offset the analysis
sends to is a block head, and block heads are aligned. -/
theorem certPoint_pop_return_aligned_paired {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off c : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State} (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.pop l true])
    (hctx : b.ctx = some c) (h : LowEq p bytes off st s₁ s₂) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ :=
  certPoint_pop_return_paired l hc hi hm hp hctx h
    (fun r _ hfind => clear_thumb_bit _ (pc_even p.base r hbase (findBlk_aligned ha hfind)))
    (certPoint_pc_even p.base hbase ha hm hp)

/-- A non-final instruction in a validated block has exactly one successor:
the next instruction in the same context. -/
theorem certPoint_nonfinal_successor {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {i j : Instr} {is : List Instr} {out : Out}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: j :: is))
    (hx : xfer env off b.ctx i st = .ok out) :
    ∃ next, out.succs = [(.pt (off + i.size) b.ctx, next)] := by
  obtain ⟨succ, sites, hr, _⟩ := blkFailure_run (certOk_block hc hm)
  obtain ⟨_, hs⟩ := blockPoint_run hp (by simp) hr
  cases out with
  | mk outputs kinds =>
    cases outputs with
    | nil => simp [runBlock, hx] at hs
    | cons first rest =>
      cases rest with
      | cons second tail => simp [runBlock, hx] at hs
      | nil =>
        rcases first with ⟨target, next⟩
        cases target with
        | exit => simp [runBlock, hx] at hs
        | pt nextOff nextCtx =>
          simp only [runBlock, hx] at hs
          split at hs
          · rename_i h
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            exact ⟨next, by simp [h.1, h.2]⟩
          · contradiction

/-- A conditional branch inside a block advances to its checked fall-through
position, including when the analyzer has pruned the other edge. -/
theorem certPoint_bcond_nonfinal_paired {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {j : Instr} {is : List Instr} {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State}
    (cond : BitVec 4) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.bcond cond imm :: j :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  obtain ⟨next, hsingle⟩ := certPoint_nonfinal_successor hc hm hp hx
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hsucc : ∀ target nextSt, (.pt target b.ctx, nextSt) ∈ out.succs → nextSt.indicesOk := by
    intro target nextSt hs
    exact certPoint_successor_indices hi hm hp hx hs
  obtain ⟨target, nextSt, t₁, t₂, event, hs₁, hs₂, hmem, hnext⟩ :=
    bcond_checked_step cond imm hx hidx hrel hdeclass hsucc heven hdecode hlen
  rw [hsingle] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq, Tgt.pt.injEq] at hmem
  obtain ⟨⟨htarget, _⟩, hstate⟩ := hmem
  subst target
  subst nextSt
  exact certAt_paired_step hc hi hm (BlockPoint.next hp hx hsingle) hnext hs₁ hs₂

/-- A conditional branch advances the paired execution whether it ends its
block or is followed by an analyzer-proved fall-through. -/
theorem certPoint_bcond_aligned_paired {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {is : List Instr} {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State}
    (cond : BitVec 4) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.bcond cond imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  have heven := certPoint_pc_even p.base hbase ha hm hp
  cases is with
  | nil => exact certPoint_bcond_paired cond imm hc hi hm hp hrel hdeclass heven
  | cons j js => exact certPoint_bcond_nonfinal_paired cond imm hc hi hm hp hrel hdeclass heven

end M0Crypto.Release.ConstantTime
