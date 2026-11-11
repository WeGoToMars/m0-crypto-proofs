import M0Crypto.Release.ConstantTime.BlockSound

/-! Consequences of the index diagnostic at reachable block positions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

theorem successorsIndexFailure_sound {b : Blk} {off : Nat} {succ : List (Tgt × AbsState)}
    (h : successorsIndexFailure b off succ = none) {target : Tgt} {st : AbsState}
    (hm : (target, st) ∈ succ) : st.indicesOk := by
  induction succ with
  | nil => simp at hm
  | cons x xs ih =>
    rcases x with ⟨t, s⟩
    simp only [List.mem_cons] at hm
    cases hi : stateIndexIssue b.off b.ctx
        (match t with | .pt nextOff _ => nextOff | .exit => off)
        (match t with | .pt _ nextCtx => nextCtx | .exit => b.ctx) s with
    | some issue =>
      cases t <;> simp [successorsIndexFailure, hi] at h
    | none =>
      rcases hm with heq | hm
      · cases heq
        have hn : st.indicesFailure = none := by
          simpa [stateIndexIssue, Option.map_eq_none_iff] using hi
        exact (AbsState.indicesCheck_eq_true_iff st).mp ((AbsState.indicesFailure_eq_none st).mp hn)
      · apply ih _ hm
        cases t <;> simpa [successorsIndexFailure, hi] using h

theorem blockPoint_indicesWalk {env : Env} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    (hp : BlockPoint env b off st code) (h : blockIndicesFailure env b = none) :
    blockIndicesFailure.walk env b off st code = none := by
  induction hp with
  | entry => exact h
  | @next off st i is out next hp hx hs ih =>
    simp only [blockIndicesFailure.walk] at ih
    cases he : stateIndexIssue b.off b.ctx off b.ctx st with
    | some e => simp [he] at ih
    | none =>
      simp only [he, hx] at ih
      cases hf : successorsIndexFailure b off out.succs with
      | some e => simp [hf] at ih
      | none =>
        rw [hs] at hf
        simpa [hs, hf] using ih

/-- Validating a nonempty suffix entails successful analysis of its first instruction. -/
theorem certPoint_xfer {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) :
    ∃ out, xfer env off b.ctx i st = .ok out := by
  obtain ⟨succ, sites, hr, _⟩ := blkFailure_run (certOk_block hc hm)
  obtain ⟨_, hs⟩ := blockPoint_run hp (by simp) hr
  cases hx : xfer env off b.ctx i st with
  | ok out => exact ⟨out, rfl⟩
  | error e =>
    cases is <;> simp [runBlock, hx] at hs

theorem certPoint_state_indices {env : Env} {cert : Cert} {b : Blk}
    {off : Nat} {st : AbsState} {code : List Instr}
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st code) : st.indicesOk := by
  have hb := (List.findSome?_eq_none_iff.mp hi) b hm
  have hw := blockPoint_indicesWalk hp hb
  have hs : stateIndexIssue b.off b.ctx off b.ctx st = none := by
    cases code with
    | nil => simpa [blockIndicesFailure.walk] using hw
    | cons i is =>
      simp only [blockIndicesFailure.walk] at hw
      cases he : stateIndexIssue b.off b.ctx off b.ctx st with
      | none => rfl
      | some e => simp [he] at hw
  have hn : st.indicesFailure = none := by
    simpa [stateIndexIssue, Option.map_eq_none_iff] using hs
  exact (AbsState.indicesCheck_eq_true_iff st).mp ((AbsState.indicesFailure_eq_none st).mp hn)

theorem certPoint_successor_indices {env : Env} {cert : Cert} {b : Blk}
    {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {out : Out}
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (hx : xfer env off b.ctx i st = .ok out)
    {target : Tgt} {nextSt : AbsState} (hs : (target, nextSt) ∈ out.succs) : nextSt.indicesOk := by
  have hb := (List.findSome?_eq_none_iff.mp hi) b hm
  have hw := blockPoint_indicesWalk hp hb
  simp only [blockIndicesFailure.walk] at hw
  cases he : stateIndexIssue b.off b.ctx off b.ctx st with
  | some e => simp [he] at hw
  | none =>
    simp only [he, hx] at hw
    cases hf : successorsIndexFailure b off out.succs with
    | some e => simp [hf] at hw
    | none => exact successorsIndexFailure_sound hf hs

/-- At the end of a validated block, its unique fall-through successor is a
checked block head that subsumes the outgoing relation. -/
theorem certPoint_fallthrough_head {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st code) (hnil : code = []) (hrel : LowEq p bytes off st s₁ s₂) :
    ∃ nextBlock, findBlk cert off b.ctx = some nextBlock ∧ nextBlock ∈ cert ∧
      LowEq p bytes off nextBlock.st s₁ s₂ := by
  cases hp with
  | entry =>
    obtain ⟨_, _, hr, _⟩ := blkFailure_run (certOk_block hc hm)
    rw [hnil] at hr
    simp [runBlock] at hr
  | next hp hx hs =>
    subst code
    have hf := certPoint_final_successors hc hm hp hx
    rw [hs] at hf
    exact checked_successor_relation hf (by simp) hi hrel

end M0Crypto.Release.ConstantTime
