import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.StateSound
import M0Crypto.Release.ConstantTime.BranchDirect

/-! Relating checked blocks to instructions in the artifact. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- Certificate validity entails validation of every listed block. -/
theorem certOk_block {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk}
    (h : certOk env bytes entry init cert = true) (hm : b ∈ cert) :
    blkFailure env bytes cert b = none := by
  have hf := (certOk_iff env bytes entry init cert).mp h
  unfold certFailure at hf
  split at hf
  · contradiction
  · split at hf
    · contradiction
    · exact (List.findSome?_eq_none_iff.mp hf) b hm

/-- The index certificate checks the records at each block head. -/
theorem certIndices_blockHead {env : Env} {cert : Cert} {b : Blk}
    (h : certIndicesFailure cert env = none) (hm : b ∈ cert) : b.st.indicesOk := by
  have hb : blockIndicesFailure env b = none := (List.findSome?_eq_none_iff.mp h) b hm
  have hi : stateIndexIssue b.off b.ctx b.off b.ctx b.st = none := by
    cases hc : b.code with
    | nil => simpa [blockIndicesFailure, blockIndicesFailure.walk, hc] using hb
    | cons i is =>
      simp only [blockIndicesFailure, hc, blockIndicesFailure.walk] at hb
      cases hi : stateIndexIssue b.off b.ctx b.off b.ctx b.st with
      | none => rfl
      | some e => simp [hi] at hb
  have hn : b.st.indicesFailure = none := by
    simpa [stateIndexIssue, Option.map_eq_none_iff] using hi
  exact (AbsState.indicesCheck_eq_true_iff b.st).mp ((AbsState.indicesFailure_eq_none b.st).mp hn)

/-- Successful block validation checks the encoded instruction sequence. -/
theorem blkFailure_seqAt {env : Env} {bytes : List (BitVec 8)} {cert : Cert} {b : Blk}
    (h : blkFailure env bytes cert b = none) : seqAt bytes b.off b.code = true := by
  unfold blkFailure at h
  split at h
  · contradiction
  · rename_i hscan
    rw [seqAt_eq_scan]
    simpa using hscan

/-- Successful block validation supplies successful abstract execution and
checked final successors. -/
theorem blkFailure_run {env : Env} {bytes : List (BitVec 8)} {cert : Cert} {b : Blk}
    (h : blkFailure env bytes cert b = none) :
    ∃ succ sites, runBlock env b.ctx b.off b.st b.code = .ok (succ, sites) ∧
      succFailure cert succ = none := by
  unfold blkFailure at h
  split at h
  · contradiction
  · cases hr : runBlock env b.ctx b.off b.st b.code with
    | error e => simp [hr] at h
    | ok pair =>
      obtain ⟨succ, sites⟩ := pair
      refine ⟨succ, sites, rfl, ?_⟩
      simpa [hr] using h

/-- Advancing past a checked fall-through instruction preserves successful
abstract execution and its final successor list. -/
theorem runBlock_tail {env : Env} {ctx : Option Nat} {off : Nat}
    {st next : AbsState} {i : Instr} {is : List Instr} {out : Out} {succ : List (Tgt × AbsState)}
    {sites : List Site} (hne : is ≠ [])
    (hx : xfer env off ctx i st = .ok out)
    (hs : out.succs = [(.pt (off + i.size) ctx, next)])
    (hr : runBlock env ctx off st (i :: is) = .ok (succ, sites)) :
    ∃ tailSites, runBlock env ctx (off + i.size) next is = .ok (succ, tailSites) := by
  cases is with
  | nil => contradiction
  | cons j js =>
    cases out with
    | mk outputs kinds =>
      simp only at hs
      subst outputs
      simp only [runBlock, hx, beq_self_eq_true, Bool.and_self, ↓reduceIte] at hr
      cases ht : runBlock env ctx (off + i.size) next (j :: js) with
      | error err => simp [ht] at hr
      | ok pair =>
        rcases pair with ⟨tailSucc, tailSites⟩
        simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, _⟩ := hr
        exact ⟨tailSites, rfl⟩

/-- The suffix at a fall-through point retains the initial block's checked
final successors. -/
theorem blockPoint_run {env : Env} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Instr} {succ : List (Tgt × AbsState)} {sites : List Site}
    (hp : BlockPoint env b off st code) (hne : code ≠ [])
    (hr : runBlock env b.ctx b.off b.st b.code = .ok (succ, sites)) :
    ∃ suffixSites, runBlock env b.ctx off st code = .ok (succ, suffixSites) := by
  induction hp with
  | entry => exact ⟨sites, hr⟩
  | @next off st i is out next hp hx hs ih =>
    have hprev : i :: is ≠ [] := by simp
    obtain ⟨priorSites, hprior⟩ := ih hprev
    exact runBlock_tail hne hx hs hprior

/-- Each checked non-exit successor resolves to a certificate block whose
head state subsumes the outgoing state. -/
theorem succFailure_target {cert : Cert} {succ : List (Tgt × AbsState)}
    {off : Nat} {ctx : Option Nat} {st : AbsState}
    (h : succFailure cert succ = none) (hm : (.pt off ctx, st) ∈ succ) :
    ∃ b, findBlk cert off ctx = some b ∧ b ∈ cert ∧ st.le b.st = true := by
  induction succ with
  | nil => simp at hm
  | cons a rest ih =>
    rcases a with ⟨target, state⟩
    simp only [List.mem_cons] at hm
    cases target with
    | exit =>
      simp only [succFailure] at h
      rcases hm with bad | hm
      · cases bad
      · exact ih h hm
    | pt o c =>
      simp only [succFailure] at h
      cases hb : findBlk cert o c with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h
        split at h
        · rename_i hle
          rcases hm with heq | hm
          · cases heq
            refine ⟨b, hb, ?_, hle⟩
            exact List.mem_of_find?_eq_some hb
          · exact ih h hm
        · contradiction

/-- A validated successor enters a certificate block and preserves the concrete
relation when the block's checked abstract state subsumes the outgoing state. -/
theorem checked_successor_relation {cert : Cert} {env : Env} {succ : List (Tgt × AbsState)}
    {p : Params} {bytes : List (BitVec 8)} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State}
    (hf : succFailure cert succ = none) (hm : (.pt off ctx, st) ∈ succ)
    (hindices : certIndicesFailure cert env = none)
    (hrel : LowEq p bytes off st s₁ s₂) :
    ∃ b, findBlk cert off ctx = some b ∧ b ∈ cert ∧ LowEq p bytes off b.st s₁ s₂ := by
  obtain ⟨b, hfind, hmem, hle⟩ := succFailure_target hf hm
  exact ⟨b, hfind, hmem, AbsState.le_sound hle (certIndices_blockHead hindices hmem) hrel⟩

/-- The final instruction at any reached block position has its outgoing
successors checked by the certificate. -/
theorem certPoint_final_successors {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {out : Out}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st [i]) (hx : xfer env off b.ctx i st = .ok out) :
    succFailure cert out.succs = none := by
  obtain ⟨succ, sites, hr, hf⟩ := blkFailure_run (certOk_block hc hm)
  obtain ⟨suffixSites, hs⟩ := blockPoint_run hp (by simp) hr
  simp only [runBlock, hx, Except.ok.injEq, Prod.mk.injEq] at hs
  rw [← hs.1] at hf
  exact hf

/-- Any fall-through position within a byte-checked block has a checked suffix. -/
theorem blockPoint_seqAt {env : Env} {b : Blk} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {code : List Instr}
    (hseq : seqAt bytes b.off b.code = true) (hp : BlockPoint env b off st code) :
    seqAt bytes off code = true := by
  induction hp with
  | entry => exact hseq
  | next _ _ _ ih =>
    simp only [seqAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ih
    exact ih.2

/-- At each nonempty checked position, decoding finds its instruction and the
instruction fits in the artifact. -/
theorem blockPoint_instrAt {env : Env} {b : Blk} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hseq : seqAt bytes b.off b.code = true) (hp : BlockPoint env b off st (i :: is)) :
    instrAt bytes off = some i ∧ off + i.size ≤ bytes.length := by
  have h := blockPoint_seqAt hseq hp
  simp only [seqAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- A valid certificate supplies decoding and artifact bounds at any
fall-through instruction of one of its blocks. -/
theorem certPoint_instrAt {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (h : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) :
    instrAt bytes off = some i ∧ off + i.size ≤ bytes.length :=
  blockPoint_instrAt (blkFailure_seqAt (certOk_block h hm)) hp

/-- A final unconditional branch in a validated block executes equally in both
runs and arrives in the related head state of its checked successor block. -/
theorem certPoint_branch_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params} {out : Out}
    (imm : BitVec 11) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st [.b imm])
    (hx : xfer env off b.ctx (.b imm) st = .ok out)
    (hidx : st.indicesOk) (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    ∃ target t₁ t₂ event nextBlock,
      step s₁ = .ok (t₁, event) ∧ step s₂ = .ok (t₂, event) ∧
      findBlk cert target b.ctx = some nextBlock ∧ nextBlock ∈ cert ∧
      LowEq p bytes target nextBlock.st t₁ t₂ := by
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hf := certPoint_final_successors hc hm hp hx
  obtain ⟨target, t₁, t₂, event, hs₁, hs₂, _, htarget, hnext⟩ :=
    branch_checked_step imm hx hidx hrel heven hdecode hlen
  obtain ⟨nextBlock, hfind, hmem, hsub⟩ := checked_successor_relation hf htarget hi hnext
  exact ⟨target, t₁, t₂, event, nextBlock, hs₁, hs₂, hfind, hmem, hsub⟩

end M0Crypto.Release.ConstantTime
