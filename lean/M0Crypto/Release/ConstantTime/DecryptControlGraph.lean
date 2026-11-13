import M0Crypto.Release.ConstantTime.DecryptPrefix
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-! Finite certificate control-flow graph checks. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Release.Aead

abbrev GraphNode := Nat × Option Nat

/-- The final targets of a checked block, omitting the exit target. -/
def graphOut (env : Env) (b : Blk) : List GraphNode :=
  match runBlock env b.ctx b.off b.st b.code with
  | .error _ => []
  | .ok (succ, _) => succ.filterMap fun x => match x.1 with
    | .pt off ctx => some (off, ctx)
    | .exit => none

def graphBlock (cert : Cert) (node : GraphNode) : List Blk :=
  cert.filter fun b => b.off == node.1 && b.ctx == node.2

/-- Compute a finite over-approximation of graph reachability. The separate
closure check ensures running out of fuel cannot establish a false result. -/
def graphWalk (env : Env) (cert : Cert) : Nat → List GraphNode → List GraphNode → List GraphNode
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | n + 1, seen, x :: xs =>
    if seen.contains x then graphWalk env cert n seen xs
    else graphWalk env cert n (x :: seen) (xs ++ (graphBlock cert x).flatMap (graphOut env))

def blocksContaining (cert : Cert) (off : Nat) : List Blk :=
  cert.filter fun b => b.off ≤ off && off < b.off + seqSize b.code

/-- A checked block position retains the total byte extent of the block. -/
theorem blockPoint_extent {env : Env} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    (hp : BlockPoint env b off st code) :
    b.off ≤ off ∧ off + seqSize code = b.off + seqSize b.code := by
  induction hp with
  | entry => exact ⟨Nat.le_refl _, rfl⟩
  | @next off st i is out next hp hx hs ih =>
    simp only [seqSize, List.map_cons, List.sum_cons] at ih ⊢
    constructor <;> omega

/-- Every nonempty checked position lies in its block's byte extent. -/
theorem blockPoint_in_blocksContaining {env : Env} {cert : Cert} {b : Blk}
    {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is)) :
    b ∈ blocksContaining cert off := by
  have ⟨hl, he⟩ := blockPoint_extent hp
  have hp' : 0 < seqSize (i :: is) := by
    simp [seqSize]
    have hs : 0 < i.size := by cases i <;> simp [Instr.size]
    omega
  simp only [blocksContaining, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, hl, by omega⟩

/-- A target of the last instruction at a validated block position is an
edge in the corresponding certificate control-flow graph. -/
theorem certPoint_final_graph_edge {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {i : Instr} {out : Out} {target : Nat} {ctx : Option Nat} {next : AbsState}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st [i]) (hx : xfer env off b.ctx i st = .ok out)
    (ht : (.pt target ctx, next) ∈ out.succs) :
    (target, ctx) ∈ graphOut env b := by
  obtain ⟨succ, sites, hr, _⟩ := blkFailure_run (certOk_block hc hm)
  obtain ⟨_, htail⟩ := blockPoint_run hp (by simp) hr
  simp only [runBlock, hx, Except.ok.injEq, Prod.mk.injEq] at htail
  have hmem : (.pt target ctx, next) ∈ succ := by rw [← htail.1]; exact ht
  simp only [graphOut, hr]
  simp only [List.mem_filterMap]
  refine ⟨(.pt target ctx, next), hmem, ?_⟩
  rfl

def decryptBranchBlocks : List Blk := blocksContaining decryptCert decRejectBrAt

def decryptAfterBranch : List GraphNode := decryptBranchBlocks.flatMap (graphOut decryptEnv)
def decryptAfterReach : List GraphNode :=
  graphWalk decryptEnv decryptCert (4 * (decryptCert.length + 1) ^ 2) [] decryptAfterBranch

/-- Check the computed set contains the initial nodes, is successor-closed,
and excludes every block containing the authentication branch. -/
def branchGraphCheck : Bool :=
  !decryptBranchBlocks.isEmpty &&
  decryptAfterBranch.all decryptAfterReach.contains &&
  decryptAfterReach.all (fun node =>
    ((graphBlock decryptCert node).flatMap (graphOut decryptEnv)).all decryptAfterReach.contains) &&
  decryptBranchBlocks.all (fun b => !(decryptAfterReach.contains (b.off, b.ctx)))

theorem branchGraphCheck_ok : branchGraphCheck = true := by decide +kernel

/-- The designated branch is the last instruction of any containing block. -/
def branchAtBlockEnd : Bool := decryptBranchBlocks.all fun b =>
  decide (decRejectBrAt + (Instr.bcond 0 0).size = b.off + seqSize b.code)

theorem branchAtBlockEnd_ok : branchAtBlockEnd = true := by decide +kernel

theorem decrypt_branch_position_final {b : Blk} {st : AbsState} {is : List Instr}
    (cond : BitVec 4) (imm : BitVec 8) (hm : b ∈ decryptCert)
    (hp : BlockPoint decryptEnv b decRejectBrAt st (.bcond cond imm :: is)) : is = [] := by
  have hb := blockPoint_in_blocksContaining hm hp
  have hend := of_decide_eq_true ((List.all_eq_true.mp branchAtBlockEnd_ok) b hb)
  have hext := (blockPoint_extent hp).2
  simp only [seqSize, Instr.size] at hend
  simp only [seqSize, List.map_cons, List.sum_cons, Instr.size] at hext
  have hz : (is.map Instr.size).sum = 0 := by omega
  cases is with
  | nil => rfl
  | cons i is =>
    simp only [List.map_cons, List.sum_cons] at hz
    have hi : 0 < i.size := by cases i <;> simp [Instr.size]
    omega

/-- Graph reachability through certificate block successors. -/
inductive GraphReach (env : Env) (cert : Cert) (starts : List GraphNode) : GraphNode → Prop
  | start {node} : node ∈ starts → GraphReach env cert starts node
  | next {node target} : GraphReach env cert starts node →
      target ∈ (graphBlock cert node).flatMap (graphOut env) → GraphReach env cert starts target

/-- Every checked successor of a block containing the authentication branch
is an initial node of the post-branch graph. -/
theorem decrypt_branch_successor_start {b : Blk} {target : GraphNode}
    (hb : b ∈ decryptBranchBlocks) (ht : target ∈ graphOut decryptEnv b) :
    GraphReach decryptEnv decryptCert decryptAfterBranch target := by
  apply GraphReach.start
  exact List.mem_flatMap.mpr ⟨b, hb, ht⟩

/-- A successful execution of the designated branch takes one of the
post-branch graph's initial edges and reaches a checked successor block. -/
theorem decrypt_branch_step_graph {b : Blk} {st : AbsState} {p : Params}
    {s₁ s₂ : M0Crypto.Armv6M.State} (cond : BitVec 4) (imm : BitVec 8)
    (hm : b ∈ decryptCert)
    (hp : BlockPoint decryptEnv b decRejectBrAt st [.bcond cond imm])
    (h : LowEq p M0Crypto.Artifacts.Release.bytes decRejectBrAt st s₁ s₂)
    (hdecision : condPassed cond s₁ = condPassed cond s₂)
    (heven : (p.base + BitVec.ofNat 32 decRejectBrAt).getLsbD 0 = false) :
    ∃ target t₁ t₂ e nextBlock,
      step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      GraphReach decryptEnv decryptCert decryptAfterBranch (target, b.ctx) ∧
      findBlk decryptCert target b.ctx = some nextBlock ∧ nextBlock ∈ decryptCert ∧
      LowEq p M0Crypto.Artifacts.Release.bytes target nextBlock.st t₁ t₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer decrypt_certOk hm hp
  have hidx := certPoint_state_indices decrypt_indicesFailure_eq_none hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt decrypt_certOk hm hp
  have hs : ∀ target nextSt, (.pt target b.ctx, nextSt) ∈ out.succs → nextSt.indicesOk := by
    intro target nextSt hmem
    exact certPoint_successor_indices decrypt_indicesFailure_eq_none hm hp hx hmem
  obtain ⟨target, nextSt, t₁, t₂, e, h₁, h₂, hmem, hrel⟩ :=
    bcond_checked_step cond imm hx hidx h (fun _ => hdecision) hs heven hdecode hlen
  have hf := certPoint_final_successors decrypt_certOk hm hp hx
  obtain ⟨nextBlock, hfind, hblock, hnext⟩ :=
    checked_successor_relation hf hmem decrypt_indicesFailure_eq_none hrel
  have hb : b ∈ decryptBranchBlocks := blockPoint_in_blocksContaining hm hp
  have hedge := certPoint_final_graph_edge decrypt_certOk hm hp hx hmem
  exact ⟨target, t₁, t₂, e, nextBlock, h₁, h₂,
    decrypt_branch_successor_start hb hedge, hfind, hblock, hnext⟩

/-- A checked successor-closed set contains every graph-reachable node. -/
theorem GraphReach.subset {env : Env} {cert : Cert} {starts seen : List GraphNode}
    (hstart : starts.all seen.contains = true)
    (hclosed : seen.all (fun node =>
      ((graphBlock cert node).flatMap (graphOut env)).all seen.contains) = true)
    {node : GraphNode} (h : GraphReach env cert starts node) : node ∈ seen := by
  induction h with
  | start hmem =>
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp hstart) _ hmem)
  | next _ hmem ih =>
    have hnext := (List.all_eq_true.mp hclosed) _ ih
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp hnext) _ hmem)

/-- No certificate graph path from a branch successor returns to a block
containing the authentication branch. -/
theorem decrypt_branch_no_return {node : GraphNode}
    (h : GraphReach decryptEnv decryptCert decryptAfterBranch node)
    {b : Blk} (hb : b ∈ decryptBranchBlocks) : node ≠ (b.off, b.ctx) := by
  have hc := branchGraphCheck_ok
  simp only [branchGraphCheck, Bool.and_eq_true] at hc
  have hmem := h.subset hc.1.1.2 hc.1.2
  have hnot := (List.all_eq_true.mp hc.2) b hb
  intro heq
  subst node
  simp at hnot
  exact hnot hmem

/-- A checked block reachable after the branch cannot contain another
instruction position at the authentication branch offset. -/
theorem decrypt_after_branch_excludes_position {b : Blk} {off : Nat} {st : AbsState}
    {i : Instr} {is : List Instr}
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (i :: is))
    (hpath : GraphReach decryptEnv decryptCert decryptAfterBranch (b.off, b.ctx)) :
    off ≠ decRejectBrAt := by
  intro heq
  subst off
  have hb : b ∈ decryptBranchBlocks := blockPoint_in_blocksContaining hm hp
  exact decrypt_branch_no_return hpath hb rfl

end M0Crypto.Release.ConstantTime
