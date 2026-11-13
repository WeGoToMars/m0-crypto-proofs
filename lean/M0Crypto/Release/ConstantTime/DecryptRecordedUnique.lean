import M0Crypto.Release.ConstantTime.DecryptControlGraph
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-! Deterministic recorded-run composition for a non-repeating program counter. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- A concrete state represented by a post-branch graph position cannot be
at the authentication branch PC. -/
theorem decrypt_after_branch_pc_ne {b : Blk} {off : Nat} {st : AbsState}
    {i : Instr} {is : List Instr} {p : Params} {s₁ s₂ : State}
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (i :: is))
    (hpath : GraphReach decryptEnv decryptCert decryptAfterBranch (b.off, b.ctx))
    (hrel : LowEq p M0Crypto.Artifacts.Release.bytes off st s₁ s₂) :
    s₁.pc ≠ p.base + BitVec.ofNat 32 decRejectBrAt := by
  intro hpc
  have heq : p.base + BitVec.ofNat 32 off =
      p.base + BitVec.ofNat 32 decRejectBrAt := hrel.1.symm.trans hpc
  have hword : BitVec.ofNat 32 off = BitVec.ofNat 32 decRejectBrAt := by bv_omega
  have hoff : off < 2 ^ 32 := by
    have hbound := (certPoint_instrAt decrypt_certOk hm hp).2
    rw [M0Crypto.Artifacts.Release.bytes_length] at hbound
    have hpos : 0 < i.size := by cases i <;> simp [Instr.size]
    simp [M0Crypto.Artifacts.Release.size] at hbound
    omega
  have hbranch : decRejectBrAt < 2 ^ 32 := by decide
  have hn := congrArg BitVec.toNat hword
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hbranch] at hn
  exact decrypt_after_branch_excludes_position hm hp hpath hn

/-- A state is represented at a checked position in the post-branch graph. -/
def DecryptAfterBranchAt (p : Params) (s : State) : Prop :=
  ∃ b off st i is, b ∈ decryptCert ∧
    BlockPoint decryptEnv b off st (i :: is) ∧
    GraphReach decryptEnv decryptCert decryptAfterBranch (b.off, b.ctx) ∧
    LowEq p M0Crypto.Artifacts.Release.bytes off st s s

/-- Stepping the authentication branch establishes the post-branch graph
position invariant for the successor state. -/
theorem decrypt_branch_step_afterBranchAt {b : Blk} {st : AbsState} {p : Params}
    {s t : State} {event : Event} (cond : BitVec 4) (imm : BitVec 8)
    (hm : b ∈ decryptCert)
    (hp : BlockPoint decryptEnv b decRejectBrAt st [.bcond cond imm])
    (hrel : LowEq p M0Crypto.Artifacts.Release.bytes decRejectBrAt st s s)
    (heven : (p.base + BitVec.ofNat 32 decRejectBrAt).getLsbD 0 = false)
    (hstep : step s = .ok (t, event)) : DecryptAfterBranchAt p t := by
  obtain ⟨target, t₁, t₂, e, hblock, h₁, h₂, hpath, hfind, hm', hrel'⟩ :=
    decrypt_branch_step_graph cond imm hm hp hrel rfl heven
  have h₁' := hstep.symm.trans h₁
  have h₂' := hstep.symm.trans h₂
  cases h₁'
  cases h₂'
  have hnode := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hnode
  have hcode := certBlock_nonempty decrypt_certOk hm'
  cases hc : hblock.code with
  | nil => exact False.elim (hcode hc)
  | cons i is =>
    refine ⟨hblock, hblock.off, hblock.st, i, is, hm', ?_, ?_, ?_⟩
    · simpa [hc] using (BlockPoint.entry (env := decryptEnv) (b := hblock))
    · simpa [hnode.1, hnode.2] using hpath
    · simpa [hnode.1] using hrel'

end M0Crypto.Release.ConstantTime
