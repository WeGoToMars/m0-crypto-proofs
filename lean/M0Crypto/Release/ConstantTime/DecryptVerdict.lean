import M0Crypto.Release.ConstantTime.InstructionCases
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-! Authentication decision at the checked decryption branch. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
open M0Crypto.Release.Aead
open M0Crypto.Release.Frame (Ctx)

/-- The functional compare invariant makes the verdict block's zero flag
exactly the authentication decision. -/
theorem verdict_zero_of_compare (c : ACall) (s : State)
    (hcmp : s.regs 3 = 0#32 ↔
      Ctx.bytesAt s.mem c.tag 16 = Ctx.bytesAt s.mem (c.A + 72#32) 16)
    (htag : Ctx.bytesAt s.mem c.tag 16 = c.tagB)
    (hexpected : Ctx.bytesAt s.mem (c.A + 72#32) 16 = c.expected) :
    (execAll verdict s).z = decide (c.expected = c.tagB) := by
  rw [(verdict_effect s).1]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [hcmp, htag, hexpected]
  exact eq_comm

/-- The functional comparison reaches the verdict block with its accumulator
encoding the authentication decision. -/
theorem compare_reaches_verdict (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 decCmpAAt)
    (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (htag : Ctx.bytesAt s.mem c.tag 16 = c.tagB)
    (hexpected : Ctx.bytesAt s.mem (c.A + 72#32) 16 = c.expected) :
    M0Crypto.Release.Reach c.base (fun _ => False) s (fun t =>
      t.pc = c.base + BitVec.ofNat 32 decVerdictAt ∧
      (execAll verdict t).z = decide (c.expected = c.tagB)) := by
  apply ((compare_reach c hv s hp hs hh).monoW (fun _ h => False.elim h)).mono
  rintro t ⟨htpc, hmem, _, hcmp⟩
  refine ⟨htpc, verdict_zero_of_compare c t (by simpa [hmem] using hcmp) ?_ ?_⟩
  · simpa [hmem] using htag
  · simpa [hmem] using hexpected

set_option maxRecDepth 4096 in
/-- The comparison followed by the verdict block reaches the actual branch
with Z equal to the authentication result. -/
theorem compare_reaches_branch (c : ACall) (hv : AValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 decCmpAAt)
    (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (htag : Ctx.bytesAt s.mem c.tag 16 = c.tagB)
    (hexpected : Ctx.bytesAt s.mem (c.A + 72#32) 16 = c.expected) :
    M0Crypto.Release.Reach c.base (fun _ => False) s (fun u =>
      u.pc = c.base + BitVec.ofNat 32 decRejectBrAt ∧
      u.z = decide (c.expected = c.tagB)) := by
  apply M0Crypto.Release.Reach.bind
  apply (compare_reaches_verdict c hv s hp hs hh htag hexpected).mono
  intro t ⟨htpc, hz⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hverdict, _, _⟩ := dec_at
  apply M0Crypto.Release.Reach.block (by have := hv.base4; omega) verdict decVerdictAt htpc
    (by decide) hverdict (by decide)
    (by simp [alignedAll, verdict, Instr.accesses])
    (M0Crypto.Release.WritesTo.of_noWritesMem _ _ (by decide) _)
  apply M0Crypto.Release.Reach.done
  refine ⟨?_, hz⟩
  rw [execAll_pc _ _ (by decide), htpc, ofNat_add_assoc]
  rfl

/-- At the designated declassification offset the checked artifact contains
the not-equal branch used by the authentication verdict. -/
theorem decrypt_declass_condition {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    (cond : BitVec 4) (imm : BitVec 8)
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (.bcond cond imm :: is))
    (hsite : decryptEnv.declass = some off) : cond = 1 := by
  have hoff : off = decRejectBrAt := by simpa [decryptEnv] using hsite.symm
  subst off
  have hi := (certPoint_instrAt decrypt_certOk hm hp).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbr, _⟩ := dec_at
  rw [hbr] at hi
  cases hi
  rfl

/-- When the two branch states carry their authentication verdict in Z,
equal verdicts discharge the certificate's declassification obligation. -/
theorem decrypt_declass_agrees {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    (c₁ c₂ : ACall) (s₁ s₂ : State) (cond : BitVec 4) (imm : BitVec 8)
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (.bcond cond imm :: is))
    (hsite : decryptEnv.declass = some off)
    (hz₁ : s₁.z = decide (c₁.expected = c₁.tagB))
    (hz₂ : s₂.z = decide (c₂.expected = c₂.tagB))
    (hverdict : (c₁.expected = c₁.tagB) = (c₂.expected = c₂.tagB)) :
    condPassed cond s₁ = condPassed cond s₂ := by
  have hc := decrypt_declass_condition cond imm hm hp hsite
  subst cond
  change (!s₁.z) = (!s₂.z)
  rw [hz₁, hz₂]
  simp [hverdict]

end M0Crypto.Release.ConstantTime
