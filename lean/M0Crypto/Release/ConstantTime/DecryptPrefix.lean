import M0Crypto.Release.ConstantTime.FunctionalReach
import M0Crypto.Release.ConstantTime.DecryptVerdict

/-! Functional entry-to-comparison execution. -/
set_option linter.unusedSimpArgs false
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (pad16 macData chacha20 decrypt poly1305 polyKey)

/-- The functional decrypt prefix supplies the comparison inputs. -/
theorem decrypt_reaches_compare (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) :
    Reach c.base (DAllowed c) s (fun y =>
      y.pc = c.base + BitVec.ofNat 32 decCmpAAt ∧ y.regs 13 = c.A ∧ Hi c y.mem ∧
      Ctx.bytesAt y.mem c.tag 16 = c.tagB ∧
      Ctx.bytesAt y.mem (c.A + 72#32) 16 = c.expected) := by
  apply (decrypt_compare_entry c hv hb s he).mono
  intro y ⟨hpc, hbody, htag, hexpected⟩
  exact ⟨hpc, hbody.sp, hbody.high, htag, hexpected⟩

/-- From the decryption entry, execution reaches the authentication branch with
Z equal to the functional authentication result. -/
theorem decrypt_reaches_auth_branch (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) :
    Reach c.base (DAllowed c) s (fun u =>
      u.pc = c.base + BitVec.ofNat 32 decRejectBrAt ∧
      u.z = decide (c.expected = c.tagB)) := by
  apply Reach.bind
  apply (decrypt_reaches_compare c hv hb s he).mono
  intro y ⟨hpc, hsp, hhigh, htag, hexpected⟩
  exact (compare_reaches_branch c hv y hpc hsp hhigh htag hexpected).monoW (fun _ h => False.elim h)

/-- Every successful recorded decrypt execution contains an authentication
branch state with the functional verdict flag. -/
theorem decrypt_auth_branch_recorded (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (stop : Word)
    (hstop : ∀ i < B.length, stop ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates stop fuel s = .ok (states, events)) :
    ∃ u ∈ states, u.pc = c.base + BitVec.ofNat 32 decRejectBrAt ∧
      u.z = decide (c.expected = c.tagB) := by
  obtain ⟨n, u, tr, hr, hw, hpc, hz⟩ := decrypt_reaches_auth_branch c hv hb s he
  have hcode : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have hmiss : TraceMissesCode B c.base tr := by
    intro e hevent i hi hwrite
    have hallowed := hw e hevent _ hwrite
    rw [B_len] at hi
    rcases hallowed with hstack | ⟨_, hout⟩
    · exact hv.code_not_swr hi hstack
    · exact not_out hb.codeO hi hout
  have hne : ∀ e ∈ tr, e.pc ≠ stop := by
    intro e hevent heq
    obtain ⟨off, hoff, hpc'⟩ := runH_pcs n s u tr hr e hevent
    exact hstop off hoff (heq ▸ hpc')
  have hreach := runH_beforeStop hcode hr hmiss hne
  exact ⟨u, hreach.mem_runStates hrun, hpc, hz⟩

/-- If the recorded decrypt execution has only one state at the branch PC,
that state's Z flag is the functional authentication verdict. -/
theorem decrypt_recorded_branch_flag (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (stop : Word)
    (hstop : ∀ i < B.length, stop ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates stop fuel s = .ok (states, events))
    (hunique : ∀ u ∈ states, ∀ v ∈ states,
      u.pc = c.base + BitVec.ofNat 32 decRejectBrAt → u.pc = v.pc → u = v)
    {v : State} (hmem : v ∈ states) (hpc : v.pc = c.base + BitVec.ofNat 32 decRejectBrAt) :
    v.z = decide (c.expected = c.tagB) := by
  obtain ⟨u, hu, hupc, huz⟩ := decrypt_auth_branch_recorded c hv hb s he stop hstop hrun
  have heq := hunique u hu v hmem hupc (hupc.trans hpc.symm)
  simpa [← heq] using huz

end M0Crypto.Release.ConstantTime
