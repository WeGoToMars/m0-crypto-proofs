import M0Crypto.Release.ConstantTime.RecordedUnique
import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-! A closed certificate for execution after the authentication decision. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Armv6M (State)
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- Retain the blocks found by the checked post-branch graph walk. -/
def decryptAfterCert : Cert :=
  decryptCert.filter fun b => decryptAfterReach.contains (b.off, b.ctx)

theorem decryptAfterBranch_nonempty : decryptAfterBranch ≠ [] := by decide +kernel

def decryptAfterEntry : Nat := (decryptAfterBranch.head decryptAfterBranch_nonempty).1
theorem decryptAfterEntry_exists :
    (findBlk decryptAfterCert decryptAfterEntry none).isSome = true := by decide +kernel

def decryptAfterInit : AbsState :=
  ((findBlk decryptAfterCert decryptAfterEntry none).get decryptAfterEntry_exists).st

/-- The restricted blocks form a complete, artifact-checked certificate. -/
theorem decryptAfter_certOk :
    certOk decryptEnv M0Crypto.Artifacts.Release.bytes decryptAfterEntry decryptAfterInit
      decryptAfterCert = true := by decide +kernel

theorem decryptAfter_indicesFailure : certIndicesFailure decryptAfterCert decryptEnv = none := by
  decide +kernel

theorem decryptAfter_aligned : certAligned decryptAfterCert = true := by decide +kernel

theorem decryptAfter_slots : certSlotsCheck decryptEnv decryptAfterCert = true := by decide +kernel

/-- Every node recorded by a graph walk is reachable from its initial nodes,
provided its initial seen and pending lists contain only reachable nodes. -/
theorem graphWalk_sound {env : Env} {cert : Cert} {starts : List GraphNode}
    (fuel : Nat) (seen pending : List GraphNode)
    (hseen : ∀ x ∈ seen, GraphReach env cert starts x)
    (hpending : ∀ x ∈ pending, GraphReach env cert starts x) :
    ∀ x ∈ graphWalk env cert fuel seen pending, GraphReach env cert starts x := by
  induction fuel generalizing seen pending with
  | zero => simpa [graphWalk] using hseen
  | succ fuel ih =>
    cases pending with
    | nil => simpa [graphWalk] using hseen
    | cons first rest =>
      have hfirst : GraphReach env cert starts first := hpending first (by simp)
      by_cases hm : first ∈ seen
      · simp only [graphWalk, List.contains_iff_mem, if_pos hm]
        apply ih seen rest hseen
        intro x hx
        exact hpending x (by simp [hx])
      · have hseen' : ∀ x ∈ first :: seen, GraphReach env cert starts x := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hfirst
          · exact hseen x hx
        have hpending' : ∀ x ∈ rest ++ (graphBlock cert first).flatMap (graphOut env),
            GraphReach env cert starts x := by
          intro x hx
          simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hpending x (by simp [hx])
          · exact GraphReach.next hfirst hx
        simpa only [graphWalk, List.contains_iff_mem, if_neg hm] using ih (first :: seen)
          (rest ++ (graphBlock cert first).flatMap (graphOut env)) hseen' hpending'

theorem decryptAfterReach_sound {node : GraphNode} (h : node ∈ decryptAfterReach) :
    GraphReach decryptEnv decryptCert decryptAfterBranch node := by
  apply graphWalk_sound _ [] decryptAfterBranch (by simp) ?_ node h
  intro x hx
  exact GraphReach.start hx

/-- A certificate position in the restricted certificate is a post-branch
position in the original certificate. -/
theorem decryptAfterCertAt_graph {p : Params} {s₁ s₂ : State}
    (h : CertAt decryptEnv decryptAfterCert p M0Crypto.Artifacts.Release.bytes s₁ s₂) :
    ∃ b off st i is, b ∈ decryptCert ∧
      BlockPoint decryptEnv b off st (i :: is) ∧
      GraphReach decryptEnv decryptCert decryptAfterBranch (b.off, b.ctx) ∧
      LowEq p M0Crypto.Artifacts.Release.bytes off st s₁ s₂ := by
  obtain ⟨b, off, st, code, hm, hp, hne, hrel⟩ := h
  have hm' := List.mem_filter.mp hm
  have hreach := decryptAfterReach_sound (List.contains_iff_mem.mp hm'.2)
  cases code with
  | nil => exact False.elim (hne rfl)
  | cons i is => exact ⟨b, off, st, i, is, hm'.1, hp, hreach, hrel⟩

/-- Any post-branch graph position belongs to the restricted certificate. -/
theorem decryptAfterBranchAt_cert {p : Params} {s : State}
    (h : DecryptAfterBranchAt p s) :
    CertAt decryptEnv decryptAfterCert p M0Crypto.Artifacts.Release.bytes s s := by
  obtain ⟨b, off, st, i, is, hm, hp, hpath, hrel⟩ := h
  have hc := branchGraphCheck_ok
  simp only [branchGraphCheck, Bool.and_eq_true] at hc
  have hseen := hpath.subset hc.1.1.2 hc.1.2
  have hmem : b ∈ decryptAfterCert := by
    exact List.mem_filter.mpr ⟨hm, List.contains_iff_mem.mpr hseen⟩
  exact ⟨b, off, st, i :: is, hmem, hp, by simp, hrel⟩

/-- A checked state at the authentication PC enters the post-branch graph
after its next successful machine step. -/
theorem decrypt_certAt_branch_step {p : Params} {s t : State} {event : Event}
    (h : CertAt decryptEnv decryptCert p M0Crypto.Artifacts.Release.bytes s s)
    (hpc : s.pc = p.base + BitVec.ofNat 32 decRejectBrAt)
    (hbase : p.base.toNat % 2 = 0) (hs : step s = .ok (t, event)) :
    DecryptAfterBranchAt p t := by
  obtain ⟨b, off, st, code, hm, hp, hne, hrel⟩ := h
  cases code with
  | nil => contradiction
  | cons i is =>
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
    subst off
    have hi := (certPoint_instrAt decrypt_certOk hm hp).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbr, _⟩ := dec_at
    rw [hbr] at hi
    cases hi
    have hfinal := decrypt_branch_position_final 1 (brImm8 decRejectBrAt decRejectAt) hm hp
    subst is
    have heven := certPoint_pc_even p.base hbase decrypt_certAligned hm hp
    exact decrypt_branch_step_afterBranchAt 1 (brImm8 decRejectBrAt decRejectAt)
      hm hp hrel heven hs

set_option maxRecDepth 100000 in
/-- A successful step preserves the post-branch graph invariant, subject to
the concrete separation obligation for buffer stores. -/
theorem decryptAfterBranch_step {p : Params} {s t : State} {event : Event}
    (h : DecryptAfterBranchAt p s)
    (hbuffer : ∀ b off st i is, b ∈ decryptAfterCert →
      BlockPoint decryptEnv b off st (i :: is) →
      LowEq p M0Crypto.Artifacts.Release.bytes off st s s →
      BufferStoreOk decryptEnv p M0Crypto.Artifacts.Release.bytes st s i)
    (hdisj : M0Crypto.Release.Frame.Disj p.base M0Crypto.Artifacts.Release.bytes.length
      (p.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above))
    (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + M0Crypto.Artifacts.Release.bytes.length ≤ 2 ^ 32)
    (hlr : p.lr0.getLsbD 0 = true)
    (hs : step s = .ok (t, event)) :
    DecryptAfterBranchAt p t ∨ t.pc = (p.lr0 &&& ~~~1#32) := by
  obtain ⟨b, off, st, code, hm, hp, hne, hrel⟩ := decryptAfterBranchAt_cert h
  cases code with
  | nil => exact False.elim (hne rfl)
  | cons i is =>
    have hpaired := certPoint_paired i decryptAfter_certOk decryptAfter_indicesFailure
      decryptAfter_aligned decryptAfter_slots hm hp hrel (by decide) hdisj
      (hbuffer b off st i is hm hp hrel) (pubLoadOk_self _ _ _ _) (by decide) hbase hnowrap hlr
      (by intros; rfl)
    simp only [PairedStep, hs] at hpaired
    rcases hpaired.2 with hcert | hret
    · left
      exact decryptAfterCertAt_graph hcert
    · exact Or.inr hret.1

/-- Reachability from a state in a successful recorded run stays within that
run: execution is deterministic and the run stops at the first stop PC. -/
theorem runStates_member_beforeStop {stop : M0Crypto.Armv6M.Word}
    {initial start v : State} {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates stop fuel initial = .ok (states, events))
    (hstart : start ∈ states) (hreach : BeforeStop stop start v) : v ∈ states := by
  induction hreach with
  | initial => exact hstart
  | next _ hnot hs ih => exact runStates_member_next hrun ih hnot hs

/-- A successful recorded run has at most one state at a PC if each step
from that PC cannot revisit it in the recorded suffix. -/
theorem runStates_unique_at_pc_recorded {stop pc : M0Crypto.Armv6M.Word}
    {fuel : Nat} {initial : State} {states : List State} {events : List Event}
    (hrun : runStates stop fuel initial = .ok (states, events))
    (hno : ∀ u ∈ states, u.pc = pc → ∀ t e, step u = .ok (t, e) →
      ∀ v ∈ states, BeforeStop stop t v → v.pc ≠ pc) :
    ∀ u ∈ states, ∀ v ∈ states, u.pc = pc → u.pc = v.pc → u = v := by
  induction fuel generalizing initial states events with
  | zero =>
    simp only [runStates] at hrun
    split at hrun
    · cases hrun; simp
    · contradiction
  | succ fuel ih =>
    simp only [runStates] at hrun
    split at hrun
    · cases hrun; simp
    · cases hs : step initial with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hnorest : ∀ u ∈ rest, u.pc = pc → ∀ t e, step u = .ok (t, e) →
              ∀ v ∈ rest, BeforeStop stop t v → v.pc ≠ pc := by
            intro u hu hupc t e hs' v hv hvreach
            exact hno u (by simp [hu]) hupc t e hs' v (by simp [hv]) hvreach
          intro u hu v hv hupc heq
          simp only [List.mem_cons] at hu hv
          rcases hu with rfl | hu
          · rcases hv with rfl | hv
            · rfl
            · have hvreach := runStates_beforeStop ht v hv
              exact False.elim (hno u (by simp) hupc next ev hs v (by simp [hv]) hvreach (heq ▸ hupc))
          · rcases hv with rfl | hv
            · have hureach := runStates_beforeStop ht u hu
              have hipc : v.pc = pc := heq.symm.trans hupc
              exact False.elim (hno v (by simp) hipc next ev hs u (by simp [hu]) hureach hupc)
            · exact ih ht hnorest u hu v hv hupc heq

/-- The functional authentication flag holds at each recorded branch visit
when those visits are covered by the full certificate and subsequent buffer
stores satisfy their concrete separation obligation. -/
theorem decrypt_recorded_branch_flag_of_cert
    (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (p : Params) (hbase : p.base = c.base)
    (hstop : ∀ i < B.length, (p.lr0 &&& ~~~1#32) ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, events))
    (hcert : ∀ u ∈ states, u.pc = c.base + BitVec.ofNat 32 decRejectBrAt →
      CertAt decryptEnv decryptCert p M0Crypto.Artifacts.Release.bytes u u)
    (hbuffer : ∀ x ∈ states, ∀ b off st i is, b ∈ decryptAfterCert →
      BlockPoint decryptEnv b off st (i :: is) →
      LowEq p M0Crypto.Artifacts.Release.bytes off st x x →
      BufferStoreOk decryptEnv p M0Crypto.Artifacts.Release.bytes st x i)
    (hdisj : M0Crypto.Release.Frame.Disj p.base M0Crypto.Artifacts.Release.bytes.length
      (p.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above))
    (halign : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + M0Crypto.Artifacts.Release.bytes.length ≤ 2 ^ 32)
    (hlr : p.lr0.getLsbD 0 = true)
    {v : State} (hmem : v ∈ states)
    (hpc : v.pc = c.base + BitVec.ofNat 32 decRejectBrAt) :
    v.z = decide (c.expected = c.tagB) := by
  apply decrypt_recorded_branch_flag c hv hb s he _ hstop hrun ?_ hmem hpc
  apply runStates_unique_at_pc_recorded hrun
  intro u hu hupc t e hs v _ hvreach
  have heven : p.base.toNat % 2 = 0 := by omega
  have hgraph : DecryptAfterBranchAt p t := by
    apply decrypt_certAt_branch_step (hcert u hu hupc) ?_ heven hs
    simpa [hbase] using hupc
  have hnot : u.pc ≠ (p.lr0 &&& ~~~1#32) := by
    rw [hupc]
    apply Ne.symm
    apply hstop decRejectBrAt
    rw [B_len]
    decide
  have htmem := runStates_member_next hrun hu hnot hs
  have hgraph' : DecryptAfterBranchAt p v ∨ v.pc = (p.lr0 &&& ~~~1#32) := by
    induction hvreach with
    | initial => exact Or.inl hgraph
    | next hreach hnot hs' ih =>
      have hxmem := runStates_member_beforeStop hrun htmem hreach
      rcases ih hxmem with hx | hret
      ·
        exact decryptAfterBranch_step hx (hbuffer _ hxmem) hdisj halign hnowrap hlr hs'
      · exact False.elim (hnot hret)
  rcases hgraph' with hg | hret
  · obtain ⟨b, off, st, i, is, hm, hp, hpath, hrel⟩ := hg
    simpa [hbase] using decrypt_after_branch_pc_ne hm hp hpath hrel
  · rw [hret]
    apply hstop decRejectBrAt
    rw [B_len]
    decide

end M0Crypto.Release.ConstantTime
