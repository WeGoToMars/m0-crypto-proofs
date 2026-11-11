import M0Crypto.Release.ConstantTime.StackBlock
import M0Crypto.Release.ConstantTime.SequentialBlock
import M0Crypto.Release.ConstantTime.ConditionalBlock
import M0Crypto.Release.ConstantTime.RunRelation
import M0Crypto.Release.ConstantTime.LogicalSound

/-! Certificate positions used to relate reachable pairs of machine states. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Armv6M (State Reg LowReg Word)

/-- A pair of states related at a nonempty instruction position of a checked
certificate block. -/
def CertAt (env : Env) (cert : Cert) (p : Params) (bytes : List (BitVec 8))
    (s₁ s₂ : State) : Prop :=
  ∃ b off st code, b ∈ cert ∧ BlockPoint env b off st code ∧ code ≠ [] ∧
    LowEq p bytes off st s₁ s₂

/-- Successful block validation excludes an empty instruction sequence. -/
theorem certBlock_nonempty {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert) : b.code ≠ [] := by
  intro hnil
  obtain ⟨_, _, hr, _⟩ := blkFailure_run (certOk_block hc hm)
  rw [hnil] at hr
  simp [runBlock] at hr

/-- A validated block head denotes a reachable certificate position. -/
theorem certAt_head {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hrel : LowEq p bytes b.off b.st s₁ s₂) : CertAt env cert p bytes s₁ s₂ :=
  ⟨b, b.off, b.st, b.code, hm, .entry, certBlock_nonempty hc hm, hrel⟩

/-- Empty fall-through suffixes normalize to their checked successor head. -/
theorem certAt_point {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st code) (hrel : LowEq p bytes off st s₁ s₂) :
    CertAt env cert p bytes s₁ s₂ := by
  by_cases hnil : code = []
  · obtain ⟨next, hfind, hmem, hnext⟩ := certPoint_fallthrough_head hc hi hm hp hnil hrel
    have hoff : next.off = off := by
      have hs := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      exact hs.1
    apply certAt_head hc hmem
    simpa [hoff] using hnext
  · exact ⟨b, off, st, code, hm, hp, hnil, hrel⟩

/-- Related certificate positions have equal PCs. -/
theorem CertAt.pc_eq {env : Env} {cert : Cert} {p : Params} {bytes : List (BitVec 8)}
    {s₁ s₂ : State} (h : CertAt env cert p bytes s₁ s₂) : s₁.pc = s₂.pc := by
  obtain ⟨_, _, _, _, _, _, _, hrel⟩ := h
  exact hrel.pc_eq.symm

/-- Equal successful steps into a checked block position preserve `CertAt`. -/
theorem certAt_paired_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    {p : Params} {s₁ s₂ t₁ t₂ : State} {event : Event}
    (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st code) (hrel : LowEq p bytes off st t₁ t₂)
    (hs₁ : step s₁ = .ok (t₁, event)) (hs₂ : step s₂ = .ok (t₂, event)) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  have hnext := certAt_point hc hi hm hp hrel
  simp [PairedStep, hs₁, hs₂, hnext]

/-- Equal machine faults also satisfy the paired-step relation. -/
theorem certAt_paired_fault {env : Env} {cert : Cert} {p : Params} {bytes : List (BitVec 8)}
    {s₁ s₂ : State} {fault : Fault} (h₁ : step s₁ = .error fault)
    (h₂ : step s₂ = .error fault) : PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  simp [PairedStep, h₁, h₂]

/-- Register moves preserve the reachable-pair relation. -/
theorem certPoint_movHi_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : Reg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.movHi d m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨_, _, _, hs₁, hs₂, hpoint, hnext⟩ := certPoint_movHi_step d m hc hi hm hp hrel heven
  exact certAt_paired_step hc hi hm hpoint hnext hs₁ hs₂

/-- Register additions preserve the reachable-pair relation. -/
theorem certPoint_addReg_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d n m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.addReg d n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨_, _, _, _, hs₁, hs₂, hpoint, hnext⟩ := certPoint_addReg_step d n m hc hi hm hp hrel heven
  exact certAt_paired_step hc hi hm hpoint hnext hs₁ hs₂

/-- Checked XOR, OR, and multiplication preserve the reachable-pair relation. -/
theorem certPoint_logical_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : DpOp) (d m : LowReg)
    (hop : op = .eors ∨ op = .orrs ∨ op = .muls)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp op d m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  obtain ⟨_, _, _, hs₁, hs₂, _, _, hnext⟩ :=
    logical_checked_step op d m hop hx hidx hrel heven hdecode hlen
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp op d m).size) b.ctx,
      { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
        fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) })], []⟩ := by
    rcases hop with rfl | rfl | rfl <;>
      simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  exact certAt_paired_step hc hi hm (BlockPoint.next hp hx hsucc) hnext hs₁ hs₂

/-- Stack loads preserve the reachable-pair relation or produce equal faults. -/
theorem certPoint_ldrSp_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (t : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldrSp t imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  rcases certPoint_ldrSp_step t imm hc hi hm hp hrel heven with ⟨_, hs₁, hs₂⟩ | hs
  · exact certAt_paired_fault hs₁ hs₂
  · obtain ⟨_, _, _, _, hs₁, hs₂, hpoint, hnext⟩ := hs
    exact certAt_paired_step hc hi hm hpoint hnext hs₁ hs₂

/-- Stack stores preserve the reachable-pair relation or produce equal faults. -/
theorem certPoint_strSp_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (t : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.strSp t imm :: is)) (hrel : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  rcases certPoint_strSp_step t imm hc hi hslots hm hp hrel hwidth hdisj heven with
    ⟨_, hs₁, hs₂⟩ | hs
  · exact certAt_paired_fault hs₁ hs₂
  · obtain ⟨_, _, _, _, hs₁, hs₂, hpoint, hnext⟩ := hs
    exact certAt_paired_step hc hi hm hpoint hnext hs₁ hs₂

/-- A resolved successor block yields a reachable certificate position. -/
theorem certAt_resolved {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {ctx : Option Nat}
    {p : Params} {s₁ s₂ : State} (hc : certOk env bytes entry init cert = true)
    (hfind : findBlk cert off ctx = some b) (hm : b ∈ cert)
    (hrel : LowEq p bytes off b.st s₁ s₂) : CertAt env cert p bytes s₁ s₂ := by
  have hs := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  apply certAt_head hc hm
  simpa [hs.1] using hrel

/-- A checked direct branch preserves the reachable-pair relation. -/
theorem certPoint_branch_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (imm : BitVec 11)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.b imm])
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  obtain ⟨_, _, _, _, _, hs₁, hs₂, hfind, hmem, hnext⟩ :=
    certPoint_branch_step imm hc hi hm hp hx hidx hrel heven
  have hn := certAt_resolved hc hfind hmem hnext
  simp [PairedStep, hs₁, hs₂, hn]

/-- A checked conditional branch preserves the reachable-pair relation when
the designated declassification decision agrees. -/
theorem certPoint_bcond_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (cond : BitVec 4) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [.bcond cond imm])
    (hrel : LowEq p bytes off st s₁ s₂)
    (hdeclass : env.declass = some off → condPassed cond s₁ = condPassed cond s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨_, _, _, _, _, hs₁, hs₂, hfind, hmem, hnext⟩ :=
    certPoint_bcond_step cond imm hc hi hm hp hrel hdeclass heven
  have hn := certAt_resolved hc hfind hmem hnext
  simp [PairedStep, hs₁, hs₂, hn]

/-- States are related while inside the certificate, or after both have reached
the common return address. -/
def RunRel (env : Env) (cert : Cert) (p : Params) (bytes : List (BitVec 8))
    (stop : Word) (s₁ s₂ : State) : Prop :=
  CertAt env cert p bytes s₁ s₂ ∨ (s₁.pc = stop ∧ s₂.pc = stop)

theorem RunRel.pc_eq {env : Env} {cert : Cert} {p : Params} {bytes : List (BitVec 8)}
    {stop : Word} {s₁ s₂ : State} (h : RunRel env cert p bytes stop s₁ s₂) :
    s₁.pc = s₂.pc := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact h.pc_eq
  · exact h₁.trans h₂.symm

/-- A step preserving an in-certificate relation also preserves the run relation. -/
theorem PairedStep.toRunRel {env : Env} {cert : Cert} {p : Params} {bytes : List (BitVec 8)}
    {stop : Word} {s₁ s₂ : State} (h : PairedStep (CertAt env cert p bytes) s₁ s₂) :
    PairedStep (RunRel env cert p bytes stop) s₁ s₂ := by
  unfold PairedStep at *
  cases h₁ : step s₁ with
  | error e₁ =>
    cases h₂ : step s₂ <;> simp_all
  | ok a =>
    cases a with
    | mk t₁ e₁ =>
      cases h₂ : step s₂ with
      | error e₂ => simp_all
      | ok b =>
        cases b with
        | mk t₂ e₂ => simp_all [RunRel]

/-- Local preservation of the run relation gives equal traces at every fuel. -/
theorem runRel_trace_eq {env : Env} {cert : Cert} {p : Params} {bytes : List (BitVec 8)}
    {stop : Word}
    (hstep : ∀ s₁ s₂, RunRel env cert p bytes stop s₁ s₂ → s₁.pc ≠ stop →
      PairedStep (RunRel env cert p bytes stop) s₁ s₂)
    (fuel : Nat) {s₁ s₂ : State} (h : RunRel env cert p bytes stop s₁ s₂) :
    (runUntil stop fuel s₁).map Prod.snd = (runUntil stop fuel s₂).map Prod.snd :=
  runUntil_trace_eq _ stop (fun _ _ hr => hr.pc_eq) hstep fuel s₁ s₂ h

end M0Crypto.Release.ConstantTime
