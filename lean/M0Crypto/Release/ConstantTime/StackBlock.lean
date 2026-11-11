import M0Crypto.Release.ConstantTime.IndexReach
import M0Crypto.Release.ConstantTime.StackStoreSound

/-! Stack accesses at validated certificate block positions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Armv6M (LowReg)

/-- A checked stack load either faults equally or advances both executions and
the certificate position. -/
theorem certPoint_ldrSp_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (t : LowReg) (imm : BitVec 8) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.ldrSp t imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    (∃ fault, step s₁ = .error fault ∧ step s₂ = .error fault) ∨
    ∃ next u₁ u₂ event, step s₁ = .ok (u₁, event) ∧ step s₂ = .ok (u₂, event) ∧
      BlockPoint env b (off + (Instr.ldrSp t imm).size) next is ∧
      LowEq p bytes (off + (Instr.ldrSp t imm).size) next u₁ u₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  rcases ldrSp_checked_step t imm hx hidx hrel heven hdecode hlen with hf | hs
  · exact .inl hf
  · right
    obtain ⟨u₁, u₂, event, hs₁, hs₂, _, _, hnext⟩ := hs
    have hb := xfer_sp_bounds hx
    have hw : env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers, hb.1, hb.2.2]
    have hout : out = ⟨[(.pt (off + (Instr.ldrSp t imm).size) b.ctx,
        st.set t.val (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat))))], []⟩ := by
      simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
        xferCore] at hx
      split at hx <;> simp_all [fall]
    have hsucc := congrArg Out.succs hout
    exact ⟨_, u₁, u₂, event, hs₁, hs₂, BlockPoint.next hp hx hsucc, hnext⟩

/-- A checked stack store either faults equally or advances both executions and
the certificate position. The stack window must be disjoint from the code. -/
theorem certPoint_strSp_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (t : LowReg) (imm : BitVec 8) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hslots : certSlotsCheck env cert = true)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.strSp t imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂) (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    (∃ fault, step s₁ = .error fault ∧ step s₂ = .error fault) ∨
    ∃ next u₁ u₂ event, step s₁ = .ok (u₁, event) ∧ step s₂ = .ok (u₂, event) ∧
      BlockPoint env b (off + (Instr.strSp t imm).size) next is ∧
      LowEq p bytes (off + (Instr.strSp t imm).size) next u₁ u₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have hstack := certPoint_stackCheck hslots hm hp
  have ⟨hcode₁, hcode₂⟩ := strSp_code_preserved t imm hx hrel hdisj
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  rcases strSp_checked_step t imm hx hidx hrel hwidth hstack hcode₁ hcode₂
      heven hdecode hlen with hf | hs
  · exact .inl hf
  · right
    obtain ⟨u₁, u₂, event, hs₁, hs₂, _, _, hnext⟩ := hs
    have hb := xfer_sp_bounds hx
    have hw : env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers, hb.1, hb.2.2]
    have hwin : env.win.covers (st.spOff + (imm.toNat * 4 : Nat))
        (st.spOff + (imm.toNat * 4 : Nat) + 4) = true := by
      have ht := hx
      simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at ht
      split at ht <;> simp_all
    have hout : out = ⟨[(.pt (off + (Instr.strSp t imm).size) b.ctx,
        { st with stk := stkSet st.stk (st.spOff + (imm.toNat * 4 : Nat)) (st.get t.val) })], []⟩ := by
      have ht := hx
      simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
        xferCore, hwin, fall, Except.ok.injEq] at ht
      exact ht.symm
    have hsucc := congrArg Out.succs hout
    exact ⟨_, u₁, u₂, event, hs₁, hs₂, BlockPoint.next hp hx hsucc, hnext⟩

end M0Crypto.Release.ConstantTime
