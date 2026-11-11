import M0Crypto.Release.ConstantTime.IndexReach
import M0Crypto.Release.ConstantTime.MovSound
import M0Crypto.Release.ConstantTime.ArithmeticSound

/-! Paired fall-through transitions within validated certificate blocks. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Armv6M (Reg LowReg)

/-- A checked register move advances both executions and the certificate's
position within the current block. -/
theorem certPoint_movHi_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (d m : Reg) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.movHi d m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    ∃ t₁ t₂ event,
      step s₁ = .ok (t₁, event) ∧ step s₂ = .ok (t₂, event) ∧
      BlockPoint env b (off + (Instr.movHi d m).size) (st.set d.val (st.get m.val)) is ∧
      LowEq p bytes (off + (Instr.movHi d m).size) (st.set d.val (st.get m.val)) t₁ t₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  obtain ⟨t₁, t₂, event, hs₁, hs₂, _, _, hnext⟩ :=
    movHi_checked_step d m hx hidx hrel heven hdecode hlen
  have ⟨hd, hs⟩ := movHi_transfer_indices hx
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have ht := movHi_transfer env off b.ctx st d m hd hs hw hb.2.1
  rw [hx] at ht
  have hout : out = ⟨[(.pt (off + (Instr.movHi d m).size) b.ctx,
      st.set d.val (st.get m.val))], []⟩ := by injection ht
  have hsucc : out.succs = [(.pt (off + (Instr.movHi d m).size) b.ctx,
      st.set d.val (st.get m.val))] := by rw [hout]
  exact ⟨t₁, t₂, event, hs₁, hs₂, BlockPoint.next hp hx hsucc, hnext⟩

/-- A checked register addition advances both executions and the certificate's
position within the current block. -/
theorem certPoint_addReg_step {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {s₁ s₂ : M0Crypto.Armv6M.State} {p : Params}
    (d n m : LowReg) (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.addReg d n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    ∃ next t₁ t₂ event,
      step s₁ = .ok (t₁, event) ∧ step s₂ = .ok (t₂, event) ∧
      BlockPoint env b (off + (Instr.addReg d n m).size) next is ∧
      LowEq p bytes (off + (Instr.addReg d n m).size) next t₁ t₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  obtain ⟨t₁, t₂, event, hs₁, hs₂, _, _, hnext⟩ :=
    addReg_checked_step d n m hx hidx hrel heven hdecode hlen
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.addReg d n m).size) b.ctx,
      { st.set d.val (addRes (st.get n.val) (st.get m.val) (.known false)
        ((st.get n.val).add (st.get m.val))).1 with
        fl := (addRes (st.get n.val) (st.get m.val) (.known false)
          ((st.get n.val).add (st.get m.val))).2 })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  exact ⟨_, t₁, t₂, event, hs₁, hs₂, BlockPoint.next hp hx hsucc, hnext⟩

end M0Crypto.Release.ConstantTime
