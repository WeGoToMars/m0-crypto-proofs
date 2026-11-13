import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ConstantTime.StmCertificate
import M0Crypto.Release.ConstantTime.AeadDecryptEntry
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Stm
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Writes

/-! Buffer-store obligations of the decryption certificate, discharged by the functional
write bounds. Kept apart from `FunctionalWrites` because it needs the checked certificate. -/
set_option maxRecDepth 100000
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- A recorded immediate-offset store has the required separation once its
bytes are classified as non-stack. -/
theorem decrypt_recorded_memImm_separated (c : ACall) (hv : AValid c) (hb : ABuf c)
    (s x : State) (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events))
    {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (.memImm op t n imm :: is))
    (h : LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes off st x x)
    (hmem : x ∈ states) (hstop : x.pc ≠ (c.regs0 14 &&& ~~~1#32))
    (hop : op.isLoad = false)
    (hstack : ∀ k, k < op.width → ¬ SWr c.A
      (x.reg n + BitVec.ofNat 32 (imm.toNat * op.width) + BitVec.ofNat 32 k)) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.size
      (x.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width ∧
    Frame.Disj (c.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above)
      (x.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width := by
  apply decrypt_store_bounds_of_write_bounds c hb op _ ?_ hstack
  exact certPoint_memImm_recorded_writes (Wr := DAllowed c) op t n imm
    decrypt_certOk decrypt_certAligned (by dsimp; have := hv.base4; omega) hm hp h hmem hstop hrun hop
    (decrypt_recorded_writes c hv hb s he hlr hret hrun)

/-- The corresponding separation result for a register-offset store. -/
theorem decrypt_recorded_memReg_separated (c : ACall) (hv : AValid c) (hb : ABuf c)
    (s x : State) (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events))
    {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (.memReg op t n m :: is))
    (h : LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes off st x x)
    (hmem : x ∈ states) (hstop : x.pc ≠ (c.regs0 14 &&& ~~~1#32))
    (hop : op.isLoad = false)
    (hstack : ∀ k, k < op.width → ¬ SWr c.A (x.reg n + x.reg m + BitVec.ofNat 32 k)) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.size (x.reg n + x.reg m) op.width ∧
    Frame.Disj (c.sp0 - BitVec.ofNat 32 decryptEnv.win.below)
      (decryptEnv.win.below + decryptEnv.win.above) (x.reg n + x.reg m) op.width := by
  apply decrypt_store_bounds_of_write_bounds c hb op _ ?_ hstack
  exact certPoint_memReg_recorded_writes (Wr := DAllowed c) op t n m
    decrypt_certOk decrypt_certAligned (by dsimp; have := hv.base4; omega) hm hp h hmem hstop hrun hop
    (decrypt_recorded_writes c hv hb s he hlr hret hrun)

/-- Functional write bounds and site classification discharge the certificate
store obligation, including multiple stores checked to use stack bases. -/
theorem decrypt_recorded_bufferStoreOk (c : ACall) (hv : AValid c) (hb : ABuf c)
    (s x : State) (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size,
      c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events))
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hm : b ∈ decryptCert) (hp : BlockPoint decryptEnv b off st (i :: is))
    (h : LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes off st x x) (hmem : x ∈ states)
    (hclass : NonStackStoreBytes c st x i) :
    BufferStoreOk decryptEnv
      ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes st x i := by
  have hstop : x.pc ≠ (c.regs0 14 &&& ~~~1#32) := by
    have hf := (certPoint_instrAt decrypt_certOk hm hp).2
    have hpos := instr_size_pos i
    have hoff : off < M0Crypto.Artifacts.Release.size := by simpa [B_len] using (show off < M0Crypto.Artifacts.Release.bytes.length by omega)
    rw [h.1]
    exact Ne.symm (hret off hoff)
  cases i with
  | memImm op t n imm =>
    intro hsp hop
    simpa [B_len] using decrypt_recorded_memImm_separated c hv hb s x he hlr hret hrun
      op t n imm hm hp h hmem hstop hop (hclass hsp hop)
  | memReg op t n m =>
    intro hsp hop
    simpa [B_len] using decrypt_recorded_memReg_separated c hv hb s x he hlr hret hrun
      op t n m hm hp h hmem hstop hop (hclass hsp hop)
  | stm n l => exact decrypt_stm_bufferStoreOk hm hp
  | _ => trivial

end M0Crypto.Release.ConstantTime
