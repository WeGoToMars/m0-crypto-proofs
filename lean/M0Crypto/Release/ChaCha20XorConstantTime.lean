import M0Crypto.Release.ChaCha20StoreEvents
import M0Crypto.Release.ConstantTime.OutputSiteCheck
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.OutputSegments

set_option linter.unusedSimpArgs false

/-!
# Constant-time trace of `m0c_chacha20_xor`

The certificate relation pairs two executions with equal public inputs. It takes a matching
step at every position provided each untracked store at that position is separated from the
code and the stack window. Here the separation of a store at an output-store instruction
follows from the whole-call access events of `ChaCha20StoreEvents`: the call's artifact run
writes the output range at those instructions. Other untracked stores do not occur
(`certOutputSiteFailure`), and multiple stores use stack bases (`certStmStack`).
-/

namespace M0Crypto.Release.ChaCha20XorConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20StoreEvents

/-- Output-range bytes of an access give its separation from code and the stack window. -/
theorem separated_of_output_bounds (c : Ctx) (hv : Valid c) (op : MemOp) (a : Word)
    (h : ∀ k < op.width, c.oidx (a + BitVec.ofNat 32 k) < c.len.toNat) :
    Disj c.base Artifacts.Release.size a op.width ∧
    Disj (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) a op.width := by
  have hw := memOp_width_pos op
  have h0 := h 0 (by omega)
  simp only [BitVec.add_zero] at h0
  exact chacha20_output_endpoints c hv op a h0 (h (op.width - 1) (by omega))

/-- A recorded write access of an output-store instruction lies in the output range. -/
theorem recorded_write_in_output (c : Ctx) {events : List Event}
    (hpol : EventAccessesTo (StorePolicy c) events) {x : State} {i : Instr}
    (hev : ⟨x.pc, i, i.accesses x⟩ ∈ events) (hsite : OutputStorePC c.base x.pc)
    {a : Access} (ha : a ∈ i.accesses x) (hk : a.kind = .write) :
    ∀ k < a.width, c.oidx (a.addr + BitVec.ofNat 32 k) < c.len.toNat := by
  intro k hk'
  rcases hpol _ hev a ha k hk' with h | ⟨_, h⟩
  · rw [hk] at h
    cases h
  · exact h hsite

/-- Multiple stores in the certificate have stack bases, so need no separation premise. -/
theorem stm_bufferStoreOk {p : Params} {bytes : List (BitVec 8)} {s : State}
    {b : Blk} {off : Nat} {st : AbsState} {n : M0Crypto.Armv6M.LowReg} {l : BitVec 8}
    {is : List Instr} (hm : b ∈ chacha20Cert)
    (hp : BlockPoint chacha20Env b off st (.stm n l :: is)) :
    BufferStoreOk chacha20Env p bytes st s (.stm n l) := by
  obtain ⟨lo, hi, hs⟩ := certPoint_stmStack chacha20_stmStack hm hp
  intro h
  exact False.elim (h lo hi hs)

/-- Every checked store of a recorded run satisfies the certificate's separation premise. -/
theorem bufferStoreOk (c : Ctx) (hv : Valid c)
    (hret : ∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {s : State} {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events))
    (hpol : EventAccessesTo (StorePolicy c) events)
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {x y : State}
    (hm : b ∈ chacha20Cert) (hp : BlockPoint chacha20Env b off st (i :: is))
    (h : LowEq ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes
      off st x y) (hmem : x ∈ states) :
    BufferStoreOk chacha20Env ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
      Artifacts.Release.bytes st x i := by
  have hstop : x.pc ≠ (c.regs0 14 &&& ~~~1#32) := by
    have hf := (certPoint_instrAt chacha20_certOk hm hp).2
    have hpos := instr_size_pos i
    have hoff : off < Artifacts.Release.size := by
      simpa [B_len] using (show off < Artifacts.Release.bytes.length by omega)
    rw [h.1]
    exact Ne.symm (hret off hoff)
  have hev := certPoint_recorded_event i chacha20_certOk chacha20_certAligned
    (by have := hv.base4; show c.base.toNat % 2 = 0; omega) hm hp h hmem hstop hrun
  cases i with
  | memImm op t n imm =>
    intro hsp hop
    have hu : untrackedStore st (.memImm op t n imm) = true := by simp [untrackedStore, hop, hsp]
    have hsite := outputStoreOffset_pc c.base off (certPoint_outputSite chacha20_outputSiteFailure_eq_none hm hp hu)
    have hsite' : OutputStorePC c.base x.pc := by rw [h.1]; exact hsite
    have hb := recorded_write_in_output c hpol hev hsite'
      (a := ⟨.write, x.reg n + BitVec.ofNat 32 (imm.toNat * op.width), op.width⟩)
      (by simp [Instr.accesses, hop]) rfl
    simpa [Artifacts.Release.bytes_length] using separated_of_output_bounds c hv op _ hb
  | memReg op t n m =>
    intro hsp hop
    have hu : untrackedStore st (.memReg op t n m) = true := by simp [untrackedStore, hop, hsp]
    have hsite := outputStoreOffset_pc c.base off (certPoint_outputSite chacha20_outputSiteFailure_eq_none hm hp hu)
    have hsite' : OutputStorePC c.base x.pc := by rw [h.1]; exact hsite
    have hb := recorded_write_in_output c hpol hev hsite'
      (a := ⟨.write, x.reg n + x.reg m, op.width⟩) (by simp [Instr.accesses, hop]) rfl
    simpa [Artifacts.Release.bytes_length] using separated_of_output_bounds c hv op _ hb
  | stm n l => exact stm_bufferStoreOk hm hp
  | _ => trivial

/-- **`m0c_chacha20_xor` runs with a trace independent of its secret inputs.** Two calls
satisfying the entry contract with equal public inputs have equal traces, for every fuel. -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_constant_time : TraceSpec.ChaCha20XorConstantTime := by
  intro c₁ c₂ s₁ s₂ ⟨hv₁, he₁, hlr₁, hret₁⟩ ⟨hv₂, he₂, hlr₂, hret₂⟩ hpub fuel
  replace hret₁ := Region.ne hret₁
  replace hret₂ := Region.ne hret₂
  have hlr : c₁.regs0 14 = c₂.regs0 14 := by
    simp only [Frame.Ctx.pub, Prod.mk.injEq] at hpub
    exact hpub.2.2.1
  have hc : CodeAt s₁.mem c₁.base B := by rw [he₁.mem]; exact hv₁.code
  obtain ⟨n, hn⟩ := reachEvents_runUntil hc
    (fun pc y hw i hi => by
      rcases hw with h | ⟨h, _⟩
      · cases h
      · exact chacha20_write_misses_code c₁ hv₁ h hi)
    (fun i hi => hret₁ i (by rwa [B_len] at hi))
    (xor_reach_events c₁ hv₁ s₁ he₁ hlr₁)
  obtain ⟨s', tr, hru, hpol⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  have hlocal : ∀ u₁ u₂, BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₂ u₂ →
      CertAt chacha20Env chacha20Cert ⟨c₁.base, c₁.sp0, c₁.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes u₁ u₂ →
      PositionObligations chacha20Env chacha20Cert
        ⟨c₁.base, c₁.sp0, c₁.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes u₁ u₂ := by
    intro u₁ u₂ hb₁ _ _ b off st i is hm hp hrel
    refine ⟨bufferStoreOk c₁ hv₁ hret₁ hrun hpol hm hp hrel (hb₁.mem_runStates hrun), ?_⟩
    intro cond imm _ hd
    simp [chacha20Env] at hd
  have key := certificate_reachable_trace_eq (env := chacha20Env) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.chacha20_xor) (init := entryState chacha20ArgWords) (cert := chacha20Cert)
    (p := ⟨c₁.base, c₁.sp0, c₁.regs0 14, Artifacts.Release.bytes.length⟩)
    chacha20_certOk chacha20_indicesFailure_eq_none chacha20_certAligned chacha20_slotsCheck
    (by decide)
    (by simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes, Frame.Ctx.fp,
        ChaCha20Layout.chStackBytes_eq, Artifacts.Release.bytes_length] using hv₁.codeF)
    (by simp [chacha20Env, Artifacts.Release.bytes_length]) hv₁.base4
    (by simpa [Artifacts.Release.bytes_length] using hv₁.codeF.1) hlr₁ hlocal fuel
    (chacha20_entry_reachable hv₁ he₁ hv₂ he₂ hpub)
  simpa [Frame.Ctx.ret, hlr] using key

end M0Crypto.Release.ChaCha20XorConstantTime
