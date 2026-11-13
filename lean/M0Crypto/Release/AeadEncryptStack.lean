import M0Crypto.Release.AeadDecryptStack
import M0Crypto.Release.AeadEncryptSite

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Stack bounds of AEAD encryption

`encrypt_reach_p` bounds, at every visited state, the writes of the step. An untracked store of
the encrypt certificate is either an output-store instruction of the encrypting ChaCha call
(counter word `1`: writes the output) or one of the tag-emit stores of the Poly1305 finish call
(writes only the tag). Either way its bytes are separated from the code and the analysis stack
window, which is the certificate's store-separation premise.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

theorem encrypt_stmStack : certStmStack encryptEnv encryptCert = true := by
  decide +kernel

theorem encrypt_stm_bufferStoreOk {p : Params} {bytes : List (BitVec 8)} {s : State}
    {b : Blk} {off : Nat} {st : AbsState} {n : M0Crypto.Armv6M.LowReg} {l : BitVec 8}
    {is : List Instr} (hm : b ∈ encryptCert)
    (hp : BlockPoint encryptEnv b off st (.stm n l :: is)) :
    BufferStoreOk encryptEnv p bytes st s (.stm n l) := by
  obtain ⟨lo, hi, hs⟩ := certPoint_stmStack encrypt_stmStack hm hp
  intro h
  exact False.elim (h lo hi hs)

theorem inFrame_tag_lt {tg y : Word} (h : Frame.InFrame tg 4 y) : (y - tg).toNat < 16 := by
  obtain ⟨o, ho, rfl⟩ := h
  have : tg + BitVec.ofNat 32 o - tg = BitVec.ofNat 32 o := by
    rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _
  rw [this, BitVec.toNat_ofNat]
  omega

/-- A store whose written bytes all lie in the output buffer, or all in the tag, is separated
from the code and the analysis stack window. -/
theorem encrypt_store_sep (c : ACall) (hb : ABuf c) (op : MemOp) (a : Word)
    (hw : (∀ k, k < op.width → OutR c (a + BitVec.ofNat 32 k)) ∨
      (∀ k, k < op.width → Frame.InFrame c.tag 4 (a + BitVec.ofNat 32 k))) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.size a op.width ∧
    Frame.Disj (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) a op.width := by
  have hwpos := memOp_width_pos op
  rcases hw with hw | hw
  · have h0 := hw 0 (by omega)
    simp only [BitVec.add_zero] at h0
    exact aead_output_endpoints c hb op a h0 (hw (op.width - 1) (by omega))
  · have h0 := inFrame_tag_lt (hw 0 (by omega))
    simp only [BitVec.add_zero] at h0
    exact aead_tag_endpoints c hb op a h0 (inFrame_tag_lt (hw (op.width - 1) (by omega)))

/-- Policy-classified writes of the step at `x` give the buffer-store premise. -/
theorem encrypt_bufferStoreOk_of_policy (c : ACall) (hb : ABuf c) {st : AbsState} {x : State} {i : Instr}
    (hnstm : ∀ n l, i ≠ .stm n l)
    (hw : (∀ y, Writes (i.accesses x) y → OutR c y) ∨
      (∀ y, Writes (i.accesses x) y → Frame.InFrame c.tag 4 y)) :
    BufferStoreOk encryptEnv ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes st x i := by
  cases i with
  | memImm op t n imm =>
    intro _ hop
    have := encrypt_store_sep c hb op (x.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) (by
      have wr : ∀ k, k < op.width → Writes ((Instr.memImm op t n imm).accesses x)
          (x.reg n + BitVec.ofNat 32 (imm.toNat * op.width) + BitVec.ofNat 32 k) := fun k hk =>
        ⟨⟨.write, x.reg n + BitVec.ofNat 32 (imm.toNat * op.width), op.width⟩,
          by simp [Instr.accesses, hop], rfl, k, hk, rfl⟩
      rcases hw with h | h
      · exact Or.inl fun k hk => h _ (wr k hk)
      · exact Or.inr fun k hk => h _ (wr k hk))
    simpa [B_len] using this
  | memReg op t n m =>
    intro _ hop
    have := encrypt_store_sep c hb op (x.reg n + x.reg m) (by
      have wr : ∀ k, k < op.width → Writes ((Instr.memReg op t n m).accesses x)
          (x.reg n + x.reg m + BitVec.ofNat 32 k) := fun k hk =>
        ⟨⟨.write, x.reg n + x.reg m, op.width⟩, by simp [Instr.accesses, hop], rfl, k, hk, rfl⟩
      rcases hw with h | h
      · exact Or.inl fun k hk => h _ (wr k hk)
      · exact Or.inr fun k hk => h _ (wr k hk))
    simpa [B_len] using this
  | stm n l => exact absurd rfl (hnstm n l)
  | _ => trivial

theorem encrypt_pol_recorded (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, x.pc ≠ c.regs0 14 &&& ~~~1#32 →
      ∃ t e, step x = .ok (t, e) ∧ PolE c c.tag (EncAllPc c.base) (AWr c) x e := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have h : ReachS c.base (PolE c c.tag (EncAllPc c.base) (AWr c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ EncryptResult c t) :=
    (encrypt_reach_p (Pc := EncAllPc c.base) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.toRetPost.pc, h⟩)
  refine ReachS.recorded ?_ hc h hrun
  intro x e h i hi hw
  rw [B_len] at hi
  rcases h.1.1.2 _ hw with hs | ho | ht
  · exact hv.code_not_swr hi hs
  · exact not_out hb.codeO hi ho
  · exact not_tag hb.codeT hi ht

/-- The artifact is disjoint from the encrypt stack window and does not wrap. -/
theorem encrypt_frame (c : ACall) (hv : AValid c) :
    Frame.Disj c.base M0Crypto.Artifacts.Release.bytes.length
      (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) ∧
    c.base.toNat + M0Crypto.Artifacts.Release.bytes.length ≤ 2 ^ 32 :=
  ⟨by simpa [encryptEnv, aeadArgWords, M0Crypto.Release.TraceSpec.aeadStackBytes, B_len] using hv.codeS,
   by simpa [B_len] using hv.codeS.1⟩

/-- Every checked store of a recorded encrypt run satisfies the certificate's separation
premise (both runs of the constant-time pairing use it for the first run). -/
theorem encrypt_hbuffer (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, ∀ y b off st i is, b ∈ encryptCert →
    BlockPoint encryptEnv b off st (i :: is) →
    LowEq ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes off st x y →
    BufferStoreOk encryptEnv
      ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
      M0Crypto.Artifacts.Release.bytes st x i := by
  intro x hx y b off st i is hm hp hlow
  have hstop := point_pc_ne_stop encrypt_certOk hret hm hp hlow
  obtain ⟨t', e, hst, hpol⟩ := encrypt_pol_recorded c hv hb s he hlr hrun x hx hstop
  have hev := ChaCha20XorReads.certPoint_step_event i encrypt_certOk encrypt_certAligned
    (by show c.base.toNat % 2 = 0; have := hv.base4; omega) hm hp hlow hst
  have key : untrackedStore st i = true →
      ((∀ y, Writes (i.accesses x) y → OutR c y) ∨
        (∀ y, Writes (i.accesses x) y → Frame.InFrame c.tag 4 y)) := by
    intro hu
    rcases untracked_cases encrypt_counter hm hp hu with ⟨hsite, hcnt⟩ | hf
    · left
      have hc1 := counter_of_stack (x := x) (y := y) hlow.stack (by simpa using hcnt)
      have hc2 : read32 x.mem (c.A + 4#32) = 1#32 := by
        rw [← counter_eq c]; exact hc1
      have hsite' : OutputStorePC c.base e.pc := by
        rw [hev]; dsimp only; rw [hlow.pc]; exact outputStoreOffset_pc _ _ hsite
      have := hpol.1.2 hsite' hc2
      rw [hev] at this; exact this
    · right
      have hoff : emitStoresAt ≤ off ∧ off < Poly1305Finish.clearAt := by
        simp [emitSite] at hf; exact hf.2
      have hem : Poly1305Finish.EmitPc c.base e.pc := by
        rw [hev]; dsimp only; rw [hlow.pc]
        have h1 : Poly1305Finish.emitAt ≤ emitStoresAt := by decide
        exact ⟨off, by omega, by omega, rfl⟩
      have := hpol.2 hem
      rw [hev] at this; exact this
  cases i with
  | memImm op t n imm =>
    intro hsp hop
    have hu : untrackedStore st (.memImm op t n imm) = true := by simp [untrackedStore, hop, hsp]
    exact encrypt_bufferStoreOk_of_policy c hb (fun _ _ => by simp) (key hu) hsp hop
  | memReg op t n m =>
    intro hsp hop
    have hu : untrackedStore st (.memReg op t n m) = true := by simp [untrackedStore, hop, hsp]
    exact encrypt_bufferStoreOk_of_policy c hb (fun _ _ => by simp) (key hu) hsp hop
  | stm n l => exact encrypt_stm_bufferStoreOk hm hp
  | _ => trivial

/-- The certificate relation holds at every visited non-final state of a recorded run. -/
theorem encrypt_certAt_states (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ u ∈ states, u.pc ≠ c.regs0 14 &&& ~~~1#32 →
      CertAt encryptEnv encryptCert ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u u := by
  obtain ⟨hdisj, hnowrap⟩ := encrypt_frame c hv
  have hbuffer := fun x hx => encrypt_hbuffer c hv hb s he hlr hret hrun x hx x
  intro u hu hpc
  exact recorded_self_certAt encrypt_certOk encrypt_indicesFailure_eq_none
    encrypt_certAligned encrypt_slotsCheck (by decide) hdisj (by decide) hv.base4 hnowrap hlr
    hrun hbuffer (encrypt_entry_reachable hv he hv he rfl) hu hpc

/-- **Every state of AEAD encryption keeps SP in the stack window.** -/
theorem _root_.M0Crypto.Release.Aead.encrypt_stack : TraceSpec.AeadEncryptStack := by
  intro c s ⟨hv, hb, he, hlr, hret⟩
  replace hret := Region.ne hret
  obtain ⟨n, hcorrect⟩ := encrypt_correct c s ⟨hv, hb, he, hlr, Region.not hret⟩
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, ?_⟩
  intro u hu
  by_cases hpc : u.pc = c.regs0 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hw⟩ := encrypt_final_stack_window c hv hb s he hlr hret hrun
    have := Release.runStates_stop_last hrun u hu hpc
    rw [hlast] at this
    cases this
    simpa [encryptEnv, M0Crypto.Release.TraceSpec.aeadStackBytes] using hw
  · have hself := encrypt_certAt_states c hv hb s he hlr hret hrun u hu hpc
    obtain ⟨b, off, st, code, hm, hp, hnil, hlow⟩ := hself
    cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      obtain ⟨out, hx⟩ := certPoint_xfer encrypt_certOk hm hp
      simpa [encryptEnv, M0Crypto.Release.TraceSpec.aeadStackBytes] using (xfer_stack_window hlow hx).1

end M0Crypto.Release.ConstantTime
