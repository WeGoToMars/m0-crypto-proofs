import M0Crypto.Release.ConstantTime.Reach
import M0Crypto.Release.ConstantTime.Entries

/-! Relational interpretation of public entry arguments. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State read32)
open M0Crypto.Artifacts
open M0Crypto.Thumb (CodeAt)

/-- Equal public stack arguments establish the entry stack interpretation; all
other words are unconstrained. -/
theorem entryStack_sound (p : Params) (args : Nat) (s₁ s₂ : State)
    (hargs : ∀ k < args, read32 s₁.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)) =
      read32 s₂.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat))) :
    StkSem p (entryState args).stk s₁.mem s₂.mem := by
  intro o
  unfold stkGet
  cases hl : (entryState args).stk.lookup o with
  | none => simp [AbsVal.Sem]
  | some v =>
    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : (o, v) ∈ (entryState args).stk := by rw [hlist]; simp
    simp only [entryState, List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
    obtain ⟨k, hk, ho, hv⟩ := hmem
    subst v
    subst o
    simpa [hl, AbsVal.Sem] using hargs k hk

/-- The entry abstract state describes any two machines agreeing on public
register and stack arguments, SP, LR, and the loaded artifact. -/
theorem entryState_sound {p : Params} {bytes : List (BitVec 8)} {off args : Nat}
    {s₁ s₂ : State}
    (hpc₁ : s₁.pc = p.base + BitVec.ofNat 32 off) (hpc₂ : s₂.pc = s₁.pc)
    (hsp₁ : s₁.regs 13 = p.sp0) (hsp₂ : s₂.regs 13 = s₁.regs 13)
    (hpub : ∀ i, i < 4 → regAt s₁ i = regAt s₂ i)
    (hlr₁ : regAt s₁ 14 = p.lr0) (hlr₂ : regAt s₂ 14 = regAt s₁ 14)
    (hargs : ∀ k < args, read32 s₁.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)) =
      read32 s₂.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)))
    (hsize : bytes.length = p.size) (hc₁ : CodeAt s₁.mem p.base bytes)
    (hc₂ : CodeAt s₂.mem p.base bytes) :
    LowEq p bytes off (entryState args) s₁ s₂ := by
  refine ⟨hpc₁, hpc₂, ?_, hsp₂, ?_, ?_, ?_, entryStack_sound p args s₁ s₂ hargs,
    ?_, ?_, hsize, hc₁, hc₂⟩
  · simpa [entryState] using hsp₁
  · intro i hi hne
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 14 := by
      simp only [numRegs] at hi
      omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [entryState, AbsState.get, regGet, entryRegs, numRegs, AbsVal.Sem, hpub, hlr₁, hlr₂]
  · simp [entryState, AFl.all, FlagSem, AbsFlags.Sem]
  · simp [entryState, AFl.all]
  · simp [entryState]
  · simp [entryState]

/-- A related initial state is admitted by the checked certificate entry. -/
theorem certAt_initial {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hrel : LowEq p bytes entry init s₁ s₂) :
    CertAt env cert p bytes s₁ s₂ := by
  have hf := (certOk_iff env bytes entry init cert).mp hc
  unfold certFailure at hf
  cases hb : findBlk cert entry none with
  | none => simp [hb] at hf
  | some b =>
    simp only [hb] at hf
    split at hf
    · contradiction
    · rename_i hle
      have hle' : init.le b.st = true := by simpa using hle
      have hm : b ∈ cert := List.mem_of_find?_eq_some hb
      have hidx := certIndices_blockHead hi hm
      have hnext := AbsState.le_sound hle' hidx hrel
      exact certAt_resolved hc hb hm hnext

/-- The ChaCha entry contract establishes the relational entry state for two
calls with equal public inputs. -/
theorem chacha20_entry_related {c₁ c₂ : M0Crypto.Release.Frame.Ctx} {s₁ s₂ : State}
    (hv₁ : M0Crypto.Release.Frame.Valid c₁) (he₁ : M0Crypto.Release.ChaCha20Setup.Entry c₁ s₁)
    (hv₂ : M0Crypto.Release.Frame.Valid c₂) (he₂ : M0Crypto.Release.ChaCha20Setup.Entry c₂ s₂)
    (hpub : c₁.pub = c₂.pub) :
    LowEq ⟨c₁.base, c₁.sp0, c₁.regs0 14, Release.bytes.length⟩ Release.bytes
      Release.chacha20_xor (entryState chacha20ArgWords) s₁ s₂ := by
  simp only [M0Crypto.Release.Frame.Ctx.pub, Prod.mk.injEq] at hpub
  rcases hpub with ⟨hbase, hsp, hlr, hout, hin, hlen, hkey, hnonce, hctr⟩
  apply entryState_sound
  · simp [M0Crypto.Armv6M.State.pc, he₁.regs, he₁.pc, Release.chacha20_xor]
  · simp [M0Crypto.Armv6M.State.pc, he₁.regs, he₂.regs, he₁.pc, he₂.pc, hbase]
  · simp [he₁.regs, he₁.sp]
  · simp [he₁.regs, he₂.regs, he₁.sp, he₂.sp, hsp]
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [regAt, he₁.regs, he₂.regs, he₁.r0, he₂.r0, he₁.r1, he₂.r1,
        he₁.r2, he₂.r2, he₁.r3, he₂.r3, hout, hin, hlen, hkey]
  · simp [regAt, he₁.regs]
  · simp [regAt, he₁.regs, he₂.regs, hlr]
  · intro k hk
    have cases : k = 0 ∨ k = 1 := by simp [chacha20ArgWords] at hk; omega
    rcases cases with rfl | rfl
    · have hn₂ : read32 c₂.m0 c₁.sp0 = c₂.nonce := by simpa [hsp] using he₂.argN
      simpa [he₁.mem, he₂.mem, he₁.argN, hn₂] using hnonce
    · have hc₂ : read32 c₂.m0 (c₁.sp0 + 4#32) = c₂.ctr := by simpa [hsp] using he₂.argC
      simpa [he₁.mem, he₂.mem, he₁.argC, hc₂] using hctr
  · rfl
  · simpa [he₁.mem] using hv₁.code
  · simpa [he₂.mem, hbase] using hv₂.code

/-- Either AEAD entry contract establishes the relational entry state for two
calls with equal public inputs. -/
theorem aead_entry_related {c₁ c₂ : M0Crypto.Release.Aead.ACall} {s₁ s₂ : State} {off : Nat}
    (hv₁ : M0Crypto.Release.Aead.AValid c₁) (he₁ : M0Crypto.Release.Aead.AEntry c₁ off s₁)
    (hv₂ : M0Crypto.Release.Aead.AValid c₂) (he₂ : M0Crypto.Release.Aead.AEntry c₂ off s₂)
    (hpub : c₁.pub = c₂.pub) :
    LowEq ⟨c₁.base, c₁.sp0, c₁.regs0 14, Release.bytes.length⟩ Release.bytes
      off (entryState aeadArgWords) s₁ s₂ := by
  simp only [M0Crypto.Release.Aead.ACall.pub, Prod.mk.injEq] at hpub
  rcases hpub with ⟨hbase, hsp, hlr, hout, htag, hin, hlen, haad, halen, hkey, hnonce⟩
  apply entryState_sound
  · simp [M0Crypto.Armv6M.State.pc, he₁.regs, he₁.pc]
  · simp [M0Crypto.Armv6M.State.pc, he₁.regs, he₂.regs, he₁.pc, he₂.pc, hbase]
  · simp [he₁.regs, he₁.sp]
  · simp [he₁.regs, he₂.regs, he₁.sp, he₂.sp, hsp]
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [regAt, he₁.regs, he₂.regs, he₁.r0, he₂.r0, he₁.r1, he₂.r1,
        he₁.r2, he₂.r2, he₁.r3, he₂.r3, hout, htag, hin, hlen]
  · simp [regAt, he₁.regs]
  · simp [regAt, he₁.regs, he₂.regs, hlr]
  · intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by simp [aeadArgWords] at hk; omega
    rcases cases with rfl | rfl | rfl | rfl
    · have h₂ : read32 c₂.m0 c₁.sp0 = c₂.aad := by simpa [hsp] using he₂.aad
      simpa [he₁.mem, he₂.mem, he₁.aad, h₂] using haad
    · have h₂ : read32 c₂.m0 (c₁.sp0 + 4#32) = c₂.alen := by simpa [hsp] using he₂.alen
      simpa [he₁.mem, he₂.mem, he₁.alen, h₂] using halen
    · have h₂ : read32 c₂.m0 (c₁.sp0 + 8#32) = c₂.key := by simpa [hsp] using he₂.key
      simpa [he₁.mem, he₂.mem, he₁.key, h₂] using hkey
    · have h₂ : read32 c₂.m0 (c₁.sp0 + 12#32) = c₂.nonce := by simpa [hsp] using he₂.nonce
      simpa [he₁.mem, he₂.mem, he₁.nonce, h₂] using hnonce
  · rfl
  · simpa [he₁.mem] using hv₁.code
  · simpa [he₂.mem, hbase] using hv₂.code

/-- The ChaCha contract initializes the checked reachable-pair relation. -/
theorem chacha20_entry_reachable {c₁ c₂ : M0Crypto.Release.Frame.Ctx} {s₁ s₂ : State}
    (hv₁ : M0Crypto.Release.Frame.Valid c₁) (he₁ : M0Crypto.Release.ChaCha20Setup.Entry c₁ s₁)
    (hv₂ : M0Crypto.Release.Frame.Valid c₂) (he₂ : M0Crypto.Release.ChaCha20Setup.Entry c₂ s₂)
    (hpub : c₁.pub = c₂.pub) :
    CertAt chacha20Env chacha20Cert ⟨c₁.base, c₁.sp0, c₁.regs0 14, Release.bytes.length⟩
      Release.bytes s₁ s₂ :=
  certAt_initial chacha20_certOk chacha20_indicesFailure_eq_none
    (chacha20_entry_related hv₁ he₁ hv₂ he₂ hpub)

/-- The encryption contract initializes the checked reachable-pair relation. -/
theorem encrypt_entry_reachable {c₁ c₂ : M0Crypto.Release.Aead.ACall} {s₁ s₂ : State}
    (hv₁ : M0Crypto.Release.Aead.AValid c₁)
    (he₁ : M0Crypto.Release.Aead.AEntry c₁ M0Crypto.Release.Aead.encOff s₁)
    (hv₂ : M0Crypto.Release.Aead.AValid c₂)
    (he₂ : M0Crypto.Release.Aead.AEntry c₂ M0Crypto.Release.Aead.encOff s₂)
    (hpub : c₁.pub = c₂.pub) :
    CertAt encryptEnv encryptCert ⟨c₁.base, c₁.sp0, c₁.regs0 14, Release.bytes.length⟩
      Release.bytes s₁ s₂ :=
  certAt_initial encrypt_certOk encrypt_indicesFailure_eq_none
    (aead_entry_related hv₁ he₁ hv₂ he₂ hpub)

/-- The decryption contract initializes the checked reachable-pair relation. -/
theorem decrypt_entry_reachable {c₁ c₂ : M0Crypto.Release.Aead.ACall} {s₁ s₂ : State}
    (hv₁ : M0Crypto.Release.Aead.AValid c₁)
    (he₁ : M0Crypto.Release.Aead.AEntry c₁ M0Crypto.Release.Aead.decOff s₁)
    (hv₂ : M0Crypto.Release.Aead.AValid c₂)
    (he₂ : M0Crypto.Release.Aead.AEntry c₂ M0Crypto.Release.Aead.decOff s₂)
    (hpub : c₁.pub = c₂.pub) :
    CertAt decryptEnv decryptCert ⟨c₁.base, c₁.sp0, c₁.regs0 14, Release.bytes.length⟩
      Release.bytes s₁ s₂ :=
  certAt_initial decrypt_certOk decrypt_indicesFailure_eq_none
    (aead_entry_related hv₁ he₁ hv₂ he₂ hpub)

end M0Crypto.Release.ConstantTime
