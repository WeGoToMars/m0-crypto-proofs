import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.AeadDecryptEntry
import M0Crypto.Release.ConstantTime.AeadEncryptEntry
import M0Crypto.Release.ConstantTime.ChaCha20Entry

/-!
Entry soundness of the ChaCha20 and AEAD certificates.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State read32)
open M0Crypto.Artifacts
open M0Crypto.Thumb (CodeAt)

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
