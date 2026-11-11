import M0Crypto.Release.AeadReadSites
import M0Crypto.Release.AeadStoreSites

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read policy of the ChaCha calls inside the AEAD functions

The AEAD functions call `m0c_chacha20_xor` twice (key derivation with counter `0`, encryption with
counter `1`). `chacha20_call_rd` turns the whole-call read bound of the callee into the AEAD read
policy `RdP`, and `key_reach_r`/`crypt_reach_r` place it in the two call sites.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (PCBetween)

/-- An offset inside the ChaCha code that is a read site but not a ChaCha load site. -/
def chaSiteMismatch : Option Nat :=
  (List.range ChaCha20Policy.chaEnd).find? fun o => rdSiteB o && !decide (ChaCha20Policy.SiteOff o)

/-- Inside the ChaCha code, the read sites are the ChaCha caller-memory loads. -/
theorem rdSite_cha : ∀ o < ChaCha20Policy.chaEnd, rdSiteB o = true → ChaCha20Policy.SiteOff o := by
  intro o ho h
  have hn : chaSiteMismatch = none := by decide +kernel
  have := List.find?_eq_none.mp hn o (List.mem_range.mpr ho)
  exact Classical.byContradiction fun hc => this (by rw [h, decide_eq_false hc]; rfl)

/-- **A ChaCha call under the AEAD read policy.** -/
theorem chacha20_call_rd {Rd : Word → Prop} (xc : Ctx) (xv : Valid xc) (u : State)
    (xe : ChaCha20Setup.Entry xc u) (hlr : (xc.regs0 14).getLsbD 0 = true)
    (hstop : ¬ ChaCha20Policy.ChaPc xc.base (xc.regs0 14 &&& ~~~1#32))
    (hRd : ∀ y, TraceSpec.ChaCha20XorReadRegion xc y → Rd y) :
    ReachS xc.base (RdP xc.base Rd) u
      (fun t => t.pc = xc.regs0 14 &&& ~~~1#32 ∧ ChaCha20Xor.Result xc t) := by
  have h1 := ChaCha20Xor.xor_reach_w (Pc := ChaCha20Policy.ChaPc xc.base) xc xv (fun _ h => h) u xe hlr
  have h2 := (reachEvents_iff_reachS _ u _).mp (ChaCha20StoreEvents.xor_reach_events_rd xc xv u xe hlr)
  have h3 := ReachS.and_stop (stop := xc.regs0 14 &&& ~~~1#32)
    (P1 := RegionWrites (ChaCha20Policy.ChaPc xc.base) (ChaCha20Xor.WrOk xc))
    (fun x e h hpc => hstop (hpc ▸ h.1)) h1 h2
  refine h3.mono (fun x e h => ?_) (fun t h => h)
  rintro ⟨o, ho, hpc⟩ y ⟨a, ha, hk, k, hk', rfl⟩
  obtain ⟨off, h1', h2', hpc'⟩ := h.1.1
  have hce : ChaCha20Policy.chaEnd ≤ 2 ^ 32 := by decide +kernel
  have hoff : off = o := pc_inj (by omega) (rdSiteB_lt ho) (hpc'.symm.trans hpc)
  subst hoff
  have hsite : ChaCha20Policy.SitePC xc.base e.pc := ⟨off, rdSite_cha off h2' ho, hpc'⟩
  have := ((h.2 a ha k hk').2 hk hsite)
  exact hRd _ this

/-- Containment of a ChaCha callee's readable bytes in the AEAD's. -/
theorem chaRd_enc (c : ACall) (xc : Ctx) (hsp : xc.sp0 = c.A) (hbase : xc.base = c.base)
    (hkey : xc.key = c.key) (hnon : xc.nonce = c.nonce)
    (hin : ∀ o < xc.len.toNat, TraceSpec.AeadEncryptReadRegion c (xc.inp + BitVec.ofNat 32 o)) {Rd : Word → Prop}
    (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) (y : Word) (h : TraceSpec.ChaCha20XorReadRegion xc y) : Rd y := by
  apply hsub
  rcases h with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · exact hin o ho
  · rw [hkey]; exact .key ho rfl
  · rw [hnon]; exact .nonce ho rfl
  · rw [hbase]; exact .code ho rfl
  · refine .stack (o := o) ?_ ?_
    · have := ChaCha20Layout.chStackBytes_eq
      simp only [TraceSpec.aeadStackBytes]; omega
    · have := ChaCha20Layout.chStackBytes_eq
      rw [hsp]
      simp only [ACall.A, TraceSpec.aeadStackBytes, this]
      bv_omega

/-- The setup key call under the read policy. -/
theorem key_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i : BitVec 25)
    (hbl : instrAt B (e + proXorOff) = some (.bl i)) (ht : blTarget (e + proXorOff) i = BitVec.ofNat 32 xorOff)
    (he : e % 2 = 0) (hex : e + copyOff ≤ Artifacts.Release.size) (p : State) (hp : ProPost c e p)
    (hpro : ¬ SiteRd c.base (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hstop : ¬ ChaCha20Policy.ChaPc c.base (c.base + BitVec.ofNat 32 (e + copyOff)))
    (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) p (XPost c e) :=
  key_reach_gen (Pn := fun pc => pc = c.base + BitVec.ofNat 32 (e + proXorOff)) c hv e i hbl ht he hex p hp rfl
    (fun x ev h => rdP_of_free (fun pc h => by subst h; exact hpro) x ev h)
    fun xc u xv xe hlr hbase hsp hout hlen hctr hretE hinp hkey hnon => by
      have hin : ∀ o < xc.len.toNat, TraceSpec.AeadEncryptReadRegion c (xc.inp + BitVec.ofNat 32 o) := by
        intro o ho
        rw [hlen] at ho
        have ho' : o < 64 := ho
        refine .stack (o := inpStackOff + o) ?_ ?_
        · simp only [inpStackOff, aeadFrame, TraceSpec.aeadStackBytes]; omega
        · rw [hinp]
          simp only [ACall.A, inpStackOff, aeadFrame, TraceSpec.aeadStackBytes]
          bv_omega
      have h := chacha20_call_rd (Rd := Rd) xc xv u xe hlr (by rw [hretE, hbase]; exact hstop)
        (chaRd_enc c xc hsp hbase hkey hnon hin hsub)
      rw [hbase] at h; exact h

/-- The encrypting ChaCha call under the read policy. -/
theorem crypt_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0)
    (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (hns : ∀ j < seqSize crypt, ¬ SiteRd c.base (c.base + BitVec.ofNat 32 (off + j)))
    (hnx : ¬ SiteRd c.base (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hret : ¬ ChaCha20Policy.ChaPc c.base (c.base + BitVec.ofNat 32 (off + cryptEnd)))
    (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) t (CryptPost c off t) :=
  crypt_reach_select_gen (Pn := fun pc => (∃ j < seqSize crypt, pc = c.base + BitVec.ofNat 32 (off + j)) ∨
      pc = c.base + BitVec.ofNat 32 (off + cryptXorOff)) c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout
    _ (fun j hj => Or.inl ⟨j, hj, rfl⟩) (Or.inr rfl)
    (fun x ev h => rdP_of_free (fun pc h' => by rcases h' with ⟨j, hj, rfl⟩ | rfl; exact hns j hj; exact hnx) x ev h)
    (fun xc u xv xe hlr hbase hout hlen hctr hsp hretE hinp hkey hnon => by
      have hin : ∀ o < xc.len.toNat, TraceSpec.AeadEncryptReadRegion c (xc.inp + BitVec.ofNat 32 o) := by
        intro o ho
        rw [hlen] at ho
        exact .inp ho (by rw [hinp])
      have h := chacha20_call_rd (Rd := Rd) xc xv u xe hlr (by rw [hretE, hbase]; exact hret)
        (chaRd_enc c xc hsp hbase hkey hnon hin hsub)
      rw [hbase] at h; exact h)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hrest => hrest)

end M0Crypto.Release.Aead
