import M0Crypto.Release.ReachInv
import M0Crypto.Release.ChaCha20StoreEvents
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.ConstantTime.ExactStoreSites

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Store-site policy of the AEAD run

The AEAD certificates track the stores of the ChaCha callee that write the output buffer only in
the call that encrypts (counter word `1`); in the setup call (counter word `0`) the same
instructions write the stack and the certificate tracks them. A pc-only policy cannot tell the two
calls apart, so the policy here is on the pre-state: the counter word at `A + 4`.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (OutputStorePC outputStoreOffset PCBetween)
open M0Crypto.Release.ChaCha20Output M0Crypto.Release.ChaCha20Layout

/-- The ChaCha callee run, with its accesses obeying both the frame/output write bound and the
output-store-instruction bound, for any larger set of program counters. -/
theorem chacha20_call_pol {Pc : Word → Prop} (xc : Ctx) (xv : Valid xc) (u : State)
    (xe : ChaCha20Setup.Entry xc u) (hlr : (xc.regs0 14).getLsbD 0 = true)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc xc.base pc → Pc pc)
    (hstop : ¬ ChaCha20Policy.ChaPc xc.base (xc.regs0 14 &&& ~~~1#32)) :
    ReachS xc.base (fun x e => RegionWrites Pc (ChaCha20Xor.WrOk xc) x e ∧
        ∀ y, Writes e.accesses y → (OutputStorePC xc.base e.pc → xc.oidx y < xc.len.toNat))
      u (fun t => t.pc = xc.regs0 14 &&& ~~~1#32 ∧ ChaCha20Xor.Result xc t) := by
  have h1 := ChaCha20Xor.xor_reach_w (Pc := ChaCha20Policy.ChaPc xc.base) xc xv (fun _ h => h) u xe hlr
  have h2 := (reachEvents_iff_reachS _ u _).mp (ChaCha20StoreEvents.xor_reach_events xc xv u xe hlr)
  have h3 := ReachS.and_stop (stop := xc.regs0 14 &&& ~~~1#32)
    (P1 := RegionWrites (ChaCha20Policy.ChaPc xc.base) (ChaCha20Xor.WrOk xc))
    (fun x e h hpc => hstop (hpc ▸ h.1)) h1 h2
  refine h3.mono (fun x e h => ⟨⟨hPc _ h.1.1, h.1.2⟩, ?_⟩) (fun t h => h)
  rintro y ⟨a, ha, hk, k, hk', rfl⟩
  have := h.2 a ha k hk'
  rw [hk] at this
  rcases this with h | ⟨-, h⟩
  · cases h
  · exact h

/-- The output-store policy of a pre-state: while the counter word of the ChaCha argument slot is
`1` (the encrypting call), a store at one of the output-store instructions writes the output. -/
def CPol (c : ACall) (x : State) (e : Event) : Prop :=
  OutputStorePC c.base e.pc → read32 x.mem (c.A + 4#32) = 1#32 → ∀ y, Writes e.accesses y → OutR c y

/-- Region, write bound and output-store policy. -/
def PolW (c : ACall) (Pc Wr : Word → Prop) (x : State) (e : Event) : Prop :=
  RegionWrites Pc Wr x e ∧ CPol c x e

/-- A region free of output-store instructions satisfies the policy trivially. -/
theorem polW_of_free {c : ACall} {Pn Pc Wr Wr' : Word → Prop}
    (hs : ∀ pc, Pn pc → ¬ OutputStorePC c.base pc) (hPc : ∀ pc, Pn pc → Pc pc)
    (hw : ∀ y, Wr y → Wr' y) (x : State) (e : Event) (h : RegionWrites Pn Wr x e) :
    PolW c Pc Wr' x e :=
  ⟨⟨hPc _ h.1, fun y hy => hw y (h.2 y hy)⟩, fun hsite => absurd hsite (hs _ h.1)⟩

theorem ReachW.toPol {c : ACall} {Pn Pc Wr Wr' : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW c.base Pn Wr s Q)
    (hs : ∀ pc, Pn pc → ¬ OutputStorePC c.base pc) (hPc : ∀ pc, Pn pc → Pc pc)
    (hw : ∀ y, Wr y → Wr' y) : ReachS c.base (PolW c Pc Wr') s Q :=
  h.mono (polW_of_free hs hPc hw) (fun _ h => h)

/-- No byte of the argument slot holding the ChaCha counter is writable by the setup call. -/
theorem slot_not_wrok (c : ACall) (hv : AValid c) (xc : Ctx) (hsp : xc.sp0 = c.A)
    (hout : xc.out = c.A + 8#32) (hlen : xc.len = 64#32) {k : Nat} (hk : k < 4) :
    ¬ ChaCha20Xor.WrOk xc (c.A + 4#32 + BitVec.ofNat 32 k) := by
  have hA := hv.A_lo
  have hA' := hv.A_hi
  have sb := ChaCha20Layout.chStackBytes_eq
  rintro (⟨o, ho, h⟩ | ⟨_, h⟩)
  · simp only [Ctx.fp, hsp, sb] at h
    rw [sb] at ho
    bv_omega
  · simp only [Ctx.oidx, hout, hlen] at h
    bv_omega

theorem wrOk_swr_key (c : ACall) (xc : Ctx) (hsp : xc.sp0 = c.A) (hout : xc.out = c.A + 8#32)
    (hlen : xc.len = 64#32) {y : Word} (h : ChaCha20Xor.WrOk xc y) : SWr c.A y := by
  rcases h with ⟨o, ho, rfl⟩ | ⟨_, hy⟩
  · have : xc.fp = c.A - BitVec.ofNat 32 176 := by simp [Ctx.fp, hsp, ChaCha20Layout.chStackBytes_eq]
    rw [this]; exact swr_lo c.A o ho
  · have hy' : (y - (c.A + 8#32)).toNat < 64 := by
      have := hy; simp only [Ctx.oidx, hout, hlen] at this; exact this
    have e1 : c.A + BitVec.ofNat 32 (8 + (y - (c.A + 8#32)).toNat) = y := by
      rw [← ofNat_add_assoc]; exact add_toNat_sub _ _
    rw [← e1]; exact swr_A _ _ (by omega)

/-- The setup call: the same call as `key_reach_w`, with the output-store policy. During it the
counter word is `0`, so the policy is vacuous at the output-store instructions it runs. -/
theorem key_reach_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i : BitVec 25)
    (hbl : instrAt B (e + proXorOff) = some (.bl i)) (ht : blTarget (e + proXorOff) i = BitVec.ofNat 32 xorOff)
    (he : e % 2 = 0) (hex : e + copyOff ≤ Artifacts.Release.size) (p : State) (hp : ProPost c e p)
    (hpro : Pc (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hns : ¬ OutputStorePC c.base (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) :
    ReachS c.base (PolW c Pc (SWr c.A)) p (XPost c e) :=
  key_reach_gen (Pn := fun pc => pc = c.base + BitVec.ofNat 32 (e + proXorOff)) c hv e i hbl ht he hex p hp rfl
    (fun x ev h => polW_of_free (Pc := Pc) (Wr' := SWr c.A) (fun pc h => by subst h; exact hns)
      (fun pc h => by subst h; exact hpro) (fun _ h => h) x ev h)
    fun xc u xv xe hlr hbase hsp hout hlen hctr _ _ _ _ => by
      have h1 := ChaCha20Xor.xor_reach_w (Pc := ChaCha20Policy.ChaPc xc.base) xc xv (fun _ h => h) u xe hlr
      have h0 : read32 u.mem (c.A + 4#32) = 0#32 := by
        have := xe.argC
        rw [← xe.mem, hsp, hctr] at this
        exact this
      have h2 := h1.add_read32 (c.A + 4#32) 0#32
        (fun x ev hx k hk hw => slot_not_wrok c hv xc hsp hout hlen hk (hx.2 _ hw)) h0
      rw [hbase] at h2
      refine h2.mono (fun x ev hx => ?_) (fun _ h => h)
      refine ⟨⟨hPc _ (hbase ▸ hx.1.1), fun y hy => wrOk_swr_key c xc hsp hout hlen (hx.1.2 y hy)⟩, ?_⟩
      intro _ hctr' _ _
      rw [hx.2] at hctr'
      exact absurd hctr' (by decide)

theorem not_pcBetween {base : Word} {lo hi o : Nat} (ho : o < 2 ^ 32) (hhi : hi ≤ 2 ^ 32)
    (h : o < lo ∨ hi ≤ o) : ¬ M0Crypto.Release.ConstantTime.PCBetween base lo hi (base + BitVec.ofNat 32 o) := by
  rintro ⟨q, h1, h2, e⟩
  have e' := congrArg (· - base) e
  simp only [BitVec.add_comm base, BitVec.add_sub_cancel] at e'
  have := congrArg BitVec.toNat e'
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem not_outputStorePC {base : Word} {o : Nat} (ho : o < 2 ^ 32)
    (h : outputStoreOffset o = false) :
    ¬ OutputStorePC base (base + BitVec.ofNat 32 o) := by
  intro hs
  have hk : ∀ x : Nat, x < 2 ^ 32 → base + BitVec.ofNat 32 o = base + BitVec.ofNat 32 x → o = x := by
    intro x hx e
    have e' := congrArg (· - base) e
    simp only [BitVec.add_comm base, BitVec.add_sub_cancel] at e'
    have := congrArg BitVec.toNat e'
    simp only [BitVec.toNat_ofNat] at this
    omega
  rcases hs with ⟨i, hi, e⟩ | e
  · have hx : achOff + achSize * i + seqSize (ach i).dropLast < 2 ^ 32 := by
      have key : ∀ i, i < 16 → achOff + achSize * i + seqSize (ach i).dropLast < 2 ^ 32 := by
        decide +kernel
      exact key i hi
    have := hk _ hx e
    simp only [outputStoreOffset, Bool.or_eq_false_iff, List.any_eq_false,
      List.mem_range, decide_eq_false_iff_not] at h
    exact h.1 i hi (by simpa using this)
  · have := hk _ (by decide) e
    simp only [outputStoreOffset, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    exact h.2 this

theorem PolW.monoW {c : ACall} {Pc Wr Wr' : Word → Prop} (hw : ∀ y, Wr y → Wr' y) {x : State}
    {e : Event} (h : PolW c Pc Wr x e) : PolW c Pc Wr' x e :=
  ⟨⟨h.1.1, fun y hy => hw y (h.1.2 y hy)⟩, h.2⟩

/-- The encrypting call: ChaCha with counter word `1` and its output stores. -/
theorem crypt_reach_p {Pc : Word → Prop} (c : ACall) (hv : AValid c) (hb : ABuf c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off crypt = true) (hbl : instrAt B (off + cryptXorOff) = some (.bl i))
    (ht : blTarget (off + cryptXorOff) i = BitVec.ofNat 32 xorOff) (ho : off % 2 = 0)
    (hox : off + cryptEnd ≤ Artifacts.Release.size)
    (t : State) (tpc : t.pc = c.base + BitVec.ofNat 32 off) (t13 : t.regs 13 = c.A) (thi : Hi c t.mem)
    (tn : read32 t.mem c.A = c.nonce) (tout : ∀ y, ¬ SWr c.A y → t.mem y = c.m0 y)
    (hrc : InRegion Pc c.base off (seqSize crypt))
    (hrx : Pc (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hns : ∀ j < seqSize crypt, ¬ OutputStorePC c.base (c.base + BitVec.ofNat 32 (off + j)))
    (hnx : ¬ OutputStorePC c.base (c.base + BitVec.ofNat 32 (off + cryptXorOff)))
    (hret : ¬ ChaCha20Policy.ChaPc c.base (c.base + BitVec.ofNat 32 (off + cryptEnd)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) :
    ReachS c.base (PolW c Pc (CryptWr c)) t (CryptPost c off t) :=
  crypt_reach_select_gen (Pn := fun pc => (∃ j < seqSize crypt, pc = c.base + BitVec.ofNat 32 (off + j)) ∨
      pc = c.base + BitVec.ofNat 32 (off + cryptXorOff)) c hv hb off i hseq hbl ht ho hox t tpc t13 thi tn tout
    _ (fun j hj => Or.inl ⟨j, hj, rfl⟩) (Or.inr rfl)
    (fun x ev h => polW_of_free (Pc := Pc) (Wr' := CryptWr c)
      (fun pc h' => by rcases h' with ⟨j, hj, rfl⟩ | rfl; exact hns j hj; exact hnx)
      (fun pc h' => by rcases h' with ⟨j, hj, rfl⟩ | rfl; exact hrc j hj; exact hrx)
      (fun _ h => h) x ev h)
    (fun xc u xv xe hlr hbase hout hlen hctr hsp hretE _ _ _ => by
      have h1 := chacha20_call_pol (Pc := Pc) xc xv u xe hlr (fun pc h => hPc pc (hbase ▸ h))
        (by rw [hretE, hbase]; exact hret)
      rw [hbase] at h1
      refine h1.mono (fun x ev hx => ?_) (fun _ h => h)
      have hO : ∀ y, xc.oidx y < xc.len.toNat → OutR c y := fun y hy => by
        simpa only [Ctx.oidx, OutR, hout, hlen] using hy
      refine ⟨⟨hx.1.1, fun y hy => ?_⟩, fun hs _ y hy => hO y (hx.2 y hy hs)⟩
      rcases hx.1.2 y hy with ⟨o, ho, rfl⟩ | ⟨_, hy'⟩
      · have : xc.fp = c.A - BitVec.ofNat 32 176 := by simp [Ctx.fp, hsp, ChaCha20Layout.chStackBytes_eq]
        rw [this]; exact .inl (swr_lo c.A o ho)
      · exact .inr (hO y hy'))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hrest => hrest)

theorem noSite_between {base : Word} {lo hi : Nat} (hh : hi ≤ 2 ^ 32)
    (h : ∀ o, lo ≤ o → o < hi → outputStoreOffset o = false) :
    ∀ pc, PCBetween base lo hi pc → ¬ OutputStorePC base pc := by
  rintro pc ⟨o, h1, h2, rfl⟩
  exact not_outputStorePC (by omega) (h o h1 h2)

/-- `AEAD_SETUP` under the output-store policy: only the ChaCha key call runs output-store
instructions, and with counter word `0`. -/
theorem aead_setup_p {Pc Pn : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i0 i1 : BitVec 25)
    (hpro : seqAt B e pro = true) (hb0 : instrAt B (e + proXorOff) = some (.bl i0))
    (ht0 : blTarget (e + proXorOff) i0 = BitVec.ofNat 32 xorOff) (hcp : seqAt B (e + copyOff) copy = true)
    (hb1 : instrAt B (e + initCallOff) = some (.bl i1))
    (ht1 : blTarget (e + initCallOff) i1 = BitVec.ofNat 32 initOff)
    (he : e % 2 = 0) (hex : e + setupEnd ≤ Artifacts.Release.size) (s : State) (h : AEntry c e s)
    (hfree : ∀ pc, Pn pc → ¬ OutputStorePC c.base pc) (hPn : ∀ pc, Pn pc → Pc pc)
    (hrp : InRegion Pn c.base e (seqSize pro))
    (hrx : Pc (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hnx : ¬ OutputStorePC c.base (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hrc : InRegion Pn c.base (e + copyOff) (seqSize copy))
    (hrb : Pn (c.base + BitVec.ofNat 32 (e + initCallOff)))
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (hPi : ∀ pc, Poly1305Init.InitPc c.base pc → Pn pc) :
    ReachS c.base (PolW c Pc (SWr c.A)) s (fun t => ∃ ic, SetupPost c e ic t) := by
  apply ReachS.bind
  apply (ReachW.toPol (pro_reach_w (Pc := Pn) (Q := ProPost c e) c hv e hpro he s h hrp
      (fun p hp => ReachS.done hp)) hfree hPn (fun _ h => h)).mono (fun _ _ h => h)
  intro p hp
  apply ReachS.bind
  apply (key_reach_p (Pc := Pc) c hv e i0 hb0 ht0 he
      (by have := copyOff_end; have := initCallOff_ret; omega) p hp hrx hnx hPc).mono (fun _ _ h => h)
  intro u hu
  exact ReachW.toPol (setup_reach_w (Pc := Pn) c hv e i1 hcp hb1 ht1 he hex u hu hrc hrb hPi) hfree hPn (fun _ h => h)

end M0Crypto.Release.Aead
