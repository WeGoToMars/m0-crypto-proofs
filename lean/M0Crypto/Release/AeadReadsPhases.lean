import M0Crypto.Release.AeadChaCha20CallReads
import M0Crypto.Release.AeadMacReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read-policy phases of the AEAD functions

Phases without a caller-memory load reuse the region-generic `_w` lemmas with the step condition
"not a read site"; phases with one use the `_r` variants, which carry the read policy.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ConstantTime (PCBetween)
open M0Crypto.Spec.Aead (pad16 macData chacha20)

/-- An interval with no read site is a region of site-free program counters. -/
theorem region_ns {base : Word} {off n : Nat} (h : firstReadSite off n = none)
    (hle : off + n ≤ 2 ^ 32) : InRegion (NoSite base) base off n := fun j hj =>
  not_siteRd (by omega) (no_readSite h j hj)

theorem pt_ns {base : Word} {off : Nat} (h : rdSiteB off = false) (hle : off < 2 ^ 32) :
    NoSite base (base + BitVec.ofNat 32 off) := not_siteRd hle h

theorem initPc_ns (base : Word) : ∀ pc, Poly1305Init.InitPc base pc → NoSite base pc := by
  rintro pc ⟨o, h1, h2, rfl⟩
  have hf : firstReadSite Poly1305Init.entryAt (Poly1305Init.popAt + 2 - Poly1305Init.entryAt) = none := by
    decide +kernel
  have := no_readSite hf (o - Poly1305Init.entryAt) (by omega)
  rw [Nat.add_sub_cancel' h1] at this
  exact not_siteRd (by have : Poly1305Init.popAt + 2 < 2 ^ 32 := by decide
                       omega) this

theorem finPc_ns (base : Word) : ∀ pc, Poly1305Finish.FinPc base pc → NoSite base pc := by
  rintro pc ⟨o, h1, h2, rfl⟩
  have hf : firstReadSite Poly1305Finish.entryAt (Poly1305Finish.popAt + 2 - Poly1305Finish.entryAt) = none := by
    decide +kernel
  have := no_readSite hf (o - Poly1305Finish.entryAt) (by omega)
  rw [Nat.add_sub_cancel' h1] at this
  exact not_siteRd (by have : Poly1305Finish.popAt + 2 < 2 ^ 32 := by decide
                       omega) this

/-- The 16-byte Poly1305 block at `A + 72` lies in the readable stack window. -/
theorem rd_blk {Rd : Word → Prop} (c : ACall) (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) :
    ∀ o < 16, Rd (c.A + 72#32 + BitVec.ofNat 32 o) := fun o ho =>
  hsub _ (.stack (o := blkStackOff + o) (by simp only [blkStackOff, aeadFrame, TraceSpec.aeadStackBytes]; omega) (by
    simp only [ACall.A, blkStackOff, aeadFrame, TraceSpec.aeadStackBytes]; bv_omega))

/-- Loads and one complete padded-message MAC, under the read policy. -/
theorem mac_phase_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (Wr : Word → Prop) (off : Nat) (is : List Instr)
    (u v : BitVec 8) (his : is = [.ldrSp 4 u, .ldrSp 5 v])
    (hseq : seqAt B off is = true) (i1 i2 : BitVec 25) (hat : MacAt (off + seqSize is) i1 i2)
    (ho : off % 2 = 0) (hx : off + seqSize is + macSize ≤ Artifacts.Release.size) (s : State) (hp : s.pc = c.base + BitVec.ofNat 32 off)
    (d n : Word) (hd : Disj d n.toNat (c.sp0-320#32) 320)
    (hloadD : read32 s.mem (c.A + BitVec.ofNat 32 (4*u.toNat)) = d)
    (hloadN : read32 s.mem (c.A + BitVec.ofNat 32 (4*v.toNat)) = n)
    (hbody : Body c Wr s) (ti : Mem) (msg : List M0Crypto.Spec.ChaCha20.Byte) (hpi : PInv c.A ti msg s.mem)
    (hw : ∀ y, MacWr c.A y → Wr y)
    (hrl : InRegion (NoSite c.base) c.base off (seqSize is)) (hfree : MacFree (off + seqSize is))
    (hR : ∀ o < n.toNat, Rd (d + BitVec.ofNat 32 o))
    (hRblk : ∀ o < 16, Rd (c.A + 72#32 + BitVec.ofNat 32 o)) :
    ReachS c.base (RdP c.base Rd) s (PhasePost c Wr (off + seqSize is + macSize) ti
      (msg ++ (Ctx.bytesAt s.mem d n.toNat ++ pad16 (Ctx.bytesAt s.mem d n.toNat))) s) := by
  have hsz : seqSize is = 4 := by subst his; exact loadPair_size u v
  apply ReachS.bind
  apply ((load_reach_w c.base c.A d n off is s hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega)
    ho hseq hp hbody.sp u v his hloadD hloadN Wr hrl).toRd (fun _ h => h)).mono (fun _ _ h => h)
  rintro t ⟨tp, t4, t5, tm, tr⟩
  have tb : Body c Wr t := ⟨by rw [tr 13 (by decide) (by decide) (by decide), hbody.sp],
    by rw [tm]; exact hbody.high, by rw [tm]; exact hbody.nonce,
    fun r a b => by rw [tr r (by omega) (by omega) (by omega), hbody.hi r a b],
    fun y hy => by rw [tm]; exact hbody.frame y hy, by rw [tm]; exact hbody.code⟩
  have he := hv.macEnv hd tb.code
  have pi : PInv c.A ti msg t.mem := by rw [tm]; exact hpi
  apply (mac_padded_r c.base c.A d n t.mem (off + seqSize is) i1 i2 hat (by omega) hx hfree hR hRblk he t tp tb.sp
    t4 t5 rfl pi.keyOk pi.bound).mono (fun _ _ h => h)
  intro z hz
  refine ⟨hz.pc, tb.mac he hz hw, ?_, fun y hy => (hz.frame y hy).trans (congrFun tm y)⟩
  have pz := pi.mac he hz
  rw [tm] at pz
  exact pz

/-- `AEAD_SETUP` under the read policy. -/
theorem aead_setup_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (e : Nat) (i0 i1 : BitVec 25)
    (hpro : seqAt B e pro = true) (hb0 : instrAt B (e + proXorOff) = some (.bl i0))
    (ht0 : blTarget (e + proXorOff) i0 = BitVec.ofNat 32 xorOff) (hcp : seqAt B (e + copyOff) copy = true)
    (hb1 : instrAt B (e + initCallOff) = some (.bl i1))
    (ht1 : blTarget (e + initCallOff) i1 = BitVec.ofNat 32 initOff)
    (he : e % 2 = 0) (hex : e + setupEnd ≤ Artifacts.Release.size) (s : State) (h : AEntry c e s)
    (hrp : InRegion (NoSite c.base) c.base e (seqSize pro))
    (hrx : NoSite c.base (c.base + BitVec.ofNat 32 (e + proXorOff)))
    (hrc : InRegion (NoSite c.base) c.base (e + copyOff) (seqSize copy))
    (hrb : NoSite c.base (c.base + BitVec.ofNat 32 (e + initCallOff)))
    (hstop : ¬ ChaCha20Policy.ChaPc c.base (c.base + BitVec.ofNat 32 (e + copyOff)))
    (hsub : ∀ y, TraceSpec.AeadEncryptReadRegion c y → Rd y) :
    ReachS c.base (RdP c.base Rd) s (fun t => ∃ ic, SetupPost c e ic t) := by
  apply ReachS.bind
  apply ((pro_reach_w (Pc := NoSite c.base) (Q := ProPost c e) c hv e hpro he s h hrp
      (fun p hp => ReachS.done hp)).toRd (fun _ h => h)).mono (fun _ _ h => h)
  intro p hp
  apply ReachS.bind
  apply (key_reach_r (Rd := Rd) c hv e i0 hb0 ht0 he
      (by have := copyOff_end; have := initCallOff_ret; omega) p hp hrx hstop hsub).mono (fun _ _ h => h)
  intro u hu
  exact (setup_reach_w (Pc := NoSite c.base) c hv e i1 hcp hb1 ht1 he hex u hu hrc hrb (initPc_ns c.base)).toRd
    (fun _ h => h)

end M0Crypto.Release.Aead
