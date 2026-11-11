import M0Crypto.Release.AeadPrologue
import M0Crypto.Release.ChaCha20Xor
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`AEAD_SETUP`, first call: `m0c_chacha20_xor(CTX, CTX, 64, key)` with counter 0 on the
zeroed `CTX` leaves ChaCha20 block 0 there (RFC 8439 §2.6).
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.ChaCha20 (block)

/-! ## Addresses in the stack region -/

namespace AValid
variable {c : ACall} (hv : AValid c)
include hv

theorem lo : (c.sp0 - 320#32).toNat = c.A.toNat - 176 := by
  have := hv.spLo; have := hv.A_toNat; simp [BitVec.toNat_sub]; omega

theorem A_lo : 176 ≤ c.A.toNat := by have := hv.spLo; have := hv.A_toNat; omega
theorem A_hi : c.A.toNat + 160 ≤ 2 ^ 32 := by have := hv.spHi; have := hv.A_toNat; omega

theorem sub_toNat (k : Nat) (hk : k ≤ 176) : (c.A - BitVec.ofNat 32 k).toNat = c.A.toNat - k := by
  have := hv.A_lo; simp [BitVec.toNat_sub]; omega

/-- A buffer disjoint from the region is disjoint from any part of it. -/
theorem win {a : Word} {l n : Nat} (h : Disj a l (c.sp0 - 320#32) n) (k m' : Nat) (b : Word)
    (hb : b.toNat = c.A.toNat - 176 + k) (hk : k + m' ≤ n) : Disj a l b m' :=
  disj_sub h (by rw [hb, hv.lo]; omega) (by rw [hb, hv.lo]; omega)

/-- Bytes of a buffer disjoint from the region are outside `[A, A + 144)`. -/
theorem out_hi {a : Word} {l : Nat} (h : Disj a l (c.sp0 - 320#32) 320) {i : Nat} (hi : i < l) (o : Nat)
    (ho : o < 144) : a + BitVec.ofNat 32 i ≠ c.A + BitVec.ofNat 32 o := by
  have h' := hv.win h 176 144 c.A (by have := hv.A_lo; omega) (by omega)
  exact ne_of_disj h'.1 h'.2.1 h'.2.2 hi ho

/-- Bytes of a buffer disjoint from the region are outside `SWr`. -/
theorem not_swr {a : Word} {l : Nat} (h : Disj a l (c.sp0 - 320#32) 320) {i : Nat} (hi : i < l) :
    ¬ SWr c.A (a + BitVec.ofNat 32 i) := by
  rintro ⟨o, ho, e⟩
  have h' := hv.win h 0 320 (c.A - 176#32) (by rw [hv.sub_toNat 176 (by omega)]; omega) (by omega)
  exact ne_of_disj h'.1 h'.2.1 h'.2.2 hi ho e

theorem code_not_swr {i : Nat} (hi : i < Artifacts.Release.size) : ¬ SWr c.A (c.base + BitVec.ofNat 32 i) :=
  hv.not_swr (disj_mono (hv.win hv.codeS 0 320 _ (by rw [hv.lo]; omega) (by omega)) (Nat.le_refl _)) hi

theorem codeAt_of {m : Mem} (hm : ∀ y, ¬ SWr c.A y → m y = c.m0 y) : CodeAt m c.base B := by
  intro i hi
  rw [hm _ (hv.code_not_swr (by rw [B_len] at hi; exact hi))]
  exact hv.code i hi

end AValid

theorem swr_of_hi {A y : Word} (h : ¬ SWr A y) : ∀ o < 144, y ≠ A + BitVec.ofNat 32 o :=
  fun o ho e => h (e ▸ swr_A A o ho)

theorem bytesAt_congr {m1 m2 : Mem} {a : Word} {n : Nat} (h : ∀ j < n, m1 (a + BitVec.ofNat 32 j) = m2 (a + BitVec.ofNat 32 j)) :
    Ctx.bytesAt m1 a n = Ctx.bytesAt m2 a n := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [ChaCha20Output.bytesAt_get _ _ _ _ hj, ChaCha20Output.bytesAt_get _ _ _ _ hj, h j hj]
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega), List.getElem?_eq_none (by rw [bytesAt_length]; omega)]

theorem add_toNat_sub (a y : Word) : a + BitVec.ofNat 32 (y - a).toNat = y := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact (BitVec.add_comm _ _).trans (BitVec.sub_add_cancel _ _)

theorem sub_off (a : Word) (j : Nat) (hj : j < 2 ^ 32) : (a + BitVec.ofNat 32 j - a).toNat = j := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

/-! ## Block 0 -/

/-- Key and nonce bytes as the caller passed them. -/
def ACall.keyB (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte := Ctx.bytesAt c.m0 c.key 32
def ACall.nonceB (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte := Ctx.bytesAt c.m0 c.nonce 12

/-- ChaCha20 of 64 zero bytes at counter 0 is block 0. -/
theorem chacha20_zero (key nonce msg : List M0Crypto.Spec.ChaCha20.Byte) (hl : msg.length = 64)
    (hz : ∀ j (h : j < 64), msg[j] = 0#8) (j : Nat) (hj : j < 64) :
    (M0Crypto.Spec.Aead.chacha20 key 0 nonce msg)[j]! = (block key 0#32 nonce)[j]! := by
  have h := ChaCha20Spec.chacha20_get key nonce msg 0 j (by omega)
  rw [List.getElem!_eq_getElem?_getD, h, hz j hj, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [ChaCha20Spec.block_length']; omega)]
  simp only [Option.getD_some, BitVec.zero_xor, show 0 + j / 64 = 0 by omega, show j % 64 = j by omega]

/-- State after the block-0 call returns, at `e + copyOff`. -/
structure XPost (c : ACall) (e : Nat) (u : State) : Prop where
  pc : u.pc = c.base + BitVec.ofNat 32 (e + copyOff)
  sp : u.regs 13 = c.A
  hi : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = c.regs0 r
  ctx : ∀ j < 64, u.mem (c.A + BitVec.ofNat 32 (8 + j)) = (block c.keyB 0#32 c.nonceB)[j]!
  nonce : read32 u.mem c.A = c.nonce
  high : Hi c u.mem
  out : ∀ y, ¬ SWr c.A y → u.mem y = c.m0 y

theorem key_reach (c : ACall) (hv : AValid c) (e : Nat) (i : BitVec 25)
    (hbl : instrAt B (e + proXorOff) = some (.bl i)) (ht : blTarget (e + proXorOff) i = BitVec.ofNat 32 xorOff)
    (he : e % 2 = 0) (hex : e + copyOff ≤ Artifacts.Release.size) (p : State) (hp : ProPost c e p) :
    Reach c.base (SWr c.A) p (XPost c e) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hret : e + proXorOff + 4 = e + copyOff := by have := proXorOff_ret; omega
  apply Reach.bl hb2 (e + proXorOff) xorOff i hp.pc (by have := proXorOff_even; omega) hbl
    (by have := proXorOff_ret; omega) ht
  generalize hu : (p.setReg 14 ((c.base + BitVec.ofNat 32 (e + proXorOff + 4)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 xorOff) = u
  have ur : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → u.regs r = p.regs r := fun r a b => by
    rw [← hu, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have um : u.mem = p.mem := by rw [← hu]; rfl
  have u14 : u.regs 14 = (c.base + BitVec.ofNat 32 (e + proXorOff + 4)) ||| 1#32 := by
    rw [← hu, setReg_ne _ _ _ _ (by decide), setReg_eq]
  have u15 : u.regs 15 = c.base := by rw [← hu, setReg_eq]; simp [xorOff_base]
  have hA := hv.A_lo
  have hA' := hv.A_hi
  have hk : ∀ j < 32, p.mem (c.key + BitVec.ofNat 32 j) = c.m0 (c.key + BitVec.ofNat 32 j) :=
    fun j hj => hp.out _ (fun o ho => hv.out_hi hv.keyS hj o ho)
  have hn : ∀ j < 12, p.mem (c.nonce + BitVec.ofNat 32 j) = c.m0 (c.nonce + BitVec.ofNat 32 j) :=
    fun j hj => hp.out _ (fun o ho => hv.out_hi hv.nonceS hj o ho)
  let xc : Ctx := { base := c.base, sp0 := c.A, out := c.A + 8#32, inp := c.A + 8#32, len := 64#32,
                    key := c.key, nonce := c.nonce, ctr := 0#32, m0 := u.mem, regs0 := u.regs }
  have fp_toNat : (c.A - BitVec.ofNat 32 176).toNat = c.A.toNat - 176 := hv.sub_toNat 176 (Nat.le_refl _)
  have c8 : (c.A + 8#32).toNat = c.A.toNat + 8 := hv.A_off 8 (by decide)
  have xv : Valid xc := {
    base4 := hv.base4
    sp8 := by show c.A.toNat % 8 = 0; rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    spLo := hA
    codeF := hv.win (disj_mono hv.codeS (Nat.le_refl _)) 0 184 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega)
      (by omega)
    codeO := by
      show Disj c.base Artifacts.Release.size (c.A + 8#32) (64#32 : Word).toNat
      exact hv.win hv.codeS 184 64 _ (by omega) (by decide)
    outF := by
      show Disj (c.A + 8#32) (64#32 : Word).toNat (c.A - BitVec.ofNat 32 176) 184
      refine ⟨?_, ?_, .inr ?_⟩ <;> simp only [c8, fp_toNat, BitVec.toNat_ofNat] <;> omega
    inF := by
      show Disj (c.A + 8#32) (64#32 : Word).toNat (c.A - BitVec.ofNat 32 176) 176
      refine ⟨?_, ?_, .inr ?_⟩ <;> simp only [c8, fp_toNat, BitVec.toNat_ofNat] <;> omega
    inOut := .inl rfl
    keyF := hv.win hv.keyS 0 176 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    nonceF := hv.win hv.nonceS 0 176 _ (by show (c.A - BitVec.ofNat 32 176).toNat = _; omega) (by omega)
    code := by
      show CodeAt u.mem c.base B
      rw [um]; exact hv.codeAt_of (fun y hy => hp.out y (swr_of_hi hy)) }
  have xe : ChaCha20Setup.Entry xc u := {
    regs := rfl, mem := rfl, pc := u15
    sp := by show u.regs 13 = c.A; rw [ur 13 (by decide) (by decide), hp.sp]
    r0 := by show u.regs 0 = _; rw [ur 0 (by decide) (by decide), hp.r0]
    r1 := by show u.regs 1 = _; rw [ur 1 (by decide) (by decide), hp.r1]
    r2 := by show u.regs 2 = _; rw [ur 2 (by decide) (by decide), hp.r2]
    r3 := by show u.regs 3 = _; rw [ur 3 (by decide) (by decide), hp.r3]
    argN := by show read32 u.mem c.A = _; rw [um, hp.nonce]
    argC := by show read32 u.mem (c.A + 4#32) = _; rw [um, hp.ctr] }
  have hlr : (xc.regs0 14).getLsbD 0 = true := by show (u.regs 14).getLsbD 0 = true; rw [u14]; exact lr_odd _
  have wr : ∀ y, ChaCha20Xor.WrOk xc y → SWr c.A y := by
    rintro y (⟨o, ho, rfl⟩ | ⟨_, hy⟩)
    · exact swr_lo c.A o ho
    · have hy' : (y - (c.A + 8#32)).toNat < 64 := hy
      have e1 : c.A + BitVec.ofNat 32 (8 + (y - (c.A + 8#32)).toNat) = y := by
        rw [← ofNat_add_assoc]; exact add_toNat_sub _ _
      rw [← e1]; exact swr_A _ _ (by omega)
  apply ((ChaCha20Xor.xor_reach xc xv u xe hlr).monoW wr).mono
  rintro t ⟨tpc, hr⟩
  have hok : M0Crypto.Spec.Aead.counterOk xc.ctr.toNat xc.len.toNat = true := by
    show M0Crypto.Spec.Aead.counterOk (0#32 : Word).toNat (64#32 : Word).toNat = true; decide
  -- the window `[A, A + 160)` is outside the callee frame
  have sSB := ChaCha20Layout.chStackBytes_eq
  have hiS : ∀ o' < 160, ChaCha20Xor.OutS xc (c.A + BitVec.ofNat 32 o') := fun o' ho' o ho =>
    ne_of_disj (b := c.A - BitVec.ofNat 32 176) (by omega) (by rw [fp_toNat]; omega)
      (.inr (by rw [fp_toNat]; omega)) ho' ho
  have tm : ∀ y, ChaCha20Xor.OutS xc y → (∀ j < 64, y ≠ c.A + BitVec.ofNat 32 (8 + j)) → t.mem y = p.mem y := by
    intro y hy hj
    rw [hr.mem y hy, if_neg]
    · exact congrFun um y
    rintro ⟨-, hlt⟩
    have e1 : c.A + BitVec.ofNat 32 (8 + (y - (c.A + 8#32)).toNat) = y := by
      rw [← ofNat_add_assoc]; exact add_toNat_sub _ _
    exact hj _ hlt e1.symm
  have tw : ∀ o, 104 ≤ o → o < 160 → t.mem (c.A + BitVec.ofNat 32 o) = p.mem (c.A + BitVec.ofNat 32 o) :=
    fun o h1 h2 => tm _ (hiS o h2) (fun j hj => off_ne _ (by omega) (by omega) (by omega))
  refine ⟨?_, hr.sp, ?_, ?_, ?_, hp.high.congr tw, ?_⟩
  · rw [tpc]; show u.regs 14 &&& ~~~1#32 = _
    rw [u14, lr_mask _ (even_off c.base hv.base4 (e + proXorOff + 4) (by have := proXorOff_even; omega)), hret]
  · intro r a b
    rw [hr.callee r a b]; show u.regs r = _
    rw [ur r (by omega) (by omega), hp.hi r a (by omega) (by omega)]
  · intro j hj
    have ho : (c.A + BitVec.ofNat 32 (8 + j) - xc.out).toNat = j := by
      show (c.A + BitVec.ofNat 32 (8 + j) - (c.A + 8#32)).toNat = j
      rw [← ofNat_add_assoc]; exact sub_off _ _ (by omega)
    rw [hr.mem _ (hiS _ (by omega)), Ctx.oidx, ho, if_pos ⟨hok, by show j < (64#32 : Word).toNat; simp; omega⟩]
    show (M0Crypto.Spec.Aead.chacha20 xc.keyB (0#32 : Word).toNat xc.nonceB xc.msg)[j]! = _
    have kB : xc.keyB = c.keyB := bytesAt_congr (fun j hj => by show u.mem _ = _; rw [um]; exact hk j hj)
    have nB : xc.nonceB = c.nonceB := bytesAt_congr (fun j hj => by show u.mem _ = _; rw [um]; exact hn j hj)
    rw [kB, nB]
    apply chacha20_zero _ _ _ (bytesAt_length _ _ _) _ j hj
    intro i hi
    have := ChaCha20Output.bytesAt_get u.mem (c.A + 8#32) 64 i hi
    rw [List.getElem?_eq_getElem (by rw [bytesAt_length]; exact hi)] at this
    have e := Option.some.inj this
    show (Ctx.bytesAt u.mem (c.A + 8#32) (64#32 : Word).toNat)[i] = _
    simp only [show (64#32 : Word).toNat = 64 from rfl]
    rw [e, um, ofNat_add_assoc]; exact hp.ctx i hi
  · rw [← hp.nonce]
    apply read32_congr
    intro k hk
    exact tm _ (hiS k (by omega)) (fun j hj => off_ne _ (by omega) (by omega) (by omega))
  · intro y hy
    rw [tm y (fun o ho e => hy (e ▸ swr_lo c.A o ho)) (fun j hj e => hy (e ▸ swr_A c.A _ (by omega))),
      hp.out y (swr_of_hi hy)]

end M0Crypto.Release.Aead
