import M0Crypto.Release.AeadLoop
import M0Crypto.Release.ReachSteps
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`MAC_PADDED` in full. `mac_tail` runs offsets `m + macCOff` to `m + macSize` (the partial
final block, zero-padded in `BLK`); `mac_padded` composes it with `mac_head`. The
result is RFC 8439's `msg ++ pad16 msg` absorbed with pad 1.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK wordAt)
open M0Crypto.Spec.Aead (p pad16)
open M0Crypto.Spec.ChaCha20 (Byte)

/-! ## Word facts -/

theorem and15 (n : Word) : 15#32 &&& n = BitVec.ofNat 32 (n.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n.toNat % 16 < 2 ^ 32), show 15 % 2 ^ 32 = 2 ^ 4 - 1 from rfl, Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod n.toNat 4

theorem shl_shr (n : Word) : (n >>> 4) <<< 4 = BitVec.ofNat 32 (16 * (n.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have h := n.isLt
  rw [BitVec.toNat_shiftLeft, lsr4, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : n.toNat / 16 * 2 ^ 4 < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## SP-relative writes inside a sub-window -/

theorem traceAll_writes_sp' (P : Nat → Prop) : ∀ (is : List Instr) (s : State),
    SpBlock is (fun q => q.1 = .read ∨ ∀ k < 4, P (q.2 + k)) →
    ∀ e ∈ traceAll is s, ∀ y, Writes e.accesses y → ∃ o, P o ∧ y = s.regs 13 + BitVec.ofNat 32 o
  | [], _, _ => by intro e he; cases he
  | i :: is, s, h => by
    obtain ⟨h13, l, hl, hp⟩ := h i List.mem_cons_self
    have ih := traceAll_writes_sp' P is (i.next s) h.tail
    rw [next_sp h13] at ih
    intro e he
    rcases List.mem_cons.mp he with rfl | h'
    · rintro y ⟨a, ha, hw, k, hk, rfl⟩
      simp only [accesses_spRel hl, List.mem_map] at ha
      obtain ⟨q, hqm, rfl⟩ := ha
      rcases hp q hqm with hr | hn
      · simp [spAccess, hr] at hw
      · exact ⟨q.2 + k, hn k (by simpa [spAccess] using hk), by simp [spAccess, ofNat_add_assoc]⟩
    · exact ih e h'

/-! ## `BLK` and the context -/

theorem blk_macWr (A : Word) (j : Nat) (hj : j < 16) : MacWr A (A + 72#32 + BitVec.ofNat 32 j) :=
  .inr (.inr ⟨j, by omega, rfl⟩)

theorem outBlk_of {A y : Word} (h : ¬ MacWr A y) : OutBlk A y := fun j hj e => h (e ▸ blk_macWr A j hj)

namespace MacEnv
variable {base A d n : Word} {M : Mem} (he : MacEnv base A d n M)
include he

/-- Context words lie outside `BLK`. -/
theorem ctx_out {m1 m2 : Mem} (hf : ∀ y, OutBlk A y → m1 y = m2 y) (j : Nat) (hj : j < 16) :
    wordAt m1 (A + 8#32) j = wordAt m2 (A + 8#32) j := by
  unfold wordAt; congr 1
  apply read32_congr
  intro k hk
  rw [slot, ctxW]
  apply hf
  intro j' hj' e
  rw [show (72#32 : Word) = BitVec.ofNat 32 72 from rfl, W_add] at e
  have := he.W_inj (by omega) (by omega) e
  omega

theorem acc_out {m1 m2 : Mem} (hf : ∀ y, OutBlk A y → m1 y = m2 y) :
    accAt m1 (A + 8#32) = accAt m2 (A + 8#32) := by
  unfold accAt
  rw [he.ctx_out hf 0 (by decide), he.ctx_out hf 1 (by decide), he.ctx_out hf 2 (by decide),
    he.ctx_out hf 3 (by decide), he.ctx_out hf 4 (by decide)]

theorem codeAt_of {m1 : Mem} (hf : ∀ y, ¬ MacWr A y → m1 y = M y) : CodeAt m1 base B := by
  intro i hi
  rw [hf _ (MacEnv.not_macWr he.codeS (by rw [B_len] at hi; exact hi))]
  exact he.code i hi

end MacEnv

/-- `BLK` as a byte list: the copied source bytes, then zeros. -/
theorem blk_bytes (A dq : Word) (M0 M mem : Mem) (rem : Nat) (hr : rem ≤ 16) (h : BlkHas A dq M0 rem mem)
    (hs : ∀ j < rem, M0 (dq + BitVec.ofNat 32 j) = M (dq + BitVec.ofNat 32 j)) :
    Ctx.bytesAt mem (A + 72#32) 16 = Ctx.bytesAt M dq rem ++ List.replicate (16 - rem) 0#8 := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 16
  · rw [Frame.bytesAt_get _ _ _ _ hj, h j hj]
    by_cases hjr : j < rem
    · rw [if_pos hjr, List.getElem?_append_left (by rw [bytesAt_length]; exact hjr),
        Frame.bytesAt_get _ _ _ _ hjr, hs j hjr]
    · rw [if_neg hjr, List.getElem?_append_right (by rw [bytesAt_length]; omega), bytesAt_length,
        List.getElem?_replicate, if_pos (by omega)]
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega),
      List.getElem?_eq_none (by simp [bytesAt_length]; omega)]

/-- RFC padding of `N` bytes, split at the last whole block. -/
theorem pad_split (M : Mem) (d : Word) (N : Nat) (hr : N % 16 ≠ 0) :
    Ctx.bytesAt M d N ++ pad16 (Ctx.bytesAt M d N) =
      Ctx.bytesAt M d (16 * (N / 16)) ++
        (Ctx.bytesAt M (d + BitVec.ofNat 32 (16 * (N / 16))) (N % 16) ++ List.replicate (16 - N % 16) 0#8) := by
  have e := Poly1305Spec.bytesAt_add M d (16 * (N / 16)) (N % 16)
  rw [show 16 * (N / 16) + N % 16 = N by omega] at e
  rw [pad16, bytesAt_length, e, List.append_assoc, show (16 - N % 16) % 16 = 16 - N % 16 by omega]

theorem pad_zero (M : Mem) (d : Word) (N : Nat) (hr : N % 16 = 0) :
    Ctx.bytesAt M d N ++ pad16 (Ctx.bytesAt M d N) = Ctx.bytesAt M d (16 * (N / 16)) := by
  rw [pad16, bytesAt_length, hr, show 16 * (N / 16) = N by omega]
  simp

/-! ## The tail -/

/-- State at `m + macSize`, after all of `MAC_PADDED`. -/
structure MacPost (base A d n : Word) (M : Mem) (m : Nat) (s t : State) : Prop where
  pc : t.pc = base + BitVec.ofNat 32 (m + macSize)
  sp : t.regs 13 = A
  hi : ∀ r : Reg, 7 ≤ r.val → r.val < 12 → t.regs r = s.regs r
  frame : ∀ y, ¬ MacWr A y → t.mem y = M y
  acc : accAt t.mem (A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt M (A + 8#32)) 1 (accAt M (A + 8#32) % p)
    (Ctx.bytesAt M d n.toNat ++ pad16 (Ctx.bytesAt M d n.toNat))
  bound : accAt t.mem (A + 8#32) < 5 * 2 ^ 128

theorem macD_sp : SpBlock macD (fun q => q.1 = .read ∨ ∀ k < 4, 72 ≤ q.2 + k ∧ q.2 + k < 88) := by
  apply (spBlock_of_B (ok := fun q => q.1 == .read || (72 ≤ q.2 && q.2 + 4 ≤ 88)) (by decide)).mono
  intro q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hq
  rcases hq with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr fun k hk => ⟨by omega, by omega⟩

theorem macD_al : SpBlock macD (fun q => q.2 % 4 = 0) :=
  (spBlock_of_B (ok := fun q => q.2 % 4 == 0) (by decide)).mono (fun q hq => by simpa using hq)

/-- **Partial block.** From `m + macCOff` to `m + macSize`. -/
theorem mac_tail {Pc : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25) (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hrg : InRegion Pc base m macSize)
    (hblk : ∀ pc, Poly1305Blocks.BlkPc base pc → Pc pc) (he : MacEnv base A d n M) (s t : State)
    (ht : MacMid base A d n M m s t) (hk : keyAtOK M (A + 8#32)) :
    ReachW base Pc (MacWr A) t (MacPost base A d n M m s) := by
  obtain ⟨-, -, -, -, sC, bC, sD, sL, bL, sE, bl2, -, t2⟩ := hat
  have hb2 : base.toNat % 2 = 0 := by have := he.base4; omega
  have hN := n.isLt
  obtain ⟨c6, cz, cm, cr⟩ := macC_effect t
  apply ReachW.block hb2 macC (m + macCOff) ht.pc (by have := macCOff_even; omega) sC (by decide) (by simp [alignedAll, macC, Instr.accesses])
    (by
      intro e he' y ⟨a, ha, _⟩
      simp [traceAll, macC] at he'
      rcases he' with rfl | rfl <;> simp [Instr.accesses] at ha)
    (hrg.sub (by decide))
  generalize hs1 : execAll macC t = s1 at c6 cz cm cr
  have p1 : s1.pc = base + BitVec.ofNat 32 (m + macBr1Off) := by
    rw [← hs1, execAll_pc _ _ (by decide), ht.pc, ofNat_add_assoc]; rfl
  rw [ht.r5, and15] at c6 cz
  apply ReachW.bcond hb2 (m + macBr1Off) (m + macSize) 0 (brImm8 (m + macBr1Off) (m + macSize)) p1
    (by have := macBr1Off_even; omega) bC
    (by have := macBr1Off_fits; omega)
    (by have := macBr1Off_le
        rw [brImm8_shift, BitVec.add_assoc, macBr1_disp, ← BitVec.ofNat_add]
        congr 1 <;> omega)
    (hrg.at (by decide))
  · -- `n % 16 = 0`: nothing more to absorb
    intro hz
    have hz' : BitVec.ofNat 32 (n.toNat % 16) = 0#32 := by simpa [condPassed, cz] using hz
    have hr : n.toNat % 16 = 0 := by
      have := congrArg BitVec.toNat hz'; simp at this; omega
    apply ReachS.done
    refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq],
      by rw [setReg_ne _ _ _ _ (by decide), cr _ (by decide) (by decide), ht.sp],
      fun r a b => by
        rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)), cr _ (by omega) (by omega), ht.hi r a b],
      fun y hy => by rw [setReg_mem, cm, ht.frame y hy], ?_, ?_⟩
    · rw [setReg_mem, cm, pad_zero M d _ hr]; exact ht.acc
    · rw [setReg_mem, cm]; exact ht.bound
  · intro hz
    have hz' : BitVec.ofNat 32 (n.toNat % 16) ≠ 0#32 := by simpa [condPassed, cz] using hz
    have hr0 : n.toNat % 16 ≠ 0 := by
      intro e; apply hz'; rw [e]
    generalize hrem : n.toNat % 16 = rem at c6 hr0
    have hr16 : rem < 16 := by omega
    have hf : m + macBr1Off + 2 = m + macDOff := by have := macBr1Off_fall; omega
    generalize hs2 : s1.setReg 15 (base + BitVec.ofNat 32 (m + macBr1Off + 2)) = s2
    have p2 : s2.pc = base + BitVec.ofNat 32 (m + macDOff) := by
      rw [← hs2, M0Crypto.Armv6M.State.pc, setReg_eq, hf]
    have r2 : ∀ r : Reg, r.val ≠ 15 → s2.regs r = s1.regs r := fun r h => by
      rw [← hs2, setReg_ne _ _ _ _ (by rintro rfl; exact h rfl)]
    have s2m : s2.mem = t.mem := by rw [← hs2, setReg_mem, cm]
    have s213 : s2.regs 13 = A := by rw [r2 13 (by decide), cr 13 (by decide) (by decide), ht.sp]
    obtain ⟨d4, d1, d2, dm, dr⟩ := macD_effect s2
    apply ReachW.block hb2 macD (m + macDOff) p2 (by have := macDOff_even; omega) sD (by decide)
      (alignedAll_sp macD s2 macD_al (by rw [s213]; have := he.a8; omega))
      (by
        intro e he' y hy
        obtain ⟨o, ⟨o1, o2⟩, rfl⟩ := traceAll_writes_sp' (fun o => 72 ≤ o ∧ o < 88) macD s2 macD_sp e he' y hy
        rw [s213]
        refine .inr (.inr ⟨o - 72, by omega, ?_⟩)
        rw [show (72#32 : Word) = BitVec.ofNat 32 72 from rfl, ofNat_add_assoc]; congr 2; omega)
      (hrg.sub (by decide))
    generalize hs3 : execAll macD s2 = s3 at d4 d1 d2 dm dr
    have p3 : s3.pc = base + BitVec.ofNat 32 (m + macLOff) := by
      rw [← hs3, execAll_pc _ _ (by decide), p2, ofNat_add_assoc]; rfl
    rw [s213] at d1 dm
    rw [s2m] at dm
    obtain ⟨z0, zo⟩ := zero16 t.mem A
    -- the source of the partial block
    let dq := d + BitVec.ofNat 32 (16 * (n.toNat / 16))
    have h4 : s3.regs 4 = dq := by
      rw [d4, r2 4 (by decide), r2 5 (by decide), cr 4 (by decide) (by decide), cr 5 (by decide) (by decide),
        ht.r4, ht.r5, shl_shr]
    have src_out : ∀ j < rem, ¬ MacWr A (dq + BitVec.ofNat 32 j) := fun j hj => by
      show ¬ MacWr A (d + BitVec.ofNat 32 (16 * (n.toNat / 16)) + BitVec.ofNat 32 j)
      rw [ofNat_add_assoc]; exact MacEnv.not_macWr he.dataS (by omega)
    have s3out : ∀ y, OutBlk A y → s3.mem y = t.mem y := fun y hy => by rw [dm]; exact zo y hy
    have hR3 : ∀ q : Reg, 7 ≤ q.val → q.val < 12 → s3.regs q = s.regs q := fun q a b => by
      rw [dr q (by omega) (by omega) (by omega) (by omega) (by omega), r2 q (by omega),
        cr q (by omega) (by omega), ht.hi q a b]
    apply ReachS.bind
    apply (mac_loop base A dq s3.mem s.regs m rem sL bL he.base4 hm hmx hr16 hrg
      (fun j hj => outBlk_of (src_out j hj)) rem 0 (by omega) (by omega) s3 p3 d1 d2 h4
      (by rw [dr 6 (by decide) (by decide) (by decide) (by decide) (by decide), r2 6 (by decide), c6])
      (by rw [dr 13 (by decide) (by decide) (by decide) (by decide) (by decide), s213]) hR3
      (fun j hj => by simp only [Nat.not_lt_zero, if_false]; rw [dm]; exact z0 j hj)
      (fun y _ => rfl)).mono (fun _ _ h => h)
    rintro v ⟨vpc, v1, v13, vR, vblk, vout⟩
    -- memory facts at the loop exit
    have vO : ∀ y, OutBlk A y → v.mem y = t.mem y := fun y hy => by rw [vout y hy, s3out y hy]
    have vM : ∀ y, ¬ MacWr A y → v.mem y = M y := fun y hy => by
      rw [vO y (outBlk_of hy), ht.frame y hy]
    have vblk' : Ctx.bytesAt v.mem (A + 72#32) 16 = Ctx.bytesAt M dq rem ++ List.replicate (16 - rem) 0#8 :=
      blk_bytes A dq s3.mem M v.mem rem (by omega) vblk (fun j hj => by
        rw [s3out _ (outBlk_of (src_out j hj)), ht.frame _ (src_out j hj)])
    obtain ⟨e0, e2, e3, em, er⟩ := macE_effect v
    apply ReachW.block hb2 macE (m + macEOff) vpc (by have := macEOff_even; omega) sE (by decide)
      (by simp [alignedAll, macE, Instr.accesses])
      (by
        intro e he' y ⟨a, ha, _⟩
        simp [traceAll, macE] at he'
        rcases he' with rfl | rfl | rfl <;> simp [Instr.accesses] at ha)
      (hrg.sub (by decide))
    generalize hw : execAll macE v = w at e0 e2 e3 em er
    have pw : w.pc = base + BitVec.ofNat 32 (m + macBl2Off) := by
      rw [← hw, execAll_pc _ _ (by decide), vpc, ofNat_add_assoc]; rfl
    apply ReachW.bl hb2 (m + macBl2Off) blocksOff i2 pw (by have := macBl2Off_even; omega) bl2
      (by have := macBl2Off_fits; omega) t2 (hrg.at (by decide))
    generalize hx : (w.setReg 14 ((base + BitVec.ofNat 32 (m + macBl2Off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 blocksOff) = x
    have xr : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → x.regs r = w.regs r := fun r a b => by
      rw [← hx, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl),
        setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
    have xm : x.mem = v.mem := by rw [← hx, setReg_mem, setReg_mem, em]
    have x0 : x.regs 0 = A + 8#32 := by rw [xr 0 (by decide) (by decide), e0, v13]
    have x1 : x.regs 1 = A + 72#32 := by
      rw [xr 1 (by decide) (by decide), er 1 (by decide) (by decide) (by decide) (by decide), v1]
    have x2 : x.regs 2 = 1#32 := by rw [xr 2 (by decide) (by decide), e2]
    have x3 : x.regs 3 = 1#32 := by rw [xr 3 (by decide) (by decide), e3]
    have x13 : x.regs 13 = A := by
      rw [xr 13 (by decide) (by decide), er 13 (by decide) (by decide) (by decide) (by decide), v13]
    have x14 : x.regs 14 = (base + BitVec.ofNat 32 (m + macBl2Off + 4)) ||| 1#32 := by
      rw [← hx, setReg_ne _ _ _ _ (by decide), setReg_eq]
    have x15 : x.regs 15 = base + BitVec.ofNat 32 blocksOff := by rw [← hx, setReg_eq]
    have xM : ∀ y, ¬ MacWr A y → x.mem y = M y := fun y hy => by rw [xm]; exact vM y hy
    let c : BCtx := { base := base, sp0 := A, ctx := A + 8#32, msg := A + 72#32, count := 1#32, pad := 1#32,
                      m0 := x.mem, regs0 := x.regs }
    have hv : BValid c := he.bvalid 1#32 (A + 72#32) x.mem x.regs 1#32
      (by
        have := he.aLo; have := he.aHi
        refine ⟨?_, ?_, .inr ?_⟩
        · rw [he.blk_toNat]; show A.toNat + 72 + 16 * 1 ≤ 2 ^ 32; omega
        · rw [he.lo]; omega
        · rw [he.lo, he.blk_toNat]; omega)
      (he.codeAt_of xM)
    have hen : BEntry c x := ⟨rfl, rfl, x15, x13, x0, x1, x2, x3⟩
    have hlr : (c.regs0 14).getLsbD 0 = true := by show (x.regs 14).getLsbD 0 = true; rw [x14]; exact lr_odd _
    apply (((Poly1305Blocks.blocks_reach_w c hv x hen hlr).monoW (bwr_mac A c rfl rfl)).monoPc hblk).mono
      (fun _ _ h => h)
    intro t' ht'
    have xacc : accAt x.mem (A + 8#32) = accAt t.mem (A + 8#32) := by
      rw [xm]; exact he.acc_out vO
    obtain ⟨acc, bound⟩ := Poly1305Blocks.result_blocks_correct c hv x t' hen ht'
      (he.keyOk xM hk)
      (by show accAt x.mem (A + 8#32) < _; rw [xacc]; exact ht.bound)
      (by show (1#32 : Word).toNat ≤ 1; decide)
    refine ⟨?_, ht'.sp, ?_, ?_, ?_, bound⟩
    · rw [ht'.pc]; show x.regs 14 &&& ~~~1#32 = _
      rw [x14, lr_mask _ (even_off base he.base4 (m + macBl2Off + 4) (by have := macBl2Off_even; omega)),
        show m + macBl2Off + 4 = m + macSize by have := macBl2Off_end; omega]
    · intro r a b
      rw [ht'.regs r (by omega) b]
      show x.regs r = _
      rw [xr r (by omega) (by omega), er r (by omega) (by omega) (by omega) (by omega), vR r a b]
    · intro y hy
      rw [Poly1305Blocks.result_frame c hv x t' hen hlr ht' y (fun h => hy (bwr_mac A c rfl rfl y h))]
      exact xM y hy
    · have acc' : accAt t'.mem (A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt x.mem (A + 8#32)) 1
          (accAt x.mem (A + 8#32) % p) (Ctx.bytesAt x.mem (A + 72#32) 16) := acc
      rw [he.key_eq xM, xacc, ht.acc, xm, vblk'] at acc'
      rw [acc', pad_split M d _ (by omega), hrem,
        Poly1305Spec.polyBlocks_append _ _ _ (n.toNat / 16) _ _ (bytesAt_length _ _ _)]

/-- **`MAC_PADDED`.** From `m` to `m + macSize`: the accumulator absorbs `msg ++ pad16 msg`
for the `n` bytes at `d`, with pad 1, writing only `MacWr A`. Region-tracking form. -/
theorem mac_padded_w {Pc : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25)
    (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hrg : InRegion Pc base m macSize)
    (hblk : ∀ pc, Poly1305Blocks.BlkPc base pc → Pc pc) (he : MacEnv base A d n M) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 m) (h13 : s.regs 13 = A) (h4 : s.regs 4 = d)
    (h5 : s.regs 5 = n) (hmem : s.mem = M)
    (hk : keyAtOK M (A + 8#32)) (hh : accAt M (A + 8#32) < 5 * 2 ^ 128) :
    ReachW base Pc (MacWr A) s (MacPost base A d n M m s) := by
  apply ReachS.bind
  apply (mac_head base A d n M m i1 i2 hat hm hmx hrg hblk he s hpc h13 h4 h5 hmem hk hh).mono
    (fun _ _ h => h)
  intro t ht
  exact mac_tail base A d n M m i1 i2 hat hm hmx hrg hblk he s t ht hk

/-- **`MAC_PADDED`.** From `m` to `m + macSize`: the accumulator absorbs `msg ++ pad16 msg`
for the `n` bytes at `d`, with pad 1, writing only `MacWr A`. -/
theorem mac_padded (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25) (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (he : MacEnv base A d n M) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 m) (h13 : s.regs 13 = A) (h4 : s.regs 4 = d)
    (h5 : s.regs 5 = n) (hmem : s.mem = M)
    (hk : keyAtOK M (A + 8#32)) (hh : accAt M (A + 8#32) < 5 * 2 ^ 128) :
    Reach base (MacWr A) s (MacPost base A d n M m s) :=
  (mac_padded_w (Pc := fun _ => True) base A d n M m i1 i2 hat hm hmx (fun _ _ => trivial)
    (fun _ _ => trivial) he s hpc h13 h4 h5 hmem hk hh).toReach

end M0Crypto.Release.Aead
