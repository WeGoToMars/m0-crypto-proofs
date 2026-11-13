import M0Crypto.Release.Call
import M0Crypto.Release.AeadCode
import M0Crypto.Release.Poly1305Context
import M0Crypto.Release.ReachSteps
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`MAC_PADDED` (60 bytes at four offsets): absorb `n` bytes at `d`, zero-padded to a
multiple of 16, into the Poly1305 context at `A + 8`, where `A` is the AEAD stack
pointer. Whole blocks go directly to `m0c_poly1305_blocks`; a partial final block
is copied into `BLK` (`A + 72`), which was zeroed first, and absorbed as one block.

This file proves the whole-block half (`mac_head`), from offset `m` to `m + macCOff`.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK)
open M0Crypto.Spec.Aead (p)

/-- Bytes `MAC_PADDED` may write: the 64 bytes below `A` used by `blocks`, the five
accumulator words of `CTX`, and the first 16 bytes of `BLK`. -/
def MacWr (A : Word) (y : Word) : Prop :=
  InFrame (A - 64#32) 16 y ∨ InFrame (A + 8#32) 5 y ∨ InFrame (A + 72#32) 4 y

/-- Placement facts for one `MAC_PADDED` over `n` bytes at `d` with memory `M`. -/
structure MacEnv (base A d n : Word) (M : Mem) : Prop where
  base4 : base.toNat % 4 = 0
  a8 : A.toNat % 8 = 0
  aLo : 64 ≤ A.toNat
  aHi : A.toNat + 144 ≤ 2 ^ 32
  codeS : Disj base Artifacts.Release.size (A - 64#32) 208
  dataS : Disj d n.toNat (A - 64#32) 208
  code : CodeAt M base B

theorem disj_sub {a b b' : Word} {n m m' : Nat} (h : Disj a n b m) (h1 : b.toNat ≤ b'.toNat)
    (h2 : b'.toNat + m' ≤ b.toNat + m) : Disj a n b' m' := by
  obtain ⟨x, y, z⟩ := h
  exact ⟨x, by omega, by omega⟩

theorem disj_mono {a b : Word} {n n' m : Nat} (h : Disj a n b m) (h1 : n' ≤ n) : Disj a n' b m := by
  obtain ⟨x, y, z⟩ := h
  exact ⟨by omega, y, by omega⟩

namespace MacEnv
variable {base A d n : Word} {M : Mem} (he : MacEnv base A d n M)
include he

theorem lo : (A - 64#32).toNat = A.toNat - 64 := by
  have := he.aLo; simp [BitVec.toNat_sub]; omega
theorem off (k : Nat) (hk : k < 144) : (A + BitVec.ofNat 32 k).toNat = A.toNat + k := by
  have := he.aHi; simp [BitVec.toNat_add]; omega
theorem ctx_toNat : (A + 8#32).toNat = A.toNat + 8 := he.off 8 (by decide)
theorem blk_toNat : (A + 72#32).toNat = A.toNat + 72 := he.off 72 (by decide)

/-- The window `[A - 64, A + 144)` contains each region the callees use. -/
theorem sub (k m' : Nat) (b : Word) (hb : b.toNat = A.toNat - 64 + k) (hk : k + m' ≤ 208)
    {a : Word} {l : Nat} (h : Disj a l (A - 64#32) 208) : Disj a l b m' :=
  disj_sub h (by rw [hb, he.lo]; omega) (by rw [hb, he.lo]; omega)

theorem bvalid (cnt : Word) (msg : Word) (mem : Mem) (regs : Reg → Word) (pad : Word)
    (hmsg : Disj msg (16 * cnt.toNat) (A - 64#32) 64) (hc : CodeAt mem base B) :
    BValid { base := base, sp0 := A, ctx := A + 8#32, msg := msg, count := cnt, pad := pad,
             m0 := mem, regs0 := regs } where
  base4 := he.base4
  sp8 := he.a8
  spLo := he.aLo
  ctx4 := by show (A + 8#32).toNat % 4 = 0; rw [he.ctx_toNat]; have := he.a8; omega
  codeS := by
    show Disj base Artifacts.Release.size (A - 64#32) 64
    exact he.sub 0 64 _ (by rw [he.lo]; omega) (by decide) he.codeS
  codeC := by
    have h := he.aLo
    exact he.sub 72 64 _ (by rw [he.ctx_toNat]; omega) (by decide) he.codeS
  ctxS := by
    show Disj (A + 8#32) 64 (A - 64#32) 64
    refine ⟨by rw [he.ctx_toNat]; have := he.aHi; omega, by rw [he.lo]; have := he.aLo; omega, ?_⟩
    have := he.aLo
    rw [he.ctx_toNat, he.lo]; omega
  msgS := hmsg
  code := hc

end MacEnv

/-- MacWr contains everything a `blocks` call from `A` with context `A + 8` writes. -/
theorem bwr_mac (A : Word) (c : BCtx) (hs : c.sp0 = A) (hc : c.ctx = A + 8#32) (y : Word)
    (h : c.Wr y) : MacWr A y := by
  rcases h with h | ⟨_, h⟩
  · left; rw [BCtx.fp, hs] at h; exact h
  · right; left; rw [hc] at h; exact h

theorem setReg_ne (s : State) (r r' : Reg) (x : Word) (h : r' ≠ r) : (s.setReg r x).regs r' = s.regs r' :=
  setReg_regs_ne s r r' x h
theorem setReg_eq (s : State) (r : Reg) (x : Word) : (s.setReg r x).regs r = x := by
  simp [M0Crypto.Armv6M.State.setReg]
theorem setReg_mem (s : State) (r : Reg) (x : Word) : (s.setReg r x).mem = s.mem := rfl

/-- State at `m + macCOff`, after the whole blocks. -/
structure MacMid (base A d n : Word) (M : Mem) (m : Nat) (s t : State) : Prop where
  pc : t.pc = base + BitVec.ofNat 32 (m + macCOff)
  sp : t.regs 13 = A
  r4 : t.regs 4 = d
  r5 : t.regs 5 = n
  hi : ∀ r : Reg, 7 ≤ r.val → r.val < 12 → t.regs r = s.regs r
  frame : ∀ y, ¬ MacWr A y → t.mem y = M y
  acc : accAt t.mem (A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt M (A + 8#32)) 1 (accAt M (A + 8#32) % p)
    (Ctx.bytesAt M d (16 * (n.toNat / 16)))
  bound : accAt t.mem (A + 8#32) < 5 * 2 ^ 128

theorem lsr4 (n : Word) : (n >>> 4).toNat = n.toNat / 16 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem macA_effect (s : State) :
    (execAll macA s).regs 2 = s.regs 5 >>> 4 ∧ (execAll macA s).z = (s.regs 5 >>> 4 == 0#32) ∧
    (execAll macA s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → (execAll macA s).regs r = s.regs r) := by
  refine ⟨?_, ?_, rfl, fun r h2 h15 => execAll_regs_other _ _ r h15 (by simp [macA, Instr.dsts, Fin.ext_iff, h2])⟩ <;>
  simp [macA, execAll, Instr.next, Instr.exec, lsrC, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6]

theorem macB_effect (s : State) :
    (execAll macB s).regs 0 = s.regs 13 + 8#32 ∧ (execAll macB s).regs 1 = s.regs 4 ∧
    (execAll macB s).regs 3 = 1#32 ∧ (execAll macB s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 3 → r.val ≠ 15 → (execAll macB s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, rfl, fun r h0 h1 h3 h15 => execAll_regs_other _ _ r h15
    (by simp [macB, Instr.dsts, Fin.ext_iff, h0, h1]; omega)⟩ <;>
  simp [macB, execAll, Instr.next, Instr.exec, lslC, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg,
    M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6]

theorem even_off (base : Word) (hb : base.toNat % 4 = 0) (k : Nat) (hk : k % 2 = 0) :
    (base + BitVec.ofNat 32 k).toNat % 2 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **Whole blocks.** From `m` to `m + macCOff`: the accumulator absorbs the
`16 * (n / 16)` leading bytes with pad 1. -/
theorem mac_head {Pc : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25) (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hrg : InRegion Pc base m macSize)
    (hblk : ∀ pc, Poly1305Blocks.BlkPc base pc → Pc pc) (he : MacEnv base A d n M) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 m) (h13 : s.regs 13 = A) (h4 : s.regs 4 = d)
    (h5 : s.regs 5 = n) (hmem : s.mem = M)
    (hk : keyAtOK M (A + 8#32)) (hh : accAt M (A + 8#32) < 5 * 2 ^ 128) :
    ReachW base Pc (MacWr A) s (MacMid base A d n M m s) := by
  obtain ⟨sA, bA, sB, bl1, -, -, -, -, -, -, -, t1, -⟩ := hat
  have hb2 : base.toNat % 2 = 0 := by have := he.base4; omega
  obtain ⟨a2, az, am, ar⟩ := macA_effect s
  apply ReachW.block hb2 macA m hpc hm sA (by decide) (by simp [alignedAll, macA, Instr.accesses])
    (by intro e he' y ⟨a, ha, _⟩; simp [traceAll, macA, Instr.accesses] at he'; subst he'; simp at ha)
    (hrg.prefix (by decide))
  generalize hs1 : execAll macA s = s1 at a2 az am ar
  have p1 : s1.pc = base + BitVec.ofNat 32 (m + macBr0Off) := by
    rw [← hs1, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  apply ReachW.bcond hb2 (m + macBr0Off) (m + macCOff) 0 (brImm8 (m + macBr0Off) (m + macCOff)) p1
    (by have := macBr0Off_even; omega) bA (by have := macBr0Off_fits; omega)
    (by have := macBr0Off_le
        rw [brImm8_shift, BitVec.add_assoc, macBr0_disp, ← BitVec.ofNat_add]
        congr 1 <;> omega)
    (hrg.at (by decide))
  · -- no whole block
    intro hz
    have hz' : s.regs 5 >>> 4 = 0#32 := by simpa [condPassed, az] using hz
    have hn : n.toNat / 16 = 0 := by rw [← lsr4, ← h5, hz']; rfl
    apply ReachS.done
    refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq], by rw [setReg_ne _ _ _ _ (by decide), ar _ (by decide) (by decide), h13],
      by rw [setReg_ne _ _ _ _ (by decide), ar _ (by decide) (by decide), h4],
      by rw [setReg_ne _ _ _ _ (by decide), ar _ (by decide) (by decide), h5],
      fun r a b => by rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)), ar _ (by intro e; omega) (by omega)],
      fun y _ => by rw [setReg_mem, am, hmem], ?_, ?_⟩
    · rw [setReg_mem, am, hmem, hn, Nat.mul_zero]; exact (Poly1305Spec.polyBlocks_nil _ _ _).symm
    · rw [setReg_mem, am, hmem]; exact hh
  · intro hz
    have hz' : s.regs 5 >>> 4 ≠ 0#32 := by simpa [condPassed, az] using hz
    generalize hs2 : s1.setReg 15 (base + BitVec.ofNat 32 (m + macBr0Off + 2)) = s2
    have hf : m + macBr0Off + 2 = m + macBOff := by have := macBr0Off_fall; omega
    have p2 : s2.pc = base + BitVec.ofNat 32 (m + macBOff) := by
      rw [← hs2, M0Crypto.Armv6M.State.pc, setReg_eq, hf]
    have r2 : ∀ r : Reg, r.val ≠ 15 → s2.regs r = s1.regs r := fun r h => by
      rw [← hs2, setReg_ne _ _ _ _ (by rintro rfl; exact h rfl)]
    obtain ⟨b0, b1, b3, bm, br⟩ := macB_effect s2
    apply ReachW.block hb2 macB (m + macBOff) p2 (by have := macBOff_even; omega) sB (by decide)
      (by simp [alignedAll, macB, Instr.accesses])
      (by
        intro e he' y ⟨a, ha, _⟩
        simp [traceAll, macB] at he'
        rcases he' with rfl | rfl | rfl <;> simp [Instr.accesses] at ha)
      (hrg.sub (by decide))
    generalize hs3 : execAll macB s2 = s3 at b0 b1 b3 bm br
    have p3 : s3.pc = base + BitVec.ofNat 32 (m + macBlOff) := by
      rw [← hs3, execAll_pc _ _ (by decide), p2, ofNat_add_assoc]; rfl
    apply ReachW.bl hb2 (m + macBlOff) blocksOff i1 p3 (by have := macBlOff_even; omega) bl1
      (by have := macBlOff_fits; omega) t1 (hrg.at (by decide))
    generalize hu : (s3.setReg 14 ((base + BitVec.ofNat 32 (m + macBlOff + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 blocksOff) = u
    have ur : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → u.regs r = s3.regs r := fun r a b => by
      rw [← hu, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl),
        setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
    have um : u.mem = M := by rw [← hu, setReg_mem, setReg_mem, bm, ← hs2, setReg_mem, am, hmem]
    have us : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val < 14 → u.regs r = s.regs r :=
      fun r x0 x1 x2 x3 x14 => by
        rw [ur r (by omega) (by omega), br r x0 x1 x3 (by omega), r2 r (by omega), ar r x2 (by omega)]
    have u0 : u.regs 0 = A + 8#32 := by
      rw [ur 0 (by decide) (by decide), b0, r2 13 (by decide), ar 13 (by decide) (by decide), h13]
    have u1 : u.regs 1 = d := by
      rw [ur 1 (by decide) (by decide), b1, r2 4 (by decide), ar 4 (by decide) (by decide), h4]
    have u2 : u.regs 2 = n >>> 4 := by
      rw [ur 2 (by decide) (by decide), br 2 (by decide) (by decide) (by decide) (by decide),
        r2 2 (by decide), a2, h5]
    have u3 : u.regs 3 = 1#32 := by rw [ur 3 (by decide) (by decide), b3]
    have u14 : u.regs 14 = (base + BitVec.ofNat 32 (m + macBlOff + 4)) ||| 1#32 := by
      rw [← hu, setReg_ne _ _ _ _ (by decide), setReg_eq]
    have u15 : u.regs 15 = base + BitVec.ofNat 32 blocksOff := by rw [← hu, setReg_eq]
    let c : BCtx := { base := base, sp0 := A, ctx := A + 8#32, msg := d, count := n >>> 4, pad := 1#32,
                      m0 := u.mem, regs0 := u.regs }
    have hcnt : (n >>> 4).toNat = n.toNat / 16 := lsr4 n
    have hv : BValid c := he.bvalid (n >>> 4) d u.mem u.regs 1#32
      (by
        rw [hcnt]
        exact he.sub 0 64 _ (by rw [he.lo]; omega) (by decide) (disj_mono he.dataS (by omega)))
      (by rw [um]; exact he.code)
    have hen : BEntry c u := ⟨rfl, rfl, u15,
      by show u.regs 13 = A; rw [us 13 (by decide) (by decide) (by decide) (by decide) (by decide), h13],
      u0, u1, u2, u3⟩
    have hlr : (c.regs0 14).getLsbD 0 = true := by show (u.regs 14).getLsbD 0 = true; rw [u14]; exact lr_odd _
    apply ReachS.bind
    apply ((((Poly1305Blocks.blocks_reach_w c hv u hen hlr).monoW (bwr_mac A c rfl rfl)).monoPc hblk)).mono
      (fun _ _ h => h)
    intro t ht
    apply ReachS.done
    have hret : t.pc = base + BitVec.ofNat 32 (m + macCOff) := by
      have hcm : m + macBlOff + 4 = m + macCOff := by have := macBlOff_ret; omega
      have hke : (m + macBlOff + 4) % 2 = 0 := by have := macBlOff_even; omega
      rw [ht.pc]; show u.regs 14 &&& ~~~1#32 = _
      rw [u14, lr_mask _ (even_off base he.base4 (m + macBlOff + 4) hke), hcm]
    obtain ⟨acc, bound⟩ := Poly1305Blocks.result_blocks_correct c hv u t hen ht (by show keyAtOK u.mem (A + 8#32); rw [um]; exact hk)
      (by show accAt u.mem (A + 8#32) < _; rw [um]; exact hh)
      (by show (1#32 : Word).toNat ≤ 1; decide)
    refine ⟨hret, ht.sp, ?_, ?_, ?_, ?_, ?_, bound⟩
    · rw [ht.regs 4 (by decide) (by decide)]
      exact (us 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4
    · rw [ht.regs 5 (by decide) (by decide)]
      exact (us 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5
    · intro r a b
      rw [ht.regs r (by omega) b]
      exact us r (by omega) (by omega) (by omega) (by omega) (by omega)
    · intro y hy
      rw [Poly1305Blocks.result_frame c hv u t hen hlr ht y (fun h => hy (bwr_mac A c rfl rfl y h))]
      show u.mem y = M y; rw [um]
    · have acc' : accAt t.mem (A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt u.mem (A + 8#32)) 1
          (accAt u.mem (A + 8#32) % p) (Ctx.bytesAt u.mem d (16 * (n >>> 4).toNat)) := acc
      rw [um, hcnt] at acc'; exact acc'

end M0Crypto.Release.Aead
