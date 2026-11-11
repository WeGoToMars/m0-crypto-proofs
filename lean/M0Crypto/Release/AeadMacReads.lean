import M0Crypto.Release.AeadReadSites
import M0Crypto.Release.AeadLoop
import M0Crypto.Release.AeadCompose
import M0Crypto.Release.AeadMac
import M0Crypto.Release.AeadPad
import M0Crypto.Release.Poly1305BlocksReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read policy of the `MAC_PADDED` pieces

`MacFree m` says that the only caller-memory load of the piece at `m` is the copy loop's `ldrb`.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK)
open M0Crypto.Spec.Aead (p)
open M0Crypto.Release.Frame

def MacFree (m : Nat) : Prop := ∀ j < macSize, j ≠ macLOff → rdSiteB (m + j) = false

/-- The first read site of the padded-MAC piece at `m`, other than the copy loop's load. -/
def macFirstSite (m : Nat) : Option Nat :=
  (((List.range macSize).filter (· != macLOff)).map (m + ·)).find? rdSiteB

theorem macFree_of_first {m : Nat} (h : macFirstSite m = none) : MacFree m := by
  intro j hj hne
  have := List.find?_eq_none.mp h (m + j)
    (List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using hne⟩, rfl⟩)
  simpa using this

theorem size_le : Artifacts.Release.size ≤ 2 ^ 32 := by decide +kernel

theorem MacFree.at {base : Word} {m : Nat} (hf : MacFree m) {off : Nat} (h1 : off < macSize)
    (h2 : off ≠ macLOff) (hmx : m + macSize ≤ Artifacts.Release.size) :
    NoSite base (base + BitVec.ofNat 32 (m + off)) :=
  not_siteRd (by have := size_le; omega) (hf off h1 h2)

theorem noP {Wr : Word → Prop} (base : Word) (Rd : Word → Prop) :
    ∀ x e, RegionWrites (NoSite base) Wr x e → RdP base Rd x e :=
  fun x e h => rdP_of_free (fun _ h => h) x e h

theorem MacFree.region {base : Word} {m : Nat} (hf : MacFree m) {off n : Nat}
    (h : ∀ j < n, off + j < macSize ∧ off + j ≠ macLOff) (hmx : m + macSize ≤ Artifacts.Release.size) :
    InRegion (NoSite base) base (m + off) n := fun j hj =>
  not_siteRd (by have := size_le; have := (h j hj).1; omega)
    (by have := hf (off + j) (h j hj).1 (h j hj).2; rwa [← Nat.add_assoc] at this)

theorem macL_ok (base : Word) (Rd : Word → Prop) (u : State) (h : Rd (u.regs 4 + u.regs 2)) :
    BlockOk (RdP base Rd) macL u := by
  have := (blockOk_events_iff (p := fun e => SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y)
    macL u).mpr ?_
  · exact this
  intro e he _ y hy
  simp only [macL, traceAll, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [Instr.accesses, Reads, MemOp.isLoad] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  simp [MemOp.width] at hk
  subst hk
  show Rd (u.reg 4 + u.reg 2 + BitVec.ofNat 32 0)
  rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  exact h

/-- **Copy loop**, read-policy form. -/
theorem mac_loop_r {Rd : Word → Prop} (base A dq : Word) (M0 : Mem) (R : Reg → Word) (m rem : Nat)
    (hseq : seqAt B (m + macLOff) macL = true) (hbr : instrAt B (m + macBr2Off) = some (.bcond 1 (brImm8 (m + macBr2Off) (m + macLOff))))
    (hb : base.toNat % 4 = 0) (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hr : rem < 16)
    (hfree : MacFree m) (hdq : ∀ j < rem, OutBlk A (dq + BitVec.ofNat 32 j))
    (hRd : ∀ j < rem, Rd (dq + BitVec.ofNat 32 j)) :
    ∀ r k, k + r = rem → k < rem → ∀ u : State,
      u.pc = base + BitVec.ofNat 32 (m + macLOff) → u.regs 1 = A + 72#32 → u.regs 2 = BitVec.ofNat 32 k →
      u.regs 4 = dq → u.regs 6 = BitVec.ofNat 32 rem → u.regs 13 = A →
      (∀ q : Reg, 7 ≤ q.val → q.val < 12 → u.regs q = R q) →
      BlkHas A dq M0 k u.mem → (∀ y, OutBlk A y → u.mem y = M0 y) →
      ReachS base (RdP base Rd) u (fun v => v.pc = base + BitVec.ofNat 32 (m + macEOff) ∧ v.regs 1 = A + 72#32 ∧
        v.regs 13 = A ∧ (∀ q : Reg, 7 ≤ q.val → q.val < 12 → v.regs q = R q) ∧
        BlkHas A dq M0 rem v.mem ∧ (∀ y, OutBlk A y → v.mem y = M0 y))
  | 0, k, h, hk, _, _, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | r + 1, k, h, hk, u, hpc, h1, h2, h4, h6, h13, hR, hblk, hout => by
    have hb2 : base.toNat % 2 = 0 := by omega
    obtain ⟨lm, l2, lz, lr⟩ := macL_effect u
    refine ReachS.block hb2 macL (m + macLOff) u hpc (by have := macLOff_even; omega) hseq (by decide)
      (by simp [alignedAll, macL, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, Nat.mod_one])
      (macL_ok base Rd u (by
        have e : u.regs 4 + u.regs 2 = dq + BitVec.ofNat 32 k := by rw [h4, h2]
        rw [e]; exact hRd k hk)) ?_
    generalize hv : execAll macL u = v at lm l2 lz lr
    have vpc : v.pc = base + BitVec.ofNat 32 (m + macBr2Off) := by
      rw [← hv, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    have src : read8 u.mem (u.regs 4 + u.regs 2) = (M0 (dq + BitVec.ofNat 32 k)).setWidth 32 := by
      rw [h4, h2, read8, hout _ (hdq k hk)]
    have vblk : BlkHas A dq M0 (k + 1) v.mem := by
      intro j hj
      rw [lm, h1, h2]
      by_cases e : j = k
      · subst e
        have e2 : read8 u.mem (u.regs 4 + BitVec.ofNat 32 j) = (M0 (dq + BitVec.ofNat 32 j)).setWidth 32 := by
          rw [h4, read8, hout _ (hdq j hk)]
        simp only [write8, if_true, e2, byte_copy, if_pos (show j < j + 1 by omega)]
      · rw [write8_other _ _ _ _ (blk_ne A hj (by omega) e), hblk j hj]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega)]
        · rw [if_neg hjk, if_neg (by omega)]
    have vout : ∀ y, OutBlk A y → v.mem y = M0 y := by
      intro y hy
      rw [lm, h1, h2, write8_other _ _ _ _ (hy k (by omega)), hout y hy]
    have v2 : v.regs 2 = BitVec.ofNat 32 (k + 1) := by
      rw [l2, h2]; apply BitVec.eq_of_toNat_eq; simp
    have vz : v.z = decide (k + 1 = rem) := by
      rw [lz, h2, h6]; exact loop_flag k rem (by omega) hr
    have vr : ∀ q : Reg, q.val ≠ 0 → q.val ≠ 2 → q.val ≠ 15 → v.regs q = u.regs q := lr
    refine ReachS.bcondW (Pn := NoSite base) (Wr := fun _ => True) (noP base Rd)
      (hfree.at (off := macBr2Off) (by decide +kernel) (by decide +kernel) hmx) hb2 (m + macLOff) 1
      (brImm8 (m + macBr2Off) (m + macLOff)) vpc (by have := macBr2Off_even; omega) hbr
      (by have := macBr2Off_fits; omega)
      (by rw [brImm8_shift, se_fa, show m + macBr2Off = (m + macLOff) + seqSize macL by have := macBr2Off_back; omega]
          exact back_target _ (seqSize macL)) ?_ ?_
    · intro hne
      have hk1 : k + 1 ≠ rem := by simpa [condPassed, vz] using hne
      apply mac_loop_r base A dq M0 R m rem hseq hbr hb hm hmx hr hfree hdq hRd r (k + 1) (by omega) (by omega)
        _ (by rw [M0Crypto.Armv6M.State.pc, setReg_eq])
      all_goals first
        | (rw [setReg_ne _ _ _ _ (by decide)]; first
            | (rw [vr 1 (by decide) (by decide) (by decide), h1])
            | exact v2
            | (rw [vr 4 (by decide) (by decide) (by decide), h4])
            | (rw [vr 6 (by decide) (by decide) (by decide), h6])
            | (rw [vr 13 (by decide) (by decide) (by decide), h13]))
        | (intro q a b
           rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)),
             vr q (by omega) (by omega) (by omega), hR q a b])
        | exact vblk
        | exact vout
    · intro heq
      have hk1 : k + 1 = rem := by simpa [condPassed, vz] using heq
      have hf : m + macBr2Off + 2 = m + macEOff := by have := macBr2Off_fall; omega
      apply ReachS.done
      refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq, hf],
        by rw [setReg_ne _ _ _ _ (by decide), vr 1 (by decide) (by decide) (by decide), h1],
        by rw [setReg_ne _ _ _ _ (by decide), vr 13 (by decide) (by decide) (by decide), h13],
        fun q a b => by
          rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)),
            vr q (by omega) (by omega) (by omega), hR q a b],
        by rw [setReg_mem, ← hk1]; exact vblk, fun y hy => by rw [setReg_mem]; exact vout y hy⟩


/-- **Whole blocks**, read-policy form. From `m` to `m + macCOff`: the accumulator absorbs the
`16 * (n / 16)` leading bytes with pad 1. -/
theorem mac_head_r {Rd : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25) (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hfree : MacFree m)
    (hR : ∀ o < n.toNat, Rd (d + BitVec.ofNat 32 o)) (he : MacEnv base A d n M) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 m) (h13 : s.regs 13 = A) (h4 : s.regs 4 = d)
    (h5 : s.regs 5 = n) (hmem : s.mem = M)
    (hk : keyAtOK M (A + 8#32)) (hh : accAt M (A + 8#32) < 5 * 2 ^ 128) :
    ReachS base (RdP base Rd) s (MacMid base A d n M m s) := by
  obtain ⟨sA, bA, sB, bl1, -, -, -, -, -, -, -, t1, -⟩ := hat
  have hb2 : base.toNat % 2 = 0 := by have := he.base4; omega
  obtain ⟨a2, az, am, ar⟩ := macA_effect s
  refine ReachS.blockW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.region (off := 0) (n := seqSize macA) (by decide +kernel) hmx) hb2 hpc hm sA (by decide) (by simp [alignedAll, macA, Instr.accesses])
    (by intro e he' y ⟨a, ha, _⟩; simp [traceAll, macA, Instr.accesses] at he'; subst he'; simp at ha)
    ?_
  generalize hs1 : execAll macA s = s1 at a2 az am ar
  have p1 : s1.pc = base + BitVec.ofNat 32 (m + macBr0Off) := by
    rw [← hs1, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
  refine ReachS.bcondW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.at (off := macBr0Off) (by decide +kernel) (by decide +kernel) hmx) hb2 (m + macCOff) 0 (brImm8 (m + macBr0Off) (m + macCOff)) p1
    (by have := macBr0Off_even; omega) bA (by have := macBr0Off_fits; omega)
    (by have := macBr0Off_le
        rw [brImm8_shift, BitVec.add_assoc, macBr0_disp, ← BitVec.ofNat_add]
        congr 1 <;> omega) ?_ ?_
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
    refine ReachS.blockW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.region (off := macBOff) (n := seqSize macB) (by decide +kernel) hmx) hb2 p2 (by have := macBOff_even; omega) sB (by decide)
      (by simp [alignedAll, macB, Instr.accesses])
      (by
        intro e he' y ⟨a, ha, _⟩
        simp [traceAll, macB] at he'
        rcases he' with rfl | rfl | rfl <;> simp [Instr.accesses] at ha)
      ?_
    generalize hs3 : execAll macB s2 = s3 at b0 b1 b3 bm br
    have p3 : s3.pc = base + BitVec.ofNat 32 (m + macBlOff) := by
      rw [← hs3, execAll_pc _ _ (by decide), p2, ofNat_add_assoc]; rfl
    refine ReachS.blW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.at (off := macBlOff) (by decide +kernel) (by decide +kernel) hmx) hb2 blocksOff i1 p3 (by have := macBlOff_even; omega) bl1
      (by have := macBlOff_fits; omega) t1 ?_
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
    have hRc : ∀ o < 16 * c.count.toNat, Rd (c.msg + BitVec.ofNat 32 o) := fun o ho =>
      hR o (by have : c.count.toNat = n.toNat / 16 := hcnt; omega)
    apply (Poly1305Blocks.blocks_reach_r c hv Rd u hen hlr hRc).mono (fun _ _ h => h)
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


/-- **Partial block**, read-policy form. From `m + macCOff` to `m + macSize`. -/
theorem mac_tail_r {Rd : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25) (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hfree : MacFree m)
    (hR : ∀ o < n.toNat, Rd (d + BitVec.ofNat 32 o))
    (hRblk : ∀ o < 16, Rd (A + 72#32 + BitVec.ofNat 32 o)) (he : MacEnv base A d n M) (s t : State)
    (ht : MacMid base A d n M m s t) (hk : keyAtOK M (A + 8#32)) :
    ReachS base (RdP base Rd) t (MacPost base A d n M m s) := by
  obtain ⟨-, -, -, -, sC, bC, sD, sL, bL, sE, bl2, -, t2⟩ := hat
  have hb2 : base.toNat % 2 = 0 := by have := he.base4; omega
  have hN := n.isLt
  obtain ⟨c6, cz, cm, cr⟩ := macC_effect t
  refine ReachS.blockW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.region (off := macCOff) (n := seqSize macC) (by decide +kernel) hmx) hb2 ht.pc (by have := macCOff_even; omega) sC (by decide) (by simp [alignedAll, macC, Instr.accesses])
    (by
      intro e he' y ⟨a, ha, _⟩
      simp [traceAll, macC] at he'
      rcases he' with rfl | rfl <;> simp [Instr.accesses] at ha)
    ?_
  generalize hs1 : execAll macC t = s1 at c6 cz cm cr
  have p1 : s1.pc = base + BitVec.ofNat 32 (m + macBr1Off) := by
    rw [← hs1, execAll_pc _ _ (by decide), ht.pc, ofNat_add_assoc]; rfl
  rw [ht.r5, and15] at c6 cz
  refine ReachS.bcondW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.at (off := macBr1Off) (by decide +kernel) (by decide +kernel) hmx) hb2 (m + macSize) 0 (brImm8 (m + macBr1Off) (m + macSize)) p1
    (by have := macBr1Off_even; omega) bC
    (by have := macBr1Off_fits; omega)
    (by have := macBr1Off_le
        rw [brImm8_shift, BitVec.add_assoc, macBr1_disp, ← BitVec.ofNat_add]
        congr 1 <;> omega) ?_ ?_
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
    refine ReachS.blockW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.region (off := macDOff) (n := seqSize macD) (by decide +kernel) hmx) hb2 p2 (by have := macDOff_even; omega) sD (by decide)
      (alignedAll_sp macD s2 macD_al (by rw [s213]; have := he.a8; omega))
      (by
        intro e he' y hy
        obtain ⟨o, ⟨o1, o2⟩, rfl⟩ := traceAll_writes_sp' (fun o => 72 ≤ o ∧ o < 88) macD s2 macD_sp e he' y hy
        rw [s213]
        refine .inr (.inr ⟨o - 72, by omega, ?_⟩)
        rw [show (72#32 : Word) = BitVec.ofNat 32 72 from rfl, ofNat_add_assoc]; congr 2; omega)
      ?_
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
    apply (mac_loop_r base A dq s3.mem s.regs m rem sL bL he.base4 hm hmx hr16 hfree
      (fun j hj => outBlk_of (src_out j hj))
      (fun j hj => by
        have h1 := hR (16 * (n.toNat / 16) + j) (by omega)
        rw [← ofNat_add_assoc] at h1; exact h1) rem 0 (by omega) (by omega) s3 p3 d1 d2 h4
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
    refine ReachS.blockW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.region (off := macEOff) (n := seqSize macE) (by decide +kernel) hmx) hb2 vpc (by have := macEOff_even; omega) sE (by decide)
      (by simp [alignedAll, macE, Instr.accesses])
      (by
        intro e he' y ⟨a, ha, _⟩
        simp [traceAll, macE] at he'
        rcases he' with rfl | rfl | rfl <;> simp [Instr.accesses] at ha)
      ?_
    generalize hw : execAll macE v = w at e0 e2 e3 em er
    have pw : w.pc = base + BitVec.ofNat 32 (m + macBl2Off) := by
      rw [← hw, execAll_pc _ _ (by decide), vpc, ofNat_add_assoc]; rfl
    refine ReachS.blW (Pn := NoSite base) (Wr := MacWr A) (noP base Rd) (hfree.at (off := macBl2Off) (by decide +kernel) (by decide +kernel) hmx) hb2 blocksOff i2 pw (by have := macBl2Off_even; omega) bl2
      (by have := macBl2Off_fits; omega) t2 ?_
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
    have hRc : ∀ o < 16 * c.count.toNat, Rd (c.msg + BitVec.ofNat 32 o) := fun o ho => by
      have : c.count.toNat = 1 := rfl
      exact hRblk o (by omega)
    apply (Poly1305Blocks.blocks_reach_r c hv Rd x hen hlr hRc).mono (fun _ _ h => h)
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


/-- **`MAC_PADDED`**, read-policy form. -/
theorem mac_padded_r {Rd : Word → Prop} (base A d n : Word) (M : Mem) (m : Nat) (i1 i2 : BitVec 25)
    (hat : MacAt m i1 i2)
    (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hfree : MacFree m)
    (hR : ∀ o < n.toNat, Rd (d + BitVec.ofNat 32 o))
    (hRblk : ∀ o < 16, Rd (A + 72#32 + BitVec.ofNat 32 o))
    (he : MacEnv base A d n M) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 m) (h13 : s.regs 13 = A) (h4 : s.regs 4 = d)
    (h5 : s.regs 5 = n) (hmem : s.mem = M)
    (hk : keyAtOK M (A + 8#32)) (hh : accAt M (A + 8#32) < 5 * 2 ^ 128) :
    ReachS base (RdP base Rd) s (MacPost base A d n M m s) := by
  apply ReachS.bind
  apply (mac_head_r base A d n M m i1 i2 hat hm hmx hfree hR he s hpc h13 h4 h5 hmem hk hh).mono
    (fun _ _ h => h)
  intro t ht
  exact mac_tail_r base A d n M m i1 i2 hat hm hmx hfree hR hRblk he s t ht hk

end M0Crypto.Release.Aead
