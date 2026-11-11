import M0Crypto.Release.AeadMacReads
import M0Crypto.Release.AeadLengths

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read policy of the lengths block and its Poly1305 block call
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK wordAt)
open M0Crypto.Spec.Aead (p leBytes)

theorem lengths_reach_r {Rd : Word → Prop} (c : ACall) (hv : AValid c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off lengths = true) (hbl : instrAt B (off + seqSize lengths) = some (.bl i))
    (ht : blTarget (off + seqSize lengths) i = BitVec.ofNat 32 blocksOff)
    (ho : off % 2 = 0) (hox : off + seqSize lengths + blSize ≤ Artifacts.Release.size)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off) (h13 : s.regs 13 = c.A)
    (hh : Hi c s.mem) (hc : CodeAt s.mem c.base B) (ti : Mem) (msg : List M0Crypto.Spec.ChaCha20.Byte)
    (hp : PInv c.A ti msg s.mem)
    (hrg : InRegion (NoSite c.base) c.base off (seqSize lengths + blSize))
    (hR : ∀ o < 16, Rd (c.A + 72#32 + BitVec.ofNat 32 o)) :
    ReachS c.base (RdP c.base Rd) s (LengthPost c off ti msg s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have he : MacEnv c.base c.A c.base 0#32 s.mem := hv.macEnv
    (disj_mono (hv.win hv.codeS 0 320 _ (by rw [hv.lo]; omega) (by decide)) (by decide)) hc
  obtain ⟨em, e0, e1, e2, e3, er⟩ := lengths_effect s
  have hLe : seqSize lengths % 2 = 0 := by decide
  have hB := blSize_eq
  rw [h13, hh.alen, hh.len] at em
  rw [h13] at e0 e1
  apply ReachS.blockW (Pn := NoSite c.base) (Wr := MacWr c.A) (is := lengths) (noP c.base Rd) (hrg.prefix (by decide)) hb2 hpc ho hseq (by decide)
    (alignedAll_sp _ _ (sp_al (by decide)) (by rw [h13]; have := he.a8; omega))
    (by
      intro e he' y hy
      obtain ⟨o, ⟨o1, o2⟩, rfl⟩ := traceAll_writes_sp' (fun o => 72 ≤ o ∧ o < 88) lengths s
        ((spBlock_of_B (ok := fun q => q.1 == .read || (72 ≤ q.2 && q.2 + 4 ≤ 88)) (by decide)).mono
          (fun q hq => by
            simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hq
            rcases hq with h | ⟨h1, h2⟩
            · exact .inl h
            · exact .inr fun k hk => ⟨by omega, by omega⟩)) e he' y hy
      rw [h13]
      refine .inr (.inr ⟨o - 72, by omega, ?_⟩)
      rw [ofNat_add_assoc]; congr 2; omega)
  generalize hu : execAll lengths s = u at em e0 e1 e2 e3 er
  have upc : u.pc = c.base + BitVec.ofNat 32 (off + seqSize lengths) := by
    rw [← hu, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
  apply ReachS.blW (Pn := NoSite c.base) (Wr := MacWr c.A) (noP c.base Rd) (off := off + seqSize lengths) (hrg.at (a := seqSize lengths) (by decide)) hb2 blocksOff i upc (by omega) hbl (by omega) ht
  generalize hx : (u.setReg 14 ((c.base + BitVec.ofNat 32 (off + seqSize lengths + 4)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 blocksOff) = x
  have xr : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → x.regs r = u.regs r := fun r a b => by
    rw [← hx, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have xm : x.mem = lengthMem s.mem c.A c.alen c.len := by rw [← hx, setReg_mem, setReg_mem, em]
  have xM : ∀ y, ¬ MacWr c.A y → x.mem y = s.mem y := fun y hy => by
    rw [xm]; exact lengthMem_other _ _ _ _ _ (outBlk_of hy)
  have xctx : ∀ j < 64, x.mem (c.A + 8#32 + BitVec.ofNat 32 j) = s.mem (c.A + 8#32 + BitVec.ofNat 32 j) := by
    intro j hj
    rw [xm]
    apply lengthMem_other
    intro k hk e
    exact off_ne c.A (a := 8 + j) (b := 72 + k) (by omega) (by omega) (by omega) (by simpa only [ofNat_add_assoc] using e)
  have xp := hp.congr xctx
  have x14 : x.regs 14 = (c.base + BitVec.ofNat 32 (off + seqSize lengths + 4)) ||| 1#32 := by
    rw [← hx, setReg_ne _ _ _ _ (by decide), setReg_eq]
  let bc : BCtx := { base := c.base, sp0 := c.A, ctx := c.A + 8#32, msg := c.A + 72#32, count := 1#32, pad := 1#32, m0 := x.mem, regs0 := x.regs }
  have bv : BValid bc := he.bvalid 1#32 (c.A + 72#32) x.mem x.regs 1#32
    (by
      have := he.aLo; have := he.aHi
      refine ⟨?_, ?_, .inr ?_⟩
      · rw [he.blk_toNat]; show c.A.toNat + 72 + 16 * 1 ≤ 2 ^ 32; omega
      · rw [he.lo]; omega
      · rw [he.lo, he.blk_toNat]; omega)
    (he.codeAt_of xM)
  have be : BEntry bc x := ⟨rfl, rfl, by change x.regs 15 = c.base + BitVec.ofNat 32 blocksOff; rw [← hx, setReg_eq],
    by change x.regs 13 = c.A; rw [xr 13 (by decide) (by decide), er 13 (by decide) (by decide), h13],
    by change x.regs 0 = c.A + 8#32; rw [xr 0 (by decide) (by decide), e0], by change x.regs 1 = c.A + 72#32; rw [xr 1 (by decide) (by decide), e1],
    by change x.regs 2 = 1#32; rw [xr 2 (by decide) (by decide), e2], by change x.regs 3 = 1#32; rw [xr 3 (by decide) (by decide), e3]⟩
  have hlr : (bc.regs0 14).getLsbD 0 = true := by show (x.regs 14).getLsbD 0 = true; rw [x14]; exact lr_odd _
  apply (Poly1305Blocks.blocks_reach_r bc bv Rd x be hlr (by intro o ho; change o < 16 * 1 at ho; exact hR o (by omega))).mono (fun _ _ h => h)
  intro t ht'
  have tf : ∀ y, ¬ MacWr c.A y → t.mem y = s.mem y := fun y hy => by
    rw [Poly1305Blocks.result_frame bc bv x t be hlr ht' y (fun h => hy (bwr_mac c.A bc rfl rfl y h))]
    exact xM y hy
  obtain ⟨acc, bound⟩ := Poly1305Blocks.result_blocks_correct bc bv x t be ht' xp.keyOk xp.bound (by change (1#32 : Word).toNat ≤ 1; decide)
  refine ⟨?_, ht'.sp, ?_, tf, ?_⟩
  · rw [ht'.pc]; show x.regs 14 &&& ~~~1#32 = _
    rw [x14, lr_mask _ (even_off c.base hv.base4 _ (by omega)), blSize_eq]
  · intro r a b
    rw [ht'.regs r a b]; show x.regs r = _
    rw [xr r (by omega) (by omega), er r a (by omega)]
  · have ep : Poly1305Context.padAt t.mem (c.A + 8#32) = Poly1305Context.padAt s.mem (c.A + 8#32) := by
      unfold Poly1305Context.padAt
      rw [he.ctx_word tf 12 (by decide) (by decide), he.ctx_word tf 13 (by decide) (by decide),
        he.ctx_word tf 14 (by decide) (by decide), he.ctx_word tf 15 (by decide) (by decide)]
    refine ⟨(he.key_eq tf).trans hp.key, he.keyOk tf hp.keyOk, ep.trans hp.pad, ?_, bound, ?_⟩
    · change accAt t.mem (c.A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt x.mem (c.A + 8#32)) 1
        (accAt x.mem (c.A + 8#32) % p) (Ctx.bytesAt x.mem (c.A + 72#32) 16) at acc
      rw [xp.key, xp.acc, xm, lengthMem_bytes] at acc
      rw [acc]
      exact (Poly1305Spec.polyBlocks_append _ _ _ (msg.length / 16) msg _ (by have := hp.len; omega)).symm
    · have := hp.len
      simp only [List.length_append, lengthBlock, Poly1305Spec.leBytes_length]; omega

end M0Crypto.Release.Aead
