import M0Crypto.Release.AeadPoly
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! `MAC_LENGTHS`: the final RFC 8439 length block and its exact-byte blocks call. -/
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry accAt keyAt keyAtOK wordAt)
open M0Crypto.Spec.Aead (p leBytes)

theorem macWr_swr (A y : Word) (h : MacWr A y) : SWr A y := by
  rcases h with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · refine ⟨112 + o, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1; bv_omega
  · rw [ofNat_add_assoc]; exact swr_A A _ (by omega)
  · rw [ofNat_add_assoc]; exact swr_A A _ (by omega)

theorem AValid.macEnv {c : ACall} (hv : AValid c) {d n : Word} {M : Mem}
    (hd : Disj d n.toNat (c.sp0 - 320#32) 320) (hc : CodeAt M c.base B) :
    MacEnv c.base c.A d n M where
  base4 := hv.base4
  a8 := by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
  aLo := by have := hv.A_lo; omega
  aHi := by have := hv.A_hi; omega
  codeS := hv.win hv.codeS 112 208 _ (by rw [hv.sub_toNat 64 (by decide)]; have := hv.A_lo; omega) (by decide)
  dataS := hv.win hd 112 208 _ (by rw [hv.sub_toNat 64 (by decide)]; have := hv.A_lo; omega) (by decide)
  code := hc

theorem Hi.mac {c : ACall} {M M' : Mem} {d n : Word} (h : Hi c M)
    (he : MacEnv c.base c.A d n M) (hf : ∀ y, ¬ MacWr c.A y → M' y = M y) : Hi c M' :=
  h.congr fun o h1 h2 => hf _ (by
    intro hw
    obtain ⟨q, hq, eq⟩ := macWr_W hw
    have hq' : q < 208 := by rcases hq with hq | hq | hq <;> omega
    have eo : c.A + BitVec.ofNat 32 o = W c.A (64 + o) := by simpa using W_add c.A o 0
    rw [eo] at eq
    apply off_ne (c.A - 64#32) (by omega) (by omega) (by unfold MacOff at hq; omega) eq)

/-- A 32-bit length followed by a zero word is its 64-bit little-endian encoding. -/
theorem bytesAt_le64 (m : Mem) (a w : Word) (h0 : read32 m a = w)
    (h1 : read32 m (a + 4#32) = 0#32) : Ctx.bytesAt m a 8 = leBytes 8 w.toNat := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 8
  · rw [ChaCha20Output.bytesAt_get _ _ _ _ hj, Poly1305Spec.leBytes_get _ _ _ hj]
    congr 1
    by_cases h4 : j < 4
    · rw [byte_of_read32 m a j h4, h0]
      exact Poly1305Finish.word_byte_nat w j h4
    · have ej : a + BitVec.ofNat 32 j = a + 4#32 + BitVec.ofNat 32 (j - 4) := by
        rw [ofNat_add_assoc]; congr 2; omega
      rw [ej, byte_of_read32 m (a + 4#32) (j - 4) (by omega), h1]
      have hw := w.isLt
      have hp : 2 ^ 32 ≤ 256 ^ j := by
        rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl <;> decide
      rw [Nat.div_eq_of_lt (by omega)]; simp
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega),
      List.getElem?_eq_none (by rw [Poly1305Spec.leBytes_length]; omega)]

def lengthMem (m : Mem) (A alen len : Word) : Mem :=
  write32 (write32 (write32 (write32 m (A + 72#32) alen) (A + 80#32) len) (A + 76#32) 0#32)
    (A + 84#32) 0#32

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3

theorem lengths_effect (s : State) :
    (execAll lengths s).mem = lengthMem s.mem (s.regs 13)
      (read32 s.mem (s.regs 13 + 148#32)) (read32 s.mem (s.regs 13 + 116#32)) ∧
    (execAll lengths s).regs 0 = s.regs 13 + 8#32 ∧
    (execAll lengths s).regs 1 = s.regs 13 + 72#32 ∧
    (execAll lengths s).regs 2 = 1#32 ∧ (execAll lengths s).regs 3 = 1#32 ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → (execAll lengths s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h4 h15 => execAll_regs_other _ _ r h15
    (by
      have h0 : r.val ≠ 0 := by omega
      have h1 : r.val ≠ 1 := by omega
      have h2 : r.val ≠ 2 := by omega
      have h3 : r.val ≠ 3 := by omega
      simp [lengths, Instr.dsts, Fin.ext_iff, h0, h1, h2, h3]; omega)⟩ <;>
    simp (config := { maxSteps := 1000000 }) [lengths, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, lengthMem,
      rd_wr_ne _ _ _ 72 116 (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem lengthMem_words (m : Mem) (A alen len : Word) (j : Nat) (hj : j < 4) :
    read32 (lengthMem m A alen len) (A + BitVec.ofNat 32 (72 + 4*j)) =
      [alen, 0#32, len, 0#32][j]'(by simp; omega) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [lengthMem, Nat.reduceMul, Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals repeat first
    | rw [rd_wr_ne _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    | rw [M0Crypto.Armv6M.read32_write32_same]

theorem lengthMem_bytes (m : Mem) (A alen len : Word) :
    Ctx.bytesAt (lengthMem m A alen len) (A + 72#32) 16 = leBytes 8 alen.toNat ++ leBytes 8 len.toNat := by
  rw [show (16 : Nat) = 8 + 8 from rfl, Poly1305Spec.bytesAt_add]
  congr 1
  · apply bytesAt_le64
    · exact lengthMem_words m A alen len 0 (by decide)
    · rw [ofNat_add_assoc]; exact lengthMem_words m A alen len 1 (by decide)
  · rw [ofNat_add_assoc]
    apply bytesAt_le64
    · exact lengthMem_words m A alen len 2 (by decide)
    · rw [ofNat_add_assoc]; exact lengthMem_words m A alen len 3 (by decide)

theorem lengthMem_other (m : Mem) (A alen len y : Word) (hy : OutBlk A y) :
    lengthMem m A alen len y = m y := by
  unfold lengthMem
  have w (a : Nat) (ha : 72 ≤ a) (hb : a + 4 ≤ 88) (m' : Mem) (v : Word) :
      write32 m' (A + BitVec.ofNat 32 a) v y = m' y :=
    write32_other' _ _ _ _ (fun k hk => by
      have := hy (a - 72 + k) (by omega)
      simpa only [ofNat_add_assoc, show 72 + (a - 72 + k) = a + k by omega] using this)
  rw [w 84 (by decide) (by decide), w 76 (by decide) (by decide),
    w 80 (by decide) (by decide), w 72 (by decide) (by decide)]

/-- The last, always-present, 16-byte AEAD MAC block. -/
def lengthBlock (c : ACall) : List M0Crypto.Spec.ChaCha20.Byte :=
  leBytes 8 c.alen.toNat ++ leBytes 8 c.len.toNat

structure LengthPost (c : ACall) (off : Nat) (ti : Mem) (msg : List M0Crypto.Spec.ChaCha20.Byte)
    (s t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 (off + seqSize lengths + blSize)
  sp : t.regs 13 = c.A
  hi : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = s.regs r
  frame : ∀ y, ¬ MacWr c.A y → t.mem y = s.mem y
  inv : PInv c.A ti (msg ++ lengthBlock c) t.mem

theorem lengths_reach (c : ACall) (hv : AValid c) (off : Nat) (i : BitVec 25)
    (hseq : seqAt B off lengths = true) (hbl : instrAt B (off + seqSize lengths) = some (.bl i))
    (ht : blTarget (off + seqSize lengths) i = BitVec.ofNat 32 blocksOff)
    (ho : off % 2 = 0) (hox : off + seqSize lengths + blSize ≤ Artifacts.Release.size)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off) (h13 : s.regs 13 = c.A)
    (hh : Hi c s.mem) (hc : CodeAt s.mem c.base B) (ti : Mem) (msg : List M0Crypto.Spec.ChaCha20.Byte)
    (hp : PInv c.A ti msg s.mem) :
    Reach c.base (MacWr c.A) s (LengthPost c off ti msg s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have he : MacEnv c.base c.A c.base 0#32 s.mem := hv.macEnv
    (disj_mono (hv.win hv.codeS 0 320 _ (by rw [hv.lo]; omega) (by decide)) (by decide)) hc
  obtain ⟨em, e0, e1, e2, e3, er⟩ := lengths_effect s
  have hLe : seqSize lengths % 2 = 0 := by decide
  have hB := blSize_eq
  rw [h13, hh.alen, hh.len] at em
  rw [h13] at e0 e1
  apply Reach.block hb2 lengths off hpc ho hseq (by decide)
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
  apply Reach.bl hb2 (off + seqSize lengths) blocksOff i upc (by omega) hbl (by omega) ht
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
  apply ((Poly1305Blocks.blocks_reach bc bv x be hlr).monoW (bwr_mac c.A bc rfl rfl)).mono
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
