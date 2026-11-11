import M0Crypto.Release.ChaCha20Block
import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.AccessReach
import M0Crypto.Sym.MemBridge
import M0Crypto.Thumb.SeqScan

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
Byte-level facts for the two output paths of `m0c_chacha20_xor`: the expected output
byte `n` is input byte `n` xor byte `n % 4` of keystream word `(n % 64) / 4` of block
`n / 64`; input bytes at or above the output prefix are still the caller's bytes; a
byte or word store of expected bytes at the prefix extends the prefix.
-/

namespace M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Block (ks block_keystream)
open M0Crypto.Spec.ChaCha20 (bytesOfWord block)
open M0Crypto.Release.ChaCha20Layout (postOff cmpEOff blo2Off dispOff bne2Off achOff achSize
  bchOff bchSize bmidOff blOff bloOff n1Off b38eOff slotX slotJ slotInp slotOutp slotLen)

/-- Stride arithmetic for the unrolled `ach` and `bch` sequences. -/
theorem off_step (base s i : Nat) : base + s * i + s = base + s * (i + 1) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]

theorem ach_size (i : Nat) : seqSize (ach i) = achSize := rfl
theorem bch_size (i : Nat) : seqSize (bch i) = bchSize := rfl
theorem achOff_even : achOff % 2 = 0 := by decide
theorem achSize_even : achSize % 2 = 0 := by decide
theorem bchOff_even : bchOff % 2 = 0 := by decide
theorem bchSize_even : bchSize % 2 = 0 := by decide
theorem ach_pc_even (i : Nat) : (achOff + achSize * i) % 2 = 0 := by
  rw [Nat.add_mod, achOff_even, Nat.mul_mod, achSize_even]; simp
theorem bch_pc_even (i : Nat) : (bchOff + bchSize * i) % 2 = 0 := by
  rw [Nat.add_mod, bchOff_even, Nat.mul_mod, bchSize_even]; simp
theorem ach_end : achOff + achSize * 16 = b38eOff := by decide

theorem bytesOfWord_get (w : Word) (q : Nat) (hq : q < 4) :
    (bytesOfWord w)[q]? = some (w.extractLsb' (8 * q) 8) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Keystream byte `p` (< 64) of block `k`. -/
def kb (c : Ctx) (k p : Nat) : BitVec 8 := (ks c k (p / 4)).extractLsb' (8 * (p % 4)) 8

theorem msg_length (c : Ctx) : c.msg.length = c.len.toNat := bytesAt_length _ _ _

/-- **Expected output byte** `n`: input byte xor keystream byte (RFC 8439 §2.4). -/
theorem output_byte_eq (c : Ctx) (n : Nat) (hn : n < c.len.toNat) :
    c.outB n = c.m0 (c.inp + BitVec.ofNat 32 n) ^^^ kb c (n / 64) (n % 64) := by
  have hl : n < c.msg.length := by rw [msg_length]; exact hn
  have h := ChaCha20Spec.chacha20_get c.keyB c.nonceB c.msg c.ctr.toNat n hl
  have hlen : n < (M0Crypto.Spec.Aead.chacha20 c.keyB c.ctr.toNat c.nonceB c.msg).length := by
    rw [ChaCha20Spec.chacha20_length]; exact hl
  have hctr : BitVec.ofNat 32 (c.ctr.toNat + n / 64) = c.ctr + BitVec.ofNat 32 (n / 64) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have hb := block_keystream c (n / 64) (n % 64) (Nat.mod_lt _ (by decide))
  have hm : c.msg[n] = c.m0 (c.inp + BitVec.ofNat 32 n) := by
    have := bytesAt_get c.m0 c.inp c.len.toNat n hn
    rw [List.getElem?_eq_getElem (by rw [bytesAt_length]; exact hn)] at this
    exact Option.some.inj this
  unfold Ctx.outB
  rw [getElem!_pos _ n hlen]
  rw [List.getElem?_eq_getElem hlen] at h
  rw [Option.some.inj h, hm]
  congr 1
  have hb' := hb
  rw [← hctr, List.getElem?_eq_getElem (by rw [M0Crypto.Spec.ChaCha20.block_length]; omega),
    bytesOfWord_get _ _ (Nat.mod_lt _ (by decide))] at hb'
  rw [Option.some.inj hb']; rfl


/-- An input byte at or above the output prefix is still the caller's byte. -/
theorem inp_mem (c : Ctx) (hv : Valid c) {P : Nat} {m : Mem} (h : c.MemOk P m) (n : Nat) (hP : P ≤ n)
    (hn : n < c.len.toNat) : m (c.inp + BitVec.ofNat 32 n) = c.m0 (c.inp + BitVec.ofNat 32 n) := by
  obtain ⟨hf, hs⟩ := ChaCha20Init.disj_out c hv hv.inF n hn
  apply ChaCha20Init.mem_m0 c h _ hf _ hs
  rcases hv.inOut with he | ⟨h1, h2, h3⟩
  · rw [Ctx.oidx, he, sub_ofNat_toNat _ _ (by omega)]; omega
  · intro hlt
    have e := eq_add_sub c.out (c.inp + BitVec.ofNat 32 n)
    exact ne_of_disj (j := c.oidx (c.inp + BitVec.ofNat 32 n)) h1 h2 h3 hn (by omega) e

theorem oidx_out (c : Ctx) (hv : Valid c) (i : Nat) (hi : i < c.len.toNat) :
    c.oidx (c.out + BitVec.ofNat 32 i) = i := by
  have := hv.outF.1
  rw [Ctx.oidx, sub_ofNat_toNat _ _ (by omega)]

theorem oidx_ne (c : Ctx) {y : Word} {i : Nat} (hy : y ≠ c.out + BitVec.ofNat 32 i) : c.oidx y ≠ i := by
  intro e; apply hy; rw [← e]; exact eq_add_sub c.out y

/-- A byte store of the expected byte at the prefix extends the prefix. -/
theorem memOk_write8 (c : Ctx) (hv : Valid c) {P : Nat} {m : Mem} (h : c.MemOk P m) (hP : P < c.len.toNat)
    (v : Word) (hb : v.extractLsb' 0 8 = c.outB P) :
    c.MemOk (P + 1) (write8 m (c.out + BitVec.ofNat 32 P) v) := by
  intro y hy
  unfold write8
  by_cases e : y = c.out + BitVec.ofNat 32 P
  · rw [if_pos e, e, oidx_out c hv P hP, if_pos (by omega), hb]
  · rw [if_neg e, h y hy]
    have := oidx_ne c e
    by_cases hl : c.oidx y < P
    · rw [if_pos hl, if_pos (by omega)]
    · rw [if_neg hl, if_neg (by omega)]

/-- A word store of four expected bytes at the prefix extends the prefix by 4. -/
theorem memOk_write32 (c : Ctx) (hv : Valid c) {P : Nat} {m : Mem} (h : c.MemOk P m)
    (hP : P + 4 ≤ c.len.toNat) (v : Word) (hb : ∀ q < 4, v.extractLsb' (8 * q) 8 = c.outB (P + q)) :
    c.MemOk (P + 4) (write32 m (c.out + BitVec.ofNat 32 P) v) := by
  intro y hy
  have ad : ∀ q, c.out + BitVec.ofNat 32 P + BitVec.ofNat 32 q = c.out + BitVec.ofNat 32 (P + q) :=
    fun q => ofNat_add_assoc _ _ _
  unfold write32
  by_cases e0 : y = c.out + BitVec.ofNat 32 P
  · rw [if_pos e0, e0, oidx_out c hv P (by omega), if_pos (by omega)]; exact hb 0 (by omega)
  rw [if_neg e0]
  by_cases e1 : y = c.out + BitVec.ofNat 32 P + 1#32
  · rw [if_pos e1, e1, ad 1, oidx_out c hv _ (by omega), if_pos (by omega)]; exact hb 1 (by omega)
  rw [if_neg e1]
  by_cases e2 : y = c.out + BitVec.ofNat 32 P + 2#32
  · rw [if_pos e2, e2, ad 2, oidx_out c hv _ (by omega), if_pos (by omega)]; exact hb 2 (by omega)
  rw [if_neg e2]
  by_cases e3 : y = c.out + BitVec.ofNat 32 P + 3#32
  · rw [if_pos e3, e3, ad 3, oidx_out c hv _ (by omega), if_pos (by omega)]; exact hb 3 (by omega)
  rw [if_neg e3, h y hy]
  have n0 := oidx_ne c e0
  have n1 := oidx_ne c (i := P + 1) (by rw [← ad 1]; exact e1)
  have n2 := oidx_ne c (i := P + 2) (by rw [← ad 2]; exact e2)
  have n3 := oidx_ne c (i := P + 3) (by rw [← ad 3]; exact e3)
  by_cases hl : c.oidx y < P
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl, if_neg (by omega)]

/-- Output stores leave the frame words alone. -/
theorem out_ne_slot (c : Ctx) (hv : Valid c) (i j q : Nat) (hi : i < c.len.toNat) (hj : j < ChaCha20Layout.chCallWords) (hq : q < 4) :
    slot c.fp j + BitVec.ofNat 32 q ≠ c.out + BitVec.ofNat 32 i := by
  obtain ⟨h1, h2, h3⟩ := hv.outF
  have := ne_of_disj h1 h2 h3 hi (show 4 * j + q < 184 by have := ChaCha20Layout.chCallWords_eq; omega)
  intro e; apply this; rw [← e]; simp only [slot, ofNat_add_assoc]

theorem read32_write8_out (c : Ctx) (hv : Valid c) (m : Mem) (i j : Nat) (v : Word) (hi : i < c.len.toNat)
    (hj : j < ChaCha20Layout.chCallWords) : read32 (write8 m (c.out + BitVec.ofNat 32 i) v) (slot c.fp j) = read32 m (slot c.fp j) := by
  apply read32_congr
  intro q hq
  simp only [write8]
  rw [if_neg (out_ne_slot c hv i j q hi hj hq)]

theorem read32_write32_out (c : Ctx) (hv : Valid c) (m : Mem) (i j : Nat) (v : Word) (hi : i + 4 ≤ c.len.toNat)
    (hj : j < ChaCha20Layout.chCallWords) : read32 (write32 m (c.out + BitVec.ofNat 32 i) v) (slot c.fp j) = read32 m (slot c.fp j) := by
  apply read32_congr
  intro q hq
  rw [M0Crypto.Armv6M.write32_other]
  intro p hp e
  rw [ofNat_add_assoc] at e
  exact out_ne_slot c hv (i + p) j q (by omega) hj hq e

/-! ## After the rounds: `postOff` to `cmpEOff` -/

theorem post_at : seqAt B postOff post = true := by decide

theorem post_effect (t : State) (sp : Word) (h13 : t.regs 13 = sp) :
    let u := execAll post t
    u.regs 13 = sp ∧ u.regs 2 = read32 t.mem (slot sp 34) ∧ u.regs 3 = read32 t.mem (slot sp 33) ∧
    u.regs 4 = read32 t.mem (slot sp 32) ∧
    u.mem = write32 (write32 (write32 (write32 (write32 t.mem (slot sp 2) (t.regs 0)) (slot sp 12) (t.regs 8))
      (slot sp 13) (t.regs 9)) (slot sp 14) (t.regs 10)) (slot sp 15) (t.regs 11) := by
  refine ⟨(execAll_regs_other post t 13 (by decide) (by decide)).trans h13, ?_⟩
  all_goals
    simp only [post, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3,
      M0Crypto.Proofs.toReg_4, slotInp, slotOutp, slotLen, slotX]
    simp (config := { decide := true }) only [ite_true, ite_false, h13]
  all_goals first | rfl | simp [slot]

open M0Crypto.Proofs.ChaCha20DoubleRound (innerBlockF)

/-- State at offset `cmpEOff` (the end of the `post` piece) of block `k`: `x` in slots 0..15,
`j` in 16..31, the pointers and the remaining length in r2-r4. -/
structure Post (c : Ctx) (k : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 cmpEOff
  sp : t.regs 13 = c.fp
  r2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)
  r3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k)
  r4 : t.regs 4 = c.len - BitVec.ofNat 32 (64 * k)
  x : ∀ i < 16, c.fw t i = ChaCha20Loop.iter innerBlockF 10 (c.J k) i
  j : ∀ i < 16, c.fw t (slotJ + i) = c.J k i
  len : c.fw t slotLen = c.len - BitVec.ofNat 32 (64 * k)
  outp : c.fw t slotOutp = c.out + BitVec.ofNat 32 (64 * k)
  inp : c.fw t slotInp = c.inp + BitVec.ofNat 32 (64 * k)
  mem : c.MemOk (64 * k) t.mem
  lt : 64 * k < c.len.toNat
  ok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true

theorem read32_w_slot (m : Mem) (sp v : Word) (a j : Nat) (ha : a < 64) (hj : j < 64) :
    read32 (write32 m (slot sp a) v) (slot sp j) = if a = j then v else read32 m (slot sp j) :=
  read32_write32_slot' m sp v a j (by omega) (by omega)

/-- **Rounds and spill**: from `BlockInv c k` to `Post c k`. -/
theorem bpost_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : BlockInv c k t) (allowed : Word → Kind → Word → Prop)
    (hround : ReachS c.base (ChaCha20Policy.EvP Pc allowed) t (fun v =>
      v.pc = c.base + BitVec.ofNat 32 postOff ∧ v.regs 13 = c.fp ∧
      ChaCha20Round.view (some 2) v = ChaCha20Loop.iter innerBlockF 10 (c.J k) ∧
      (∀ j, 12 ≤ j → j < 64 → c.fw v j = c.fw t j) ∧ c.MemOk (64 * k) v.mem))
    (hpost : ∀ v : State, v.pc = c.base + BitVec.ofNat 32 postOff → v.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll post v)) (Q : State → Prop)
    (cont : ∀ u, Post c k u → ReachS c.base (ChaCha20Policy.EvP Pc allowed) u Q) : ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have sJ : slotJ = 16 := by decide
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  apply ReachS.bind
  apply hround.mono (fun _ _ h => h)
  rintro v ⟨vpc, vsp, vview, vfw, vmem⟩
  apply ChaCha20Policy.blockP hPc hb2 post postOff vpc (by decide) post_at (by decide)
    (alignedAll_sp post v (spBlock_of_B (ok := fun p => p.2 % 4 == 0) (by decide) |>.mono
      (fun p hp => by simpa using hp)) (by rw [vsp]; exact ChaCha20Setup.fp4 hv))
    (hpost v vpc vsp) (by decide +kernel)
  obtain ⟨u13, u2, u3, u4, um⟩ := post_effect v c.fp vsp
  have rd : ∀ j, j < 64 → read32 (execAll post v).mem (slot c.fp j) =
      if 15 = j then v.regs 11 else if 14 = j then v.regs 10 else if 13 = j then v.regs 9 else
      if 12 = j then v.regs 8 else if 2 = j then v.regs 0 else read32 v.mem (slot c.fp j) := fun j hj => by
    rw [um]; simp (disch := omega) only [read32_w_slot]
  have vf : ∀ j, 16 ≤ j → j < 64 → c.fw (execAll post v) j = c.fw t j := fun j h1 h2 => by
    rw [← vfw j (by omega) h2]
    show read32 _ _ = _
    rw [rd j h2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; rfl
  have vw : ∀ i, (i < 16) → c.fw (execAll post v) i = ChaCha20Loop.iter innerBlockF 10 (c.J k) i := by
    intro i hi
    rw [← vview]
    show read32 _ _ = _
    rw [rd i (by omega)]
    unfold ChaCha20Round.view
    by_cases h12 : i < 12
    · rw [if_pos h12, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      by_cases h2 : i = 2
      · subst h2; rfl
      · rw [if_neg (Ne.symm h2), if_neg (fun e => h2 (Option.some.inj e).symm), vsp]
    · rw [if_neg h12, if_pos hi]
      have : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rfl
  apply cont
  refine ⟨?_, u13, ?_, ?_, ?_, vw, fun i hi => (vf (slotJ + i) (by omega) (by omega)).trans (h.j i hi),
    (vf 32 (by omega) (by omega)).trans h.len, (vf 33 (by omega) (by omega)).trans h.outp,
    (vf 34 (by omega) (by omega)).trans h.inp, ?_, h.lt, h.ok⟩
  · rw [execAll_pc _ _ (by decide), vpc, ofNat_add_assoc]; rfl
  · rw [u2, ← h.inp]; exact (vfw 34 (by omega) (by omega))
  · rw [u3, ← h.outp]; exact (vfw 33 (by omega) (by omega))
  · rw [u4, ← h.len]; exact (vfw 32 (by omega) (by omega))
  · rw [um]
    exact c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot
      (c.memOk_write_slot vmem _ (by omega) _) _ (by omega) _) _ (by omega) _) _ (by omega) _) _ (by omega) _


theorem bpost_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : BlockInv c k t) (Q : State → Prop)
    (cont : ∀ u, Post c k u → ReachW c.base Pc c.Wr u Q) : ReachW c.base Pc c.Wr t Q := by
  apply ChaCha20Policy.ofEvPW
  apply bpost_S c hv hPc k t h (writeOnlyPolicy c.Wr) ?_ ?_ Q ?_
  · exact ChaCha20Policy.reachW_toEvP (ChaCha20Block.bround_w c hv hPc k t h _
      (fun v vp vs vv vf vm => ReachS.done ⟨vp, vs, vv, vf, vm⟩))
  · intro v vp vs
    apply WritesTo.toEventAccesses
    intro e he y hy
    exact ChaCha20Setup.wr_frame (by
      have := frameWB_writes (n := 35) post v (by decide) e he y hy
      rwa [vs] at this) (by have := ChaCha20Layout.chStackWords_eq; omega)
  · intro u hu
    exact ChaCha20Policy.reachW_toEvP (cont u hu)

theorem block_post (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) (Q : State → Prop)
    (cont : ∀ u, Post c k u → Reach c.base c.Wr u Q) : Reach c.base c.Wr t Q := by
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine bpost_w c hv (fun _ _ => trivial) k t h Q ?_
  intro u hu
  exact (cont u hu).toReachW

/-- The block's setup, rounds and spill access memory only before output. -/
theorem bpost_before_output {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State)
    (h : BlockInv c k t) :
    ReachS c.base (ChaCha20Policy.EvP Pc (fun pc kind y => PCBetween c.base ChaCha20Layout.bpreOff ChaCha20Layout.achOff pc ∧ writeOnlyPolicy c.Wr pc kind y)) t (Post c k) := by
  apply bpost_S c hv hPc k t h (fun pc kind y => PCBetween c.base ChaCha20Layout.bpreOff ChaCha20Layout.achOff pc ∧ writeOnlyPolicy c.Wr pc kind y)
    (ChaCha20Block.bround_before_output c hv hPc k t h)
  · intro v hp hs
    apply EventAccessesTo.and (traceAll_pcBetween c.base ChaCha20Layout.bpreOff ChaCha20Layout.achOff postOff post v (by decide) hp (by decide +kernel) (by decide +kernel))
    apply WritesTo.toEventAccesses
    intro e he y hy
    exact ChaCha20Setup.wr_frame (by
      have := frameWB_writes (n := 35) post v (by decide) e he y hy
      rwa [hs] at this) (by have := ChaCha20Layout.chStackWords_eq; omega)
  · intro u hu
    exact ReachS.done hu

/-! ## Aligned path: `achOff` to `b38eOff` -/

theorem sub_carry (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).2.1 = decide (y.toNat ≤ x.toNat) := by
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := x.isLt; have := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not, Decidable.not_not]; omega

theorem ach_at : (List.range 16).all (fun i => seqAt B (achOff + achSize * i) (ach i)) = true := by
  simp only [seqAt_eq_scan]; cbv

theorem ach_falls (i : Nat) : (ach i).all Instr.falls = true := by simp [ach, Instr.falls]

/-- Symbolic memory of `ach i` from the unknown initial state (checker form): one store of
`(sp[i] + sp[16 + i]) ^ r2[i]` to `r3 + 4i`, the sum in the carry-free `awc` form. -/
def achMemS (i : Nat) : M0Crypto.Sym.SMem :=
  .w32 .mem0 (.add (.reg0 3) (.const (BitVec.ofNat 32 (4 * i))))
    (.xor (.awc (.ld32 .mem0 (.add (.reg0 13) (.const (BitVec.ofNat 32 (4 * i)))))
        (.ld32 .mem0 (.add (.reg0 13) (.const (BitVec.ofNat 32 (4 * (slotJ + i)))))) (.const false))
      (.ld32 .mem0 (.add (.reg0 2) (.const (BitVec.ofNat 32 (4 * i))))))

/-- The kernel computes the symbolic memory of every `ach i`, `i < 16`. -/
theorem ach_mem_sym : ∀ i ∈ List.range 16,
    (M0Crypto.Sym.symExec (ach i) (M0Crypto.Sym.SState.initK [])).mem = achMemS i := by decide

/-- The kernel computes the symbolic registers of every `ach i`: only r0 and r1 change. -/
theorem ach_regs_sym : ∀ i ∈ List.range 16, ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 →
    (M0Crypto.Sym.symExec (ach i) (M0Crypto.Sym.SState.initK [])).regs r =
      M0Crypto.Sym.SExpr.reg0 r := by decide

theorem ach_effect (t : State) (i : Nat) (hi : i < 16) :
    let u := execAll (ach i) t
    u.mem = write32 t.mem (t.regs 3 + BitVec.ofNat 32 (4 * i))
      ((read32 t.mem (slot (t.regs 13) i) + read32 t.mem (slot (t.regs 13) (slotJ + i))) ^^^
        read32 t.mem (t.regs 2 + BitVec.ofNat 32 (4 * i))) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → u.regs r = t.regs r) := by
  have hk : ∀ p ∈ ([] : List (Reg × Word)), t.regs p.1 = p.2 := by simp
  have hm := M0Crypto.Sym.mem_execAll_normK (ach i) (ach_falls i) [] t hk
  rw [ach_mem_sym i (List.mem_range.mpr hi)] at hm
  dsimp only
  refine ⟨?_, fun r h0 h1 h15 => ?_⟩
  · rw [hm]
    simp only [achMemS, M0Crypto.Sym.SMem.denote, M0Crypto.Sym.SExpr.denote,
      M0Crypto.Sym.SBool.denote, add_flags, slot]
  · rw [M0Crypto.Sym.execAll_regs_normK (ach i) (ach_falls i) [] t hk r,
      ach_regs_sym i (List.mem_range.mpr hi) r h0 h1 h15]
    rfl

theorem ach_seq (i : Nat) (hi : i < 16) : seqAt B (achOff + achSize * i) (ach i) = true :=
  List.all_eq_true.mp ach_at i (List.mem_range.mpr hi)

theorem ach_aligned (t : State) (i : Nat) (hi : i < 16) (h13 : (t.regs 13).toNat % 4 = 0)
    (h2 : (t.regs 2).toNat % 4 = 0) (h3 : (t.regs 3).toNat % 4 = 0) : alignedAll (ach i) t = true := by
  have h8 : (BitVec.ofNat 8 (slotX + i)).toNat = i := by simp [slotX]; omega
  have h8' : (BitVec.ofNat 8 (slotJ + i)).toNat = slotJ + i := by simp [slotJ]; omega
  have h5 : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  generalize hs1 : (Instr.ldrSp 0 (BitVec.ofNat 8 (slotX + i))).next t = s1
  generalize hs2 : (Instr.ldrSp 1 (BitVec.ofNat 8 (slotJ + i))).next s1 = s2
  generalize hs3 : (Instr.addReg 0 0 1).next s2 = s3
  generalize hs4 : (Instr.memImm .ldr 1 2 (BitVec.ofNat 5 i)).next s3 = s4
  generalize hs5 : (Instr.dp .eors 0 1).next s4 = s5
  have e1 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → s5.regs r = t.regs r := fun r h0 h1 h15 => by
    rw [← hs5, ← hs4, ← hs3, ← hs2, ← hs1]
    simp (disch := simp [Instr.dsts, MemOp.isLoad, Fin.ext_iff, h0, h1, h15]) only [next_regs_other]
  have e13 : s1.regs 13 = t.regs 13 := by rw [← hs1]; exact next_regs_other t 13 (by decide) (by simp [Instr.dsts])
  have e3 : s3.regs 2 = t.regs 2 := by
    rw [← hs3, ← hs2, ← hs1]
    simp (disch := simp [Instr.dsts, MemOp.isLoad]) only [next_regs_other]
  have e5 : s5.regs 3 = t.regs 3 := e1 3 (by decide) (by decide) (by decide)
  simp only [alignedAll, ach, hs1, hs2, hs3, hs4, hs5, Instr.accesses, M0Crypto.Armv6M.State.reg,
    M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, h8, h8', h5, MemOp.width,
    MemOp.isLoad, e13, e3, e5]
  simp only [List.all_cons, List.all_nil, Access.aligned, Bool.and_true, beq_iff_eq, Bool.and_eq_true,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.true_and, decide_eq_true_eq]
  omega

theorem ach_writes (t : State) (i : Nat) (hi : i < 16) :
    ∀ e ∈ traceAll (ach i) t, ∀ y, Writes e.accesses y →
      ∃ q < 4, y = t.regs 3 + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q := by
  have h5 : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  intro e he y ⟨a, ha, hw, q, hq, hy⟩
  simp only [traceAll, ach, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hw)
  refine ⟨q, by simpa [MemOp.width] using hq, ?_⟩
  rw [hy]
  try simp only [M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_3, MemOp.width]
  rw [Nat.mod_eq_of_lt (by omega : i < 32), Nat.mul_comm i 4]
  rw [show ((Instr.dp DpOp.eors 0 1).next ((Instr.memImm MemOp.ldr 1 2 (BitVec.ofNat 5 i)).next
      ((Instr.addReg 0 0 1).next ((Instr.ldrSp 1 (BitVec.ofNat 8 (slotJ + i))).next
      ((Instr.ldrSp 0 (BitVec.ofNat 8 (slotX + i))).next t))))).regs 3 = t.regs 3 from
    execAll_regs_other [.ldrSp 0 (BitVec.ofNat 8 (slotX + i)), .ldrSp 1 (BitVec.ofNat 8 (slotJ + i)), .addReg 0 0 1,
      .memImm .ldr 1 2 (BitVec.ofNat 5 i), .dp .eors 0 1] t 3 (by decide) (by simp [Instr.dsts, MemOp.isLoad]; decide)]

/-- The aligned output macro obeys the functional write policy. -/
theorem ach_write_policy (c : Ctx) (hv : Valid c) (k i : Nat) (hi : i < 16)
    (t : State) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (hlen : 64 * k + 64 ≤ c.len.toNat) :
    EventAccessesTo (writeOnlyPolicy c.Wr) (traceAll (ach i) t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read => exact Or.inl rfl
  | write =>
    right
    obtain ⟨j, hj, hy⟩ := ach_writes t i hi e he _ ⟨a, ha, hk, q, hq, rfl⟩
    refine .inr ?_
    rw [hy, h3, ofNat_add_assoc, ofNat_add_assoc, oidx_out c hv _ (by omega)]
    omega

theorem ach_in (i : Nat) (hi : i < 16) : achOff + achSize * i + seqSize (ach i) ≤ ChaCha20Policy.chaEnd := by
  rw [ach_size, off_step]
  have h1 : achSize * (i + 1) ≤ achSize * 16 := Nat.mul_le_mul_left _ (by omega)
  have h2 := ach_end
  have h3 : b38eOff ≤ ChaCha20Policy.chaEnd := by decide +kernel
  omega

/-- One aligned output word. -/
theorem achunk_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k i : Nat) (hi : i < 16) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i)) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (a2 : (t.regs 2).toNat % 4 = 0) (a3 : (t.regs 3).toNat % 4 = 0)
    (hx : c.fw t i + c.fw t (slotJ + i) = ChaCha20Block.ks c k i) (hlen : 64 * k + 64 ≤ c.len.toNat)
    (hm : c.MemOk (64 * k + 4 * i) t.mem)
    (allowed : Word → Kind → Word → Prop)
    (hacc : EventAccessesTo allowed (traceAll (ach i) t)) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (achOff + achSize * (i + 1)) →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 4 * (i + 1)) t'.mem → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) :
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ChaCha20Policy.blockP hPc hb2 (ach i) _ hpc (ach_pc_even i) (ach_seq i hi) (ach_falls i)
    (ach_aligned t i hi (by rw [h13]; exact ChaCha20Setup.fp4 hv) a2 a3)
    hacc (ach_in i hi)
  obtain ⟨em, er⟩ := ach_effect t i hi
  apply cont _ (by rw [execAll_pc _ _ (ach_falls i), hpc, ofNat_add_assoc, ach_size, off_step]) er
  · intro j hj
    show read32 _ _ = _
    rw [em, h3, ofNat_add_assoc, read32_write32_out c hv _ _ _ _ (by omega) hj]; rfl
  · rw [em, h3, ofNat_add_assoc]
    apply memOk_write32 c hv hm (by omega)
    intro q hq
    have hin : t.mem (c.inp + BitVec.ofNat 32 (64 * k + 4 * i + q)) = c.m0 (c.inp + BitVec.ofNat 32 (64 * k + 4 * i + q)) :=
      inp_mem c hv hm _ (by omega) (by omega)
    rw [output_byte_eq c _ (by omega), BitVec.extractLsb'_xor, h2, ofNat_add_assoc, ← byte_of_read32 _ _ _ hq,
      ofNat_add_assoc c.inp (64 * k + 4 * i) q, hin, h13, BitVec.xor_comm]
    congr 1
    have e1 : (64 * k + 4 * i + q) / 64 = k := by omega
    have e2 : (64 * k + 4 * i + q) % 64 / 4 = i := by omega
    have e3 : (64 * k + 4 * i + q) % 64 % 4 = q := by omega
    rw [kb, e1, e2, e3, ← hx]; rfl


theorem achunk_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k i : Nat) (hi : i < 16) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i)) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (a2 : (t.regs 2).toNat % 4 = 0) (a3 : (t.regs 3).toNat % 4 = 0)
    (hx : c.fw t i + c.fw t (slotJ + i) = ChaCha20Block.ks c k i) (hlen : 64 * k + 64 ≤ c.len.toNat)
    (hm : c.MemOk (64 * k + 4 * i) t.mem) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (achOff + achSize * (i + 1)) →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 4 * (i + 1)) t'.mem → ReachW c.base Pc c.Wr t' Q) :
    ReachW c.base Pc c.Wr t Q := by
  apply ChaCha20Policy.ofEvPW
  apply achunk_S c hv hPc k i hi t hpc h13 h2 h3 a2 a3 hx hlen hm (writeOnlyPolicy c.Wr) ?_ Q ?_
  · exact ach_write_policy c hv k i hi t h3 hlen
  · intro t' hp hr hf hm'
    exact ChaCha20Policy.reachW_toEvP (cont t' hp hr hf hm')

theorem achunk (c : Ctx) (hv : Valid c) (k i : Nat) (hi : i < 16) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i)) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (a2 : (t.regs 2).toNat % 4 = 0) (a3 : (t.regs 3).toNat % 4 = 0)
    (hx : c.fw t i + c.fw t (slotJ + i) = ChaCha20Block.ks c k i) (hlen : 64 * k + 64 ≤ c.len.toNat)
    (hm : c.MemOk (64 * k + 4 * i) t.mem) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (achOff + achSize * (i + 1)) →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 4 * (i + 1)) t'.mem → Reach c.base c.Wr t' Q) :
    Reach c.base c.Wr t Q := by
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine achunk_w c hv (fun _ _ => trivial) k i hi t hpc h13 h2 h3 a2 a3 hx hlen hm Q ?_
  intro t' hp hr hf hm'
  exact (cont t' hp hr hf hm').toReachW

/-- The 16 aligned words, to offset `b38eOff`. -/
theorem apath_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (hlen : 64 * k + 64 ≤ c.len.toNat) (allowed : Word → Kind → Word → Prop)
    (haccess : ∀ i, i < 16 → ∀ t : State,
      t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) →
      t.regs 13 = c.fp → t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
      EventAccessesTo allowed (traceAll (ach i) t)) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) → t.regs 13 = c.fp →
    t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) → t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
    (t.regs 2).toNat % 4 = 0 → (t.regs 3).toNat % 4 = 0 →
    (∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) → c.MemOk (64 * k + 4 * i) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 b38eOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 64) t'.mem → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) →
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q
  | 0, i, hi, t, hpc, _, _, _, _, _, _, hm, cont => by
    have sJ : slotJ = 16 := by decide
    obtain rfl : i = 16 := by omega
    exact cont t (by rw [hpc, ach_end]) (fun _ _ _ _ => rfl) (fun _ _ => rfl) hm
  | n + 1, i, hi, t, hpc, h13, h2, h3, a2, a3, hx, hm, cont => by
    have hcw := ChaCha20Layout.chCallWords_eq
    have sJ : slotJ = 16 := by decide
    apply achunk_S c hv hPc k i (by omega) t hpc h13 h2 h3 a2 a3 (hx i (by omega)) hlen hm
      allowed (haccess i (by omega) t hpc h13 h2 h3)
    intro t1 pc1 r1 f1 m1
    have e : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t1.regs r = t.regs r := r1
    apply apath_S c hv hPc k hlen allowed haccess Q n (i + 1) (by omega) t1 pc1 (by rw [e 13 (by decide) (by decide) (by decide), h13])
      (by rw [e 2 (by decide) (by decide) (by decide), h2]) (by rw [e 3 (by decide) (by decide) (by decide), h3])
      (by rw [e 2 (by decide) (by decide) (by decide)]; exact a2) (by rw [e 3 (by decide) (by decide) (by decide)]; exact a3)
      (fun j hj => by rw [f1 j (by omega), f1 (slotJ + j) (by omega)]; exact hx j hj) m1
    intro t2 pc2 r2 f2 m2
    exact cont t2 pc2 (fun r a b d => (r2 r a b d).trans (e r a b d)) (fun j hj => (f2 j hj).trans (f1 j hj)) m2


theorem apath_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (hlen : 64 * k + 64 ≤ c.len.toNat) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) → t.regs 13 = c.fp →
    t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) → t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
    (t.regs 2).toNat % 4 = 0 → (t.regs 3).toNat % 4 = 0 →
    (∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) → c.MemOk (64 * k + 4 * i) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 b38eOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 64) t'.mem → ReachW c.base Pc c.Wr t' Q) →
    ReachW c.base Pc c.Wr t Q := by
  intro n i hi t hpc h13 h2 h3 a2 a3 hx hm cont
  apply ChaCha20Policy.ofEvPW
  apply apath_S c hv hPc k hlen (writeOnlyPolicy c.Wr) ?_ Q n i hi t hpc h13 h2 h3 a2 a3 hx hm ?_
  · intro j hj u _ _ _ hu
    exact ach_write_policy c hv k j hj u hu hlen
  · intro u hp hr hf hm'
    exact ChaCha20Policy.reachW_toEvP (cont u hp hr hf hm')

theorem apath (c : Ctx) (hv : Valid c) (k : Nat) (hlen : 64 * k + 64 ≤ c.len.toNat) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) → t.regs 13 = c.fp →
    t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) → t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
    (t.regs 2).toNat % 4 = 0 → (t.regs 3).toNat % 4 = 0 →
    (∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) → c.MemOk (64 * k + 4 * i) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 b38eOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + 64) t'.mem → Reach c.base c.Wr t' Q) →
    Reach c.base c.Wr t Q := by
  intro n i hi t hpc h13 h2 h3 a2 a3 hx hm cont
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine apath_w c hv (fun _ _ => trivial) k hlen Q n i hi t hpc h13 h2 h3 a2 a3 hx hm ?_
  intro u hp hr hf hm'
  exact (cont u hp hr hf hm').toReachW

/-! ## Byte path: `bchOff` to `bloOff` -/

theorem bch_at : (List.range 16).all (fun i => seqAt B (bchOff + bchSize * i) (bch i)) = true := by
  simp only [seqAt_eq_scan]; cbv
theorem bch_end : bchOff + bchSize * 16 = bmidOff := by decide

theorem bl_at : seqAt B blOff bl = true := by decide
theorem bmid_at : seqAt B bmidOff [.addRdSp 5 0, .movImm 0 0] = true := by decide
theorem blo_at : instrAt B bloOff = some (.bcond 3 (brImm8 bloOff blOff)) := by decide +kernel
theorem blo_next : bloOff + 2 = n1Off := by decide

theorem bch_effect (t : State) (i : Nat) (hi : i < 16) :
    let u := execAll (bch i) t
    u.mem = write32 t.mem (slot (t.regs 13) i)
      (read32 t.mem (slot (t.regs 13) i) + read32 t.mem (slot (t.regs 13) (slotJ + i))) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → u.regs r = t.regs r) := by
  have h8 : (BitVec.ofNat 8 (slotX + i)).toNat = i := by simp [slotX]; omega
  have h8' : (BitVec.ofNat 8 (slotJ + i)).toNat = slotJ + i := by simp [slotJ]; omega
  refine ⟨?_, fun r h0 h1 h15 => execAll_regs_other _ _ r h15 (by
    simp [bch, Instr.dsts, MemOp.isLoad, Fin.ext_iff, h0, h1])⟩
  simp only [bch, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, h8, h8']
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [add_flags, Nat.mul_comm i 4, Nat.mul_comm (slotJ + i) 4]; rfl

theorem bch_aligned (t : State) (i : Nat) (hi : i < 16) (h13 : (t.regs 13).toNat % 4 = 0) :
    alignedAll (bch i) t = true := by
  have h8 : (BitVec.ofNat 8 (slotX + i)).toNat = i := by simp [slotX]; omega
  have h8' : (BitVec.ofNat 8 (slotJ + i)).toNat = slotJ + i := by simp [slotJ]; omega
  apply alignedAll_sp _ t _ h13
  intro j hj
  simp only [bch, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;>
    refine ⟨by simp [Instr.dsts], _, rfl, ?_⟩ <;> simp [h8, h8'] <;> omega

theorem bch_writes (t : State) (i : Nat) (hi : i < 16) :
    ∀ e ∈ traceAll (bch i) t, ∀ y, Writes e.accesses y → InFrame (t.regs 13) ChaCha20Layout.chFrameWords y :=
  frameWB_writes (bch i) t (by
    have hfw := ChaCha20Layout.chFrameWords_eq
    simp [frameWB, bch, Instr.writesMem, Instr.dsts, MemOp.isLoad, slotX]; omega)

/-- Byte preparation writes stay inside the functional frame bound. -/
theorem bch_write_policy (c : Ctx) (i : Nat) (hi : i < 16) (t : State)
    (hsp : t.regs 13 = c.fp) :
    EventAccessesTo (writeOnlyPolicy c.Wr) (traceAll (bch i) t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read => exact Or.inl rfl
  | write =>
    right
    have hw := bch_writes t i hi e he _ ⟨a, ha, hk, q, hq, rfl⟩
    rw [hsp] at hw
    exact ChaCha20Setup.wr_frame hw (by have := ChaCha20Layout.chFrameWords_eq; have := ChaCha20Layout.chStackWords_eq; omega)

theorem bch_in (i : Nat) (hi : i < 16) : bchOff + bchSize * i + seqSize (bch i) ≤ ChaCha20Policy.chaEnd := by
  rw [bch_size, off_step]
  have h1 : bchSize * (i + 1) ≤ bchSize * 16 := Nat.mul_le_mul_left _ (by omega)
  have h2 := bch_end
  have h3 : bmidOff ≤ ChaCha20Policy.chaEnd := by decide +kernel
  omega

/-- `x[i] += j[i]` for i = 0..15, to offset `bmidOff`. -/
theorem bsum_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (allowed : Word → Kind → Word → Prop)
    (haccess : ∀ i, i < 16 → ∀ t : State,
      t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → t.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll (bch i) t)) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → t.regs 13 = c.fp →
    (∀ j, i ≤ j → j < 16 → c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) →
    (∀ j < i, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk P t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 bmidOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < 16, c.fw t' j = ChaCha20Block.ks c k j) → (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) →
      c.MemOk P t'.mem → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) →
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q
  | 0, i, hi, t, hpc, _, _, hd, hm, cont => by
    have sJ : slotJ = 16 := by decide
    obtain rfl : i = 16 := by omega
    exact cont t (by rw [hpc, bch_end]) (fun _ _ _ _ => rfl) hd (fun _ _ _ => rfl) hm
  | n + 1, i, hi, t, hpc, h13, hx, hd, hm, cont => by
    have hcw := ChaCha20Layout.chCallWords_eq
    have sJ : slotJ = 16 := by decide
    have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
    have sFW := ChaCha20Layout.chFrameWords_eq
    have sSW := ChaCha20Layout.chStackWords_eq
    apply ChaCha20Policy.blockP hPc hb2 (bch i) _ hpc (bch_pc_even i) (List.all_eq_true.mp bch_at i (List.mem_range.mpr (by omega)))
      (by simp [bch, Instr.falls]) (bch_aligned t i (by omega) (by rw [h13]; exact ChaCha20Setup.fp4 hv))
      (haccess i (by omega) t hpc h13) (bch_in i (by omega))
    obtain ⟨em, er⟩ := bch_effect t i (by omega)
    have fw1 : ∀ j < ChaCha20Layout.chCallWords, c.fw (execAll (bch i) t) j = if i = j then ChaCha20Block.ks c k i else c.fw t j := by
      intro j hj
      rw [c.fw_write (k := i) (by rw [em, h13]) j (by omega) (by omega)]
      have := hx i (by omega) (by omega)
      simp only [Ctx.fw] at this
      rw [this]; rfl
    apply bsum_S c hv hPc k allowed haccess Q n (i + 1) (by omega) _
      (by rw [execAll_pc _ _ (by simp [bch, Instr.falls]), hpc, ofNat_add_assoc, bch_size, off_step])
      (by rw [er 13 (by decide) (by decide) (by decide), h13])
      (fun j h1 h2 => by rw [fw1 j (by omega), fw1 (slotJ + j) (by omega), if_neg (by omega), if_neg (by omega)];
                         exact hx j (by omega) h2)
      (fun j hj => by
        rw [fw1 j (by omega)]
        by_cases e : i = j
        · rw [if_pos e, e]
        · rw [if_neg e]; exact hd j (by omega))
      (by rw [em, h13]; exact c.memOk_write_slot hm i (by omega) _)
    intro t2 pc2 r2 x2 f2 m2
    exact cont t2 pc2 (fun r a b d => (r2 r a b d).trans (er r a b d)) x2
      (fun j h1 h2 => by rw [f2 j h1 h2, fw1 j h2, if_neg (by omega)]) m2


theorem bsum_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → t.regs 13 = c.fp →
    (∀ j, i ≤ j → j < 16 → c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) →
    (∀ j < i, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk P t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 bmidOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < 16, c.fw t' j = ChaCha20Block.ks c k j) → (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) →
      c.MemOk P t'.mem → ReachW c.base Pc c.Wr t' Q) →
    ReachW c.base Pc c.Wr t Q := by
  intro n i hi t hpc h13 hx hd hm cont
  apply ChaCha20Policy.ofEvPW
  apply bsum_S c hv hPc k (writeOnlyPolicy c.Wr) ?_ Q n i hi t hpc h13 hx hd hm ?_
  · intro j hj u _ hsp
    exact bch_write_policy c j hj u hsp
  · intro u hp hr hx hf hm'
    exact ChaCha20Policy.reachW_toEvP (cont u hp hr hx hf hm')

theorem bsum (c : Ctx) (hv : Valid c) (k : Nat) (Q : State → Prop) :
    ∀ n i, i + n = 16 → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → t.regs 13 = c.fp →
    (∀ j, i ≤ j → j < 16 → c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j) →
    (∀ j < i, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk P t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 bmidOff →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < 16, c.fw t' j = ChaCha20Block.ks c k j) → (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) →
      c.MemOk P t'.mem → Reach c.base c.Wr t' Q) →
    Reach c.base c.Wr t Q := by
  intro n i hi t hpc h13 hx hd hm cont
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine bsum_w c hv (fun _ _ => trivial) k Q n i hi t hpc h13 hx hd hm ?_
  intro u hp hr hx hf hm'
  exact (cont u hp hr hx hf hm').toReachW

theorem byte_xor (a b : BitVec 8) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : Word)).extractLsb' 0 8 = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, hi,
    show i < 32 by omega]

theorem bl_effect (t : State) :
    let u := execAll bl t
    u.mem = write8 t.mem (t.regs 3 + t.regs 0)
      (read8 t.mem (t.regs 2 + t.regs 0) ^^^ read8 t.mem (t.regs 5 + t.regs 0)) ∧
    u.regs 0 = t.regs 0 + 1#32 ∧ u.c = decide ((t.regs 4).toNat ≤ (t.regs 0 + 1#32).toNat) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → u.regs r = t.regs r) := by
  refine ⟨?_, ?_, ?_, fun r h0 h1 h6 h15 => execAll_regs_other _ _ r h15 (by
    simp [bl, Instr.dsts, MemOp.isLoad, Fin.ext_iff, h0, h1]; exact h6)⟩
  all_goals
    simp only [bl, execAll, Instr.next, Instr.exec, Instr.exec.memOp, addFlags, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
      M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3,
      M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6]
    simp (config := { decide := true }) only [ite_true, ite_false]
  all_goals first | rfl | (rw [add_flags]; rfl) | (rw [add_flags, sub_carry]; rfl)

theorem bl_writes (t : State) :
    ∀ e ∈ traceAll bl t, ∀ y, Writes e.accesses y → y = t.regs 3 + t.regs 0 := by
  intro e he y ⟨a, ha, hw, q, hq, hy⟩
  simp only [traceAll, bl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hw)
  have hq0 : q = 0 := by simpa [MemOp.width] using hq
  subst hq0
  rw [hy]
  simp only [M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_0, BitVec.add_zero]
  rw [show ((Instr.dp DpOp.eors 1 6).next ((Instr.memReg MemOp.ldrb 6 5 0).next
      ((Instr.memReg MemOp.ldrb 1 2 0).next t))).regs 3 = t.regs 3 from
    execAll_regs_other [.memReg .ldrb 1 2 0, .memReg .ldrb 6 5 0, .dp .eors 1 6] t 3 (by decide)
      (by simp [Instr.dsts, MemOp.isLoad]; decide),
    show ((Instr.dp DpOp.eors 1 6).next ((Instr.memReg MemOp.ldrb 6 5 0).next
      ((Instr.memReg MemOp.ldrb 1 2 0).next t))).regs 0 = t.regs 0 from
    execAll_regs_other [.memReg .ldrb 1 2 0, .memReg .ldrb 6 5 0, .dp .eors 1 6] t 0 (by decide)
      (by simp [Instr.dsts, MemOp.isLoad]; decide)]

theorem ofNat_succ (p : Nat) : BitVec.ofNat 32 p + 1#32 = BitVec.ofNat 32 (p + 1) := by
  rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]

/-- A byte-tail iteration satisfies the functional write bound. -/
theorem bl_write_policy (c : Ctx) (hv : Valid c) (k p : Nat) (t : State)
    (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (h0 : t.regs 0 = BitVec.ofNat 32 p) (hbound : 64 * k + p < c.len.toNat) :
    EventAccessesTo (writeOnlyPolicy c.Wr) (traceAll bl t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read => exact Or.inl rfl
  | write =>
    right
    have hw := bl_writes t e he _ ⟨a, ha, hk, q, hq, rfl⟩
    rw [hw, h3, h0, ofNat_add_assoc]
    exact Or.inr (by rw [oidx_out c hv _ hbound]; exact hbound)

/-- The byte loop at `blOff` with `r0 = p`, `r4 = N`, `r5 = sp`, keystream words in slots 0..15. -/
theorem bloop_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k N : Nat) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (allowed : Word → Kind → Word → Prop)
    (haccess : ∀ p, p < N → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 blOff →
      t.regs 13 = c.fp → t.regs 0 = BitVec.ofNat 32 p →
      t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → t.regs 5 = c.fp →
      EventAccessesTo allowed (traceAll bl t)) (Q : State → Prop) :
    ∀ n p, p + n = N → p < N → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 blOff → t.regs 13 = c.fp →
    t.regs 0 = BitVec.ofNat 32 p → t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
    t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → t.regs 4 = BitVec.ofNat 32 N → t.regs 5 = c.fp →
    (∀ j < 16, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk (64 * k + p) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) →
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q
  | 0, p, hp, hpN, _, _, _, _, _, _, _, _, _, _, _ => absurd hpN (by omega)
  | n + 1, p, hp, hpN, t, hpc, h13, h0, h2, h3, h4, h5, hx, hm, cont => by
    have hcw := ChaCha20Layout.chCallWords_eq
    have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
    have hP : 64 * k + p < c.len.toNat := by omega
    apply ChaCha20Policy.blockP hPc hb2 bl blOff hpc (by decide) bl_at (by decide)
      (by simp [alignedAll, bl, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, Nat.mod_one])
      (haccess p hpN t hpc h13 h0 h2 h3 h5) (by decide +kernel)
    obtain ⟨um, u0, uc, ur⟩ := bl_effect t
    generalize hu : execAll bl t = u at um u0 uc ur
    have upc : u.pc = c.base + BitVec.ofNat 32 bloOff := by
      rw [← hu, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    have uf : ∀ j < ChaCha20Layout.chCallWords, c.fw u j = c.fw t j := fun j hj => by
      show read32 _ _ = _
      rw [um, h3, h0, ofNat_add_assoc, read32_write8_out c hv _ _ _ _ hP hj]; rfl
    have umem : c.MemOk (64 * k + (p + 1)) u.mem := by
      rw [um, h3, h0, ofNat_add_assoc]
      apply memOk_write8 c hv hm hP
      rw [h2, h5, ofNat_add_assoc]
      simp only [read8]
      rw [byte_xor, inp_mem c hv hm _ (Nat.le_refl _) hP, output_byte_eq c _ hP]
      congr 1
      have e1 : (64 * k + p) / 64 = k := by omega
      have e2 : (64 * k + p) % 64 = p := by omega
      rw [e1, e2, kb, ← hx (p / 4) (by omega)]
      have ea : c.fp + BitVec.ofNat 32 p = slot c.fp (p / 4) + BitVec.ofNat 32 (p % 4) := by
        simp only [slot, ofNat_add_assoc]; congr 2; omega
      rw [ea, byte_of_read32 t.mem (slot c.fp (p / 4)) (p % 4) (Nat.mod_lt _ (by decide))]; rfl
    have ec : u.c = decide (N ≤ p + 1) := by
      rw [uc, h4, h0, ofNat_succ]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have ur' : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → u.regs r = t.regs r := ur
    apply ChaCha20Policy.evBcond hb2 bloOff blOff 3 (brImm8 bloOff blOff) upc (by decide) blo_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
    · intro hT
      rw [ChaCha20Setup.condPassed_3, ec] at hT
      have hlt : p + 1 < N := by simpa using hT
      apply bloop_S c hv hPc k N hN hlen allowed haccess Q n (p + 1) (by omega) hlt _ (ChaCha20Setup.setReg15_pc _ _)
        (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), ur' 13 (by decide) (by decide) (by decide) (by decide), h13])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 0 (by decide), u0, h0, ofNat_succ])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), ur' 2 (by decide) (by decide) (by decide) (by decide), h2])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), ur' 3 (by decide) (by decide) (by decide) (by decide), h3])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 4 (by decide), ur' 4 (by decide) (by decide) (by decide) (by decide), h4])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 5 (by decide), ur' 5 (by decide) (by decide) (by decide) (by decide), h5])
        (fun j hj => by rw [← hx j hj, ← uf j (by omega)]; rfl)
        (by rw [← Nat.add_assoc] at umem; exact umem)
      intro t2 pc2 r2 f2 m2
      refine cont t2 pc2 (fun r a b d e => ?_) (fun j hj => ?_) m2
      · rw [r2 r a b d e, ChaCha20Setup.setReg15_regs _ _ r e, ur' r a b d e]
      · rw [f2 j hj, ← uf j hj]; rfl
    · intro hF
      rw [ChaCha20Setup.condPassed_3, ec] at hF
      have heq : p + 1 = N := by simp at hF; omega
      refine cont _ (by rw [ChaCha20Setup.setReg15_pc, blo_next]) (fun r a b d e => ?_) (fun j hj => ?_) ?_
      · rw [ChaCha20Setup.setReg15_regs _ _ r e, ur' r a b d e]
      · rw [← uf j hj]; rfl
      · rw [← heq, ← Nat.add_assoc] at *; exact umem


theorem bloop_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k N : Nat) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (Q : State → Prop) :
    ∀ n p, p + n = N → p < N → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 blOff → t.regs 13 = c.fp →
    t.regs 0 = BitVec.ofNat 32 p → t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
    t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → t.regs 4 = BitVec.ofNat 32 N → t.regs 5 = c.fp →
    (∀ j < 16, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk (64 * k + p) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → ReachW c.base Pc c.Wr t' Q) →
    ReachW c.base Pc c.Wr t Q := by
  intro n p hp hpN t hpc h13 h0 h2 h3 h4 h5 hx hm cont
  apply ChaCha20Policy.ofEvPW
  apply bloop_S c hv hPc k N hN hlen (writeOnlyPolicy c.Wr) ?_ Q n p hp hpN t
    hpc h13 h0 h2 h3 h4 h5 hx hm ?_
  · intro j hj u _ _ hu0 _ hu3 _
    exact bl_write_policy c hv k j u hu3 hu0 (by omega)
  · intro u hp hr hf hm'
    exact ChaCha20Policy.reachW_toEvP (cont u hp hr hf hm')

theorem bloop (c : Ctx) (hv : Valid c) (k N : Nat) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (Q : State → Prop) :
    ∀ n p, p + n = N → p < N → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 blOff → t.regs 13 = c.fp →
    t.regs 0 = BitVec.ofNat 32 p → t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
    t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → t.regs 4 = BitVec.ofNat 32 N → t.regs 5 = c.fp →
    (∀ j < 16, c.fw t j = ChaCha20Block.ks c k j) → c.MemOk (64 * k + p) t.mem →
    (∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < ChaCha20Layout.chCallWords, c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → Reach c.base c.Wr t' Q) →
    Reach c.base c.Wr t Q := by
  intro n p hp hpN t hpc h13 h0 h2 h3 h4 h5 hx hm cont
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine bloop_w c hv (fun _ _ => trivial) k N hN hlen Q n p hp hpN t hpc h13 h0 h2 h3 h4 h5 hx hm ?_
  intro u hp hr hf hm'
  exact (cont u hp hr hf hm').toReachW

/-- The byte path from `bchOff` with `r4 = N` bytes to write. -/
theorem bpath_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k N : Nat) (hN1 : 1 ≤ N) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (t : State) (hpc : t.pc = c.base + BitVec.ofNat 32 bchOff) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (h4 : t.regs 4 = BitVec.ofNat 32 N) (hx : ∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j)
    (hm : c.MemOk (64 * k) t.mem) (allowed : Word → Kind → Word → Prop)
    (hprepare : ∀ i, i < 16 → ∀ t : State,
      t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → t.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll (bch i) t))
    (htail : ∀ p, p < N → ∀ t : State, t.pc = c.base + BitVec.ofNat 32 blOff →
      t.regs 13 = c.fp → t.regs 0 = BitVec.ofNat 32 p →
      t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      t.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → t.regs 5 = c.fp →
      EventAccessesTo allowed (traceAll bl t)) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off → t'.regs 13 = c.fp →
      t'.regs 2 = t.regs 2 → t'.regs 3 = t.regs 3 →
      (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) :
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply bsum_S c hv hPc k allowed hprepare Q 16 0 (by omega) t (by rw [hpc, Nat.mul_zero, Nat.add_zero]) h13 (fun j _ hj => hx j hj) (fun j hj => absurd hj (by omega)) hm
  intro t1 pc1 r1 x1 f1 m1
  have e1 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t1.regs r = t.regs r := r1
  apply ChaCha20Policy.blockP hPc hb2 [.addRdSp 5 0, .movImm 0 0] bmidOff pc1 (by decide) bmid_at (by decide)
    (by simp [alignedAll, Instr.accesses]) (by simp [EventAccessesTo, traceAll, Instr.accesses]) (by decide +kernel)
  generalize hu : execAll [.addRdSp 5 0, .movImm 0 0] t1 = u
  have ur : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 5 → r.val ≠ 15 → u.regs r = t1.regs r := fun r a b d => by
    rw [← hu]; exact execAll_regs_other _ _ r d (by simp [Instr.dsts, Fin.ext_iff, a]; exact b)
  have u13 : u.regs 13 = c.fp := by rw [ur 13 (by decide) (by decide) (by decide), e1 13 (by decide) (by decide) (by decide), h13]
  have u5 : u.regs 5 = c.fp := by
    rw [← hu]
    simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_0]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [e1 13 (by decide) (by decide) (by decide), h13]; simp
  have u0 : u.regs 0 = BitVec.ofNat 32 0 := by
    rw [← hu]
    simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_0]
    simp (config := { decide := true }) only [ite_true, ite_false]; try rfl
  have um : u.mem = t1.mem := by rw [← hu]; exact execAll_mem _ _ (by decide)
  have upc : u.pc = c.base + BitVec.ofNat 32 blOff := by
    rw [← hu, execAll_pc _ _ (by decide), pc1, ofNat_add_assoc]; rfl
  have uf : ∀ j, c.fw u j = c.fw t1 j := fun j => by simp only [Ctx.fw, um]
  have r2' : u.regs 2 = t.regs 2 := by rw [ur 2 (by decide) (by decide) (by decide), e1 2 (by decide) (by decide) (by decide)]
  have r3' : u.regs 3 = t.regs 3 := by rw [ur 3 (by decide) (by decide) (by decide), e1 3 (by decide) (by decide) (by decide)]
  apply bloop_S c hv hPc k N hN hlen allowed htail Q N 0 (by omega) (by omega) u upc u13 u0 (r2'.trans h2) (r3'.trans h3)
    (by rw [ur 4 (by decide) (by decide) (by decide), e1 4 (by decide) (by decide) (by decide), h4]) u5
    (fun j hj => (uf j).trans (x1 j hj)) (by rw [um]; exact m1)
  intro t2 pc2 r2 f2 m2
  refine cont t2 pc2 (by rw [r2 13 (by decide) (by decide) (by decide) (by decide), u13])
    (by rw [r2 2 (by decide) (by decide) (by decide) (by decide), r2'])
    (by rw [r2 3 (by decide) (by decide) (by decide) (by decide), r3'])
    (fun j a b => by rw [f2 j b, uf j, f1 j a b]) m2


theorem bpath_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k N : Nat) (hN1 : 1 ≤ N) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (t : State) (hpc : t.pc = c.base + BitVec.ofNat 32 bchOff) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (h4 : t.regs 4 = BitVec.ofNat 32 N) (hx : ∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j)
    (hm : c.MemOk (64 * k) t.mem) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off → t'.regs 13 = c.fp →
      t'.regs 2 = t.regs 2 → t'.regs 3 = t.regs 3 →
      (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → ReachW c.base Pc c.Wr t' Q) :
    ReachW c.base Pc c.Wr t Q := by
  apply ChaCha20Policy.ofEvPW
  apply bpath_S c hv hPc k N hN1 hN hlen t hpc h13 h2 h3 h4 hx hm
    (writeOnlyPolicy c.Wr) ?_ ?_ Q ?_
  · intro i hi u _ hsp
    exact bch_write_policy c i hi u hsp
  · intro p hp u _ _ hu0 _ hu3 _
    exact bl_write_policy c hv k p u hu3 hu0 (by omega)
  · intro u hp hs hr2 hr3 hf hm'
    exact ChaCha20Policy.reachW_toEvP (cont u hp hs hr2 hr3 hf hm')

theorem bpath (c : Ctx) (hv : Valid c) (k N : Nat) (hN1 : 1 ≤ N) (hN : N ≤ 64) (hlen : 64 * k + N ≤ c.len.toNat)
    (t : State) (hpc : t.pc = c.base + BitVec.ofNat 32 bchOff) (h13 : t.regs 13 = c.fp)
    (h2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (h4 : t.regs 4 = BitVec.ofNat 32 N) (hx : ∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j)
    (hm : c.MemOk (64 * k) t.mem) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 n1Off → t'.regs 13 = c.fp →
      t'.regs 2 = t.regs 2 → t'.regs 3 = t.regs 3 →
      (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw t' j = c.fw t j) → c.MemOk (64 * k + N) t'.mem → Reach c.base c.Wr t' Q) :
    Reach c.base c.Wr t Q := by
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine bpath_w c hv (fun _ _ => trivial) k N hN1 hN hlen t hpc h13 h2 h3 h4 hx hm Q ?_
  intro u hp hs hr2 hr3 hf hm'
  exact (cont u hp hs hr2 hr3 hf hm').toReachW

/-! ## `cmpEOff` to `achOff`: full or partial block, aligned or not -/

theorem low2 (x y : Word) (h : (x ||| y) <<< 30 = 0) : x.toNat % 4 = 0 ∧ y.toNat % 4 = 0 := by
  have hz : ∀ z : Word, z <<< 30 = 0 → z.setWidth 2 = 0 := fun z hz => by
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (0 : Word).toNat = 0 from rfl] at this
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, show (0 : BitVec 2).toNat = 0 from rfl]
    omega
  have h2 := hz _ h
  rw [BitVec.setWidth_or] at h2
  have key : ∀ a b : BitVec 2, a ||| b = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨ha, hb⟩ := key _ _ h2
  have ha' := congrArg BitVec.toNat ha
  have hb' := congrArg BitVec.toNat hb
  rw [BitVec.toNat_setWidth, show (0 : BitVec 2).toNat = 0 from rfl] at ha' hb'
  exact ⟨by omega, by omega⟩

/-- State at `n1Off` after the output of block `k`. -/
structure Out (c : Ctx) (k : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 n1Off
  sp : t.regs 13 = c.fp
  r2 : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k)
  r3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k)
  j : ∀ i < 16, c.fw t (slotJ + i) = c.J k i
  len : c.fw t slotLen = c.len - BitVec.ofNat 32 (64 * k)
  outp : c.fw t slotOutp = c.out + BitVec.ofNat 32 (64 * k)
  inp : c.fw t slotInp = c.inp + BitVec.ofNat 32 (64 * k)
  mem : c.MemOk (min (64 * k + 64) c.len.toNat) t.mem
  lt : 64 * k < c.len.toNat
  ok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true

theorem disp_at : seqAt B dispOff disp = true := by decide
theorem cmp_at : seqAt B cmpEOff [.cmpImm 4 64] = true := by decide
theorem blo2_at : instrAt B blo2Off = some (.bcond 3 (brImm8 blo2Off bchOff)) := by decide +kernel
theorem bne_at : instrAt B bne2Off = some (.bcond 1 (brImm8 bne2Off bchOff)) := by decide +kernel
theorem bne2_next : bne2Off + 2 = achOff := by decide
theorem b38e_at : instrAt B b38eOff = some (.b (brImm11 b38eOff n1Off)) := by decide +kernel

theorem disp_effect (t : State) :
    let u := execAll disp t
    u.regs 4 = 64#32 ∧ u.z = (((t.regs 2 ||| t.regs 3) <<< 30) == 0) ∧ u.mem = t.mem ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 4 → r.val ≠ 15 → u.regs r = t.regs r) := by
  refine ⟨?_, ?_, execAll_mem _ _ (by decide), fun r a b d => execAll_regs_other _ _ r d
    (by simp [disp, Instr.dsts, Fin.ext_iff, a]; exact b)⟩
  all_goals
    simp only [disp, execAll, Instr.next, Instr.exec, lslC, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
      M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4]
    simp (config := { decide := true }) only [ite_true, ite_false]
  all_goals first | rfl | simp

theorem ks_post (c : Ctx) {k : Nat} {t : State} (h : Post c k t) :
    ∀ j < 16, c.fw t j + c.fw t (slotJ + j) = ChaCha20Block.ks c k j := fun j hj => by
  rw [h.x j hj, h.j j hj, ChaCha20Block.ks, BitVec.add_comm]

theorem rem_eq (c : Ctx) (k : Nat) (hk : 64 * k < c.len.toNat) :
    c.len - BitVec.ofNat 32 (64 * k) = BitVec.ofNat 32 (c.len.toNat - 64 * k) := by
  apply BitVec.eq_of_toNat_eq
  have := c.len.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 64 * k < 2 ^ 32)]
  omega

/-- **Output of block `k`**: from `Post c k` (`cmpEOff`) to `Out c k` (`n1Off`). -/
theorem bout_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : Post c k t) (allowed : Word → Kind → Word → Prop)
    (haligned : 64 * k + 64 ≤ c.len.toNat → ∀ i, i < 16 → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) → u.regs 13 = c.fp →
      u.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      u.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
      EventAccessesTo allowed (traceAll (ach i) u))
    (hprepare : ∀ i, i < 16 → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → u.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll (bch i) u))
    (htail : ∀ N, N ≤ 64 → 64 * k + N ≤ c.len.toNat → ∀ p, p < N → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 blOff → u.regs 13 = c.fp → u.regs 0 = BitVec.ofNat 32 p →
      u.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      u.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → u.regs 5 = c.fp →
      EventAccessesTo allowed (traceAll bl u)) (Q : State → Prop)
    (cont : ∀ u, Out c k u → ReachS c.base (ChaCha20Policy.EvP Pc allowed) u Q) : ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hcw := ChaCha20Layout.chCallWords_eq
  have sJ : slotJ = 16 := by decide
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hR := rem_eq c k h.lt
  apply ChaCha20Policy.blockP hPc hb2 [.cmpImm 4 64] cmpEOff h.pc (by decide) cmp_at (by decide)
    (by simp [alignedAll, Instr.accesses]) (by simp [EventAccessesTo, traceAll, Instr.accesses]) (by decide +kernel)
  generalize hs1 : execAll [.cmpImm 4 64] t = s1
  have r1 : ∀ r : Reg, r.val ≠ 15 → s1.regs r = t.regs r := fun r hr => by
    rw [← hs1]; exact execAll_regs_other _ _ r hr (by simp [Instr.dsts])
  have m1 : s1.mem = t.mem := by rw [← hs1]; exact execAll_mem _ _ (by decide)
  have pc1 : s1.pc = c.base + BitVec.ofNat 32 blo2Off := by
    rw [← hs1, execAll_pc _ _ (by decide), h.pc, ofNat_add_assoc]; rfl
  have c1 : s1.c = decide (64 ≤ c.len.toNat - 64 * k) := by
    rw [← hs1]
    simp only [execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setNZCV,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_4, h.r4, hR]
    try simp (config := { decide := true }) only [ite_false]
    rw [sub_carry]
    have := c.len.isLt
    simp only [decide_eq_decide]
    simp
    omega
  have f1 : ∀ j, c.fw s1 j = c.fw t j := fun j => by simp only [Ctx.fw, m1]
  have mkOut : ∀ u N, N = min 64 (c.len.toNat - 64 * k) → u.pc = c.base + BitVec.ofNat 32 n1Off →
      u.regs 13 = c.fp → u.regs 2 = t.regs 2 → u.regs 3 = t.regs 3 →
      (∀ j, 16 ≤ j → j < ChaCha20Layout.chCallWords → c.fw u j = c.fw t j) → c.MemOk (64 * k + N) u.mem → Out c k u :=
    fun u N hN pc u13 u2 u3 uf um =>
      ⟨pc, u13, u2.trans h.r2, u3.trans h.r3, fun i hi => (uf (slotJ + i) (by omega) (by omega)).trans (h.j i hi),
       (uf 32 (by omega) (by omega)).trans h.len, (uf 33 (by omega) (by omega)).trans h.outp,
       (uf 34 (by omega) (by omega)).trans h.inp, by
        rw [show min (64 * k + 64) c.len.toNat = 64 * k + N by have := h.lt; omega]; exact um, h.lt, h.ok⟩
  apply ChaCha20Policy.evBcond hb2 blo2Off bchOff 3 (brImm8 blo2Off bchOff) pc1 (by decide) blo2_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
  · -- partial final block
    intro hT
    rw [ChaCha20Setup.condPassed_3, c1] at hT
    have hlt : c.len.toNat - 64 * k < 64 := by simpa using hT
    have := h.lt
    apply bpath_S c hv hPc k (c.len.toNat - 64 * k) (by omega) (by omega) (by omega) _ (ChaCha20Setup.setReg15_pc _ _)
      (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), r1 13 (by decide), h.sp])
      (by rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), r1 2 (by decide), h.r2])
      (by rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), r1 3 (by decide), h.r3])
      (by rw [ChaCha20Setup.setReg15_regs _ _ 4 (by decide), r1 4 (by decide), h.r4, hR])
      (fun j hj => by simp only [Ctx.fw, ChaCha20Setup.setReg15_regs, M0Crypto.Armv6M.State.setReg]; rw [← ks_post c h j hj]; simp only [Ctx.fw, m1])
      (by simp only [M0Crypto.Armv6M.State.setReg]; rw [m1]; exact h.mem)
      allowed hprepare (htail _ (by omega) (by omega))
    intro u pc u13 u2 u3 uf um
    apply cont
    refine mkOut u _ (by omega) pc u13 ?_ ?_ (fun j a b => ?_) um
    · rw [u2, ChaCha20Setup.setReg15_regs _ _ 2 (by decide), r1 2 (by decide)]
    · rw [u3, ChaCha20Setup.setReg15_regs _ _ 3 (by decide), r1 3 (by decide)]
    · rw [uf j a b, ← f1 j]; rfl
  · -- full block
    intro hF
    rw [ChaCha20Setup.condPassed_3, c1] at hF
    have hge : 64 ≤ c.len.toNat - 64 * k := by simpa using hF
    have := h.lt
    apply ChaCha20Policy.blockP hPc hb2 disp dispOff (ChaCha20Setup.setReg15_pc _ _) (by decide) disp_at (by decide)
      (by simp [alignedAll, disp, Instr.accesses]) (by simp [EventAccessesTo, traceAll, disp, Instr.accesses]) (by decide +kernel)
    obtain ⟨d4, dz, dm, dr⟩ := disp_effect (s1.setReg 15 (c.base + BitVec.ofNat 32 dispOff))
    generalize hs2 : execAll disp (s1.setReg 15 (c.base + BitVec.ofNat 32 dispOff)) = s2 at d4 dz dm dr ⊢
    have e2 : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 4 → r.val ≠ 15 → s2.regs r = t.regs r := fun r a b d => by
      rw [dr r a b d, ChaCha20Setup.setReg15_regs _ _ r d, r1 r d]
    have pc2 : s2.pc = c.base + BitVec.ofNat 32 bne2Off := by
      rw [← hs2, execAll_pc _ _ (by decide), ChaCha20Setup.setReg15_pc, ofNat_add_assoc]; rfl
    have f2 : ∀ j, c.fw s2 j = c.fw t j := fun j => by
      simp only [Ctx.fw, dm, M0Crypto.Armv6M.State.setReg, m1]
    have g2 : s2.regs 2 = t.regs 2 := e2 2 (by decide) (by decide) (by decide)
    have g3 : s2.regs 3 = t.regs 3 := e2 3 (by decide) (by decide) (by decide)
    have g13 : s2.regs 13 = t.regs 13 := e2 13 (by decide) (by decide) (by decide)
    apply ChaCha20Policy.evBcond hb2 bne2Off bchOff 1 (brImm8 bne2Off bchOff) pc2 (by decide) bne_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
    · -- unaligned: byte path with 64 bytes
      intro _
      apply bpath_S c hv hPc k 64 (by omega) (by omega) (by omega) _ (ChaCha20Setup.setReg15_pc _ _)
        (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), g13, h.sp])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), g2, h.r2])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), g3, h.r3])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 4 (by decide), d4])
        (fun j hj => by
          have := ks_post c h j hj
          rw [← f2 j, ← f2 (slotJ + j)] at this
          exact this)
        (by simp only [M0Crypto.Armv6M.State.setReg]; rw [dm]; simp only [M0Crypto.Armv6M.State.setReg]; rw [m1]; exact h.mem)
        allowed hprepare (htail _ (by omega) (by omega))
      intro u pc u13 u2 u3 uf um
      apply cont
      refine mkOut u 64 (by omega) pc u13 ?_ ?_ (fun j a b => ?_) um
      · rw [u2, ChaCha20Setup.setReg15_regs _ _ 2 (by decide), g2]
      · rw [u3, ChaCha20Setup.setReg15_regs _ _ 3 (by decide), g3]
      · rw [uf j a b, ← f2 j]; rfl
    · -- aligned
      intro hz
      rw [ChaCha20Setup.condPassed_1, dz] at hz
      have hz' : (t.regs 2 ||| t.regs 3) <<< 30 = 0 := by
        rw [Bool.not_eq_false'] at hz
        have e := beq_iff_eq.mp hz
        rwa [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), ChaCha20Setup.setReg15_regs _ _ 3 (by decide),
          r1 2 (by decide), r1 3 (by decide)] at e
      obtain ⟨a2, a3⟩ := low2 _ _ hz'
      apply apath_S c hv hPc k (by omega) allowed (haligned (by omega)) Q 16 0 (by omega) _ (by rw [ChaCha20Setup.setReg15_pc, bne2_next, Nat.mul_zero, Nat.add_zero])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), g13, h.sp])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), g2, h.r2])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), g3, h.r3])
        (by rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), g2]; exact a2)
        (by rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), g3]; exact a3)
        (fun j hj => by
          have := ks_post c h j hj
          rw [← f2 j, ← f2 (slotJ + j)] at this
          exact this)
        (by simp only [M0Crypto.Armv6M.State.setReg]; rw [dm]; simp only [M0Crypto.Armv6M.State.setReg]; rw [m1]; exact h.mem)
      intro u pc ur uf um
      apply ChaCha20Policy.evB hb2 b38eOff n1Off (brImm11 b38eOff n1Off) pc (by decide) b38e_at (by decide) (by decide +kernel) (ChaCha20Policy.chaAt hPc (by decide +kernel))
      apply cont
      have er : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → u.regs r = s2.regs r := fun r a b d => by
        rw [ur r a b d, ChaCha20Setup.setReg15_regs _ _ r d]
      refine mkOut _ 64 (by omega) (ChaCha20Setup.setReg15_pc _ _) ?_ ?_ ?_ (fun j a b => ?_) ?_
      · rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), er 13 (by decide) (by decide) (by decide), g13, h.sp]
      · rw [ChaCha20Setup.setReg15_regs _ _ 2 (by decide), er 2 (by decide) (by decide) (by decide), g2]
      · rw [ChaCha20Setup.setReg15_regs _ _ 3 (by decide), er 3 (by decide) (by decide) (by decide), g3]
      · show read32 _ _ = _
        simp only [M0Crypto.Armv6M.State.setReg]
        rw [show read32 u.mem (slot c.fp j) = c.fw u j from rfl, uf j b]
        simp only [Ctx.fw, M0Crypto.Armv6M.State.setReg]
        exact f2 j
      · simp only [M0Crypto.Armv6M.State.setReg]; exact um


/-- Event-only form of `bout_S`. -/
theorem bout_events (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : Post c k t) (allowed : Word → Kind → Word → Prop)
    (haligned : 64 * k + 64 ≤ c.len.toNat → ∀ i, i < 16 → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 (achOff + achSize * i) → u.regs 13 = c.fp →
      u.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      u.regs 3 = c.out + BitVec.ofNat 32 (64 * k) →
      EventAccessesTo allowed (traceAll (ach i) u))
    (hprepare : ∀ i, i < 16 → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i) → u.regs 13 = c.fp →
      EventAccessesTo allowed (traceAll (bch i) u))
    (htail : ∀ N, N ≤ 64 → 64 * k + N ≤ c.len.toNat → ∀ p, p < N → ∀ u : State,
      u.pc = c.base + BitVec.ofNat 32 blOff → u.regs 13 = c.fp → u.regs 0 = BitVec.ofNat 32 p →
      u.regs 2 = c.inp + BitVec.ofNat 32 (64 * k) →
      u.regs 3 = c.out + BitVec.ofNat 32 (64 * k) → u.regs 5 = c.fp →
      EventAccessesTo allowed (traceAll bl u)) (Q : State → Prop)
    (cont : ∀ u, Out c k u → ReachEvents c.base allowed u Q) : ReachEvents c.base allowed t Q :=
  ChaCha20Policy.ofEvP (bout_S (Pc := fun _ => True) c hv (fun _ _ => trivial) k t h allowed haligned hprepare htail Q
    (fun u hu => ChaCha20Policy.reachEvents_toEvP (cont u hu)))

theorem bout_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (k : Nat) (t : State) (h : Post c k t) (Q : State → Prop)
    (cont : ∀ u, Out c k u → ReachW c.base Pc c.Wr u Q) : ReachW c.base Pc c.Wr t Q := by
  apply ChaCha20Policy.ofEvPW
  apply bout_S c hv hPc k t h (writeOnlyPolicy c.Wr) ?_ ?_ ?_ Q ?_
  · intro hlen i hi u _ _ _ hu
    exact ach_write_policy c hv k i hi u hu hlen
  · intro i hi u _ hu
    exact bch_write_policy c i hi u hu
  · intro N hN hlen p hp u _ _ hu0 _ hu3 _
    exact bl_write_policy c hv k p u hu3 hu0 (by omega)
  · intro u hu
    exact ChaCha20Policy.reachW_toEvP (cont u hu)

theorem block_output (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : Post c k t) (Q : State → Prop)
    (cont : ∀ u, Out c k u → Reach c.base c.Wr u Q) : Reach c.base c.Wr t Q := by
  refine ReachW.toReach (Pc := fun _ => True) ?_
  refine bout_w c hv (fun _ _ => trivial) k t h Q ?_
  intro u hu
  exact (cont u hu).toReachW

end M0Crypto.Release.ChaCha20Output
