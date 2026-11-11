import M0Crypto.Release.AeadPad
import M0Crypto.Release.ChaChaRetDefs
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
The shared AEAD prologue `pro` (offset `e` to `e + proXorOff`): push, `sub sp, #124`,
`SAVE_ARGS`, zero `CTX` and the counter, store the nonce argument, and set up
`m0c_chacha20_xor(CTX, CTX, 64, key)`.

`A = sp0 - 144` is the AEAD stack pointer; every write of the AEAD and its callees
lies in `SWr A = [A - 176, A + 144)` or the caller's `out`/`tag` buffers.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-! ## The call -/

/-- One AEAD call (same register and stack arguments for encrypt and decrypt). -/
structure ACall where
  base : Word
  sp0 : Word
  out : Word
  tag : Word
  inp : Word
  len : Word
  aad : Word
  alen : Word
  key : Word
  nonce : Word
  m0 : Mem
  regs0 : Reg → Word

namespace ACall
variable (c : ACall)
/-- Stack pointer after the prologue. -/
def A : Word := c.sp0 - 144#32
/-- The four words `push {r4-r7, lr}` saves. -/
def saved : List Word := [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14]
end ACall

/-- Entry to the function at offset `e`. -/
structure AEntry (c : ACall) (e : Nat) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 e
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.out
  r1 : c.regs0 1 = c.tag
  r2 : c.regs0 2 = c.inp
  r3 : c.regs0 3 = c.len
  aad : read32 c.m0 c.sp0 = c.aad
  alen : read32 c.m0 (c.sp0 + 4#32) = c.alen
  key : read32 c.m0 (c.sp0 + 8#32) = c.key
  nonce : read32 c.m0 (c.sp0 + 12#32) = c.nonce

/-- The stack region of the AEAD and its callees: `[sp0 - 320, sp0)`. -/
def SWr (A : Word) (y : Word) : Prop := ∃ o < 320, y = A - 176#32 + BitVec.ofNat 32 o

theorem swr_A (A : Word) (o : Nat) (ho : o < 144) : SWr A (A + BitVec.ofNat 32 o) := by
  refine ⟨176 + o, by omega, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem swr_lo (A : Word) (o : Nat) (ho : o < 176) : SWr A (A - BitVec.ofNat 32 176 + BitVec.ofNat 32 o) :=
  ⟨o, by omega, rfl⟩

/-! ## Effects of the four pieces of `pro` -/

def proA : List Instr := [.push 0xf0 true, .subSp 0x1f]
def proB : List Instr := [.strSp 0 0x1a, .strSp 1 0x1b, .strSp 2 0x1c, .strSp 3 0x1d, .movImm 0 0]
def proC : List Instr :=
  [.strSp 0 0x01, .ldrSp 0 0x27, .strSp 0 0x00, .addRdSp 0 0x02, .lslImm 1 0 0, .movImm 2 0x40,
   .ldrSp 3 0x26]

theorem pro_split : pro = proA ++ proB ++ zeroCtx ++ proC := rfl

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3

theorem proA_effect (s : State) :
    (execAll proA s).regs 13 = s.regs 13 - 144#32 ∧
    (execAll proA s).mem = storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] ∧
    (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → (execAll proA s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [execAll, proA, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, ChaChaRet.bitCount_f0, ChaChaRet.listRegs_f0]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [BitVec.sub_sub]; rfl
  · simp only [execAll, proA, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, ChaChaRet.bitCount_f0, ChaChaRet.listRegs_f0]
    simp (config := { decide := true }) only [ite_true, ite_false, List.map]
    rfl
  · intro r h13 h15
    exact execAll_regs_other _ _ r h15 (by
      simp [proA, Instr.dsts, Fin.ext_iff, ChaChaRet.listRegs_f0]; omega)

theorem proB_effect (t : State) :
    (execAll proB t).mem = write32 (write32 (write32 (write32 t.mem (t.regs 13 + 104#32) (t.regs 0))
      (t.regs 13 + 108#32) (t.regs 1)) (t.regs 13 + 112#32) (t.regs 2)) (t.regs 13 + 116#32) (t.regs 3) ∧
    (execAll proB t).regs 0 = 0#32 ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → (execAll proB t).regs r = t.regs r) := by
  refine ⟨?_, ?_, fun r h0 h15 => execAll_regs_other _ _ r h15
    (by simp [proB, Instr.dsts, Fin.ext_iff, h0])⟩ <;>
  simp [proB, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg]

theorem proC_effect (t : State) :
    (execAll proC t).mem = write32 (write32 t.mem (t.regs 13 + 4#32) (t.regs 0)) (t.regs 13)
      (read32 (write32 t.mem (t.regs 13 + 4#32) (t.regs 0)) (t.regs 13 + 156#32)) ∧
    (execAll proC t).regs 0 = t.regs 13 + 8#32 ∧ (execAll proC t).regs 1 = t.regs 13 + 8#32 ∧
    (execAll proC t).regs 2 = 64#32 ∧
    (execAll proC t).regs 3 = read32 (execAll proC t).mem (t.regs 13 + 152#32) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 15 →
      (execAll proC t).regs r = t.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h15 => execAll_regs_other _ _ r h15
    (by simp [proC, Instr.dsts, Fin.ext_iff, h0, h1, h2, MemOp.isLoad]; omega)⟩ <;>
  simp [proC, execAll, Instr.next, Instr.exec, lslC, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg]

/-! ## Words at offsets from one base -/

theorem off_ne (A : Word) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    A + BitVec.ofNat 32 a ≠ A + BitVec.ofNat 32 b := by
  intro e
  have e' : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
    have := congrArg (· - A) e
    simpa [BitVec.add_comm A, BitVec.add_sub_cancel] using this
  have := congrArg BitVec.toNat e'
  simp at this; omega

theorem rd_wr (m : Mem) (A v : Word) (a b : Nat) (ha : a % 4 = 0) (hb : b % 4 = 0) (ha' : a < 2 ^ 30)
    (hb' : b < 2 ^ 30) :
    read32 (write32 m (A + BitVec.ofNat 32 a) v) (A + BitVec.ofNat 32 b) =
      if a = b then v else read32 m (A + BitVec.ofNat 32 b) := by
  have e1 : A + BitVec.ofNat 32 a = slot A (a / 4) := by rw [slot]; congr 2; omega
  have e2 : A + BitVec.ofNat 32 b = slot A (b / 4) := by rw [slot]; congr 2; omega
  rw [e1, e2, read32_write32_slot' m A v _ _ (by omega) (by omega)]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]

theorem rd_wr_ne (m : Mem) (A v : Word) (a b : Nat) (ha : a % 4 = 0) (hb : b % 4 = 0) (ha' : a < 2 ^ 30)
    (hb' : b < 2 ^ 30) (h : a ≠ b) :
    read32 (write32 m (A + BitVec.ofNat 32 a) v) (A + BitVec.ofNat 32 b) = read32 m (A + BitVec.ofNat 32 b) := by
  rw [rd_wr m A v a b ha hb ha' hb', if_neg h]

theorem rd_wr0 (m : Mem) (A v : Word) (b : Nat) (hb : b % 4 = 0) (hb0 : b ≠ 0) (hb' : b < 2 ^ 30) :
    read32 (write32 m A v) (A + BitVec.ofNat 32 b) = read32 m (A + BitVec.ofNat 32 b) := by
  have := rd_wr m A v 0 b (by omega) hb (by omega) hb'
  rw [if_neg (Ne.symm hb0)] at this
  simpa using this

theorem rd_store_other (m : Mem) (A : Word) (vs : List Word) (a b : Nat)
    (hab : b + 4 ≤ a ∨ a + 4 * vs.length ≤ b) (hs : a + 4 * vs.length + b + 4 < 2 ^ 32) :
    read32 (storeWords m (A + BitVec.ofNat 32 a) vs) (A + BitVec.ofNat 32 b) = read32 m (A + BitVec.ofNat 32 b) := by
  apply read32_congr
  intro k hk
  apply storeWords_other
  intro i q hi hq e
  rw [ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc] at e
  exact off_ne A (by omega) (by omega) (by omega) e

theorem rd_store_same (m : Mem) (A : Word) (vs : List Word) (a i : Nat) (hi : i < vs.length)
    (hl : vs.length ≤ 2 ^ 28) :
    read32 (storeWords m (A + BitVec.ofNat 32 a) vs) (A + BitVec.ofNat 32 (a + 4 * i)) = vs[i] := by
  rw [← ofNat_add_assoc]; exact Frame.read32_storeWords_same m _ vs i hi hl

/-! ## Zeroing `CTX` -/

def zs (n : Nat) : List Instr := (List.range n).map fun i => .strSp 0 (BitVec.ofNat 8 (2 + i))

theorem zeroCtx_zs : zeroCtx = zs 16 := rfl

theorem zs_regs (n : Nat) (t : State) (r : Reg) (h15 : r.val ≠ 15) : (execAll (zs n) t).regs r = t.regs r :=
  execAll_regs_other _ _ r h15 (by simp [zs, Instr.dsts])

theorem zs_zero : ∀ (n : Nat), n ≤ 16 → ∀ (t : State), t.regs 0 = 0#32 →
    ∀ o < 4 * n, (execAll (zs n) t).mem (t.regs 13 + BitVec.ofNat 32 (8 + o)) = 0#8
  | 0, _, _, _, o, ho => absurd ho (by omega)
  | n + 1, hn, t, h0, o, ho => by
    rw [show zs (n + 1) = zs n ++ [.strSp 0 (BitVec.ofNat 8 (2 + n))] by
      simp [zs, List.range_succ, List.map_append]]
    rw [execAll_append]
    have u0 : (execAll (zs n) t).regs 0 = 0#32 := by rw [zs_regs n t 0 (by decide), h0]
    have u13 : (execAll (zs n) t).regs 13 = t.regs 13 := zs_regs n t 13 (by decide)
    simp only [execAll, Frame.strSp_next _ 0 (2 + n) (by omega), M0Crypto.Proofs.toReg_0, u0, u13]
    by_cases hlo : o < 4 * n
    · exact write32_zero_pass _ _ _ (zs_zero n (by omega) t h0 o hlo)
    · have : t.regs 13 + BitVec.ofNat 32 (8 + o) = slot (t.regs 13) (2 + n) + BitVec.ofNat 32 (o - 4 * n) := by
        rw [slot, ofNat_add_assoc]; congr 2; omega
      rw [this]; exact write32_zero_hit _ _ _ (by omega)

theorem zeroCtx_other (t : State) (y : Word) (hy : ∀ o < 64, y ≠ t.regs 13 + BitVec.ofNat 32 (8 + o)) :
    (execAll zeroCtx t).mem y = t.mem y := by
  apply execAll_mem_sp zeroCtx t y
  apply (spBlock_of_B (ok := fun q => q.1 == .read || (8 ≤ q.2 && q.2 + 4 ≤ 72)) (by decide)).mono
  intro q hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hq
  rcases hq with h | ⟨h1, h2⟩
  · exact .inl h
  · right; intro j hj
    rw [ofNat_add_assoc, show q.2 + j = 8 + (q.2 + j - 8) by omega]
    exact hy _ (by omega)

/-! ## Placement and the high frame words -/

structure AValid (c : ACall) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 320 ≤ c.sp0.toNat
  spHi : c.sp0.toNat + 16 ≤ 2 ^ 32
  codeS : Disj c.base Artifacts.Release.size (c.sp0 - 320#32) 336
  keyS : Disj c.key 32 (c.sp0 - 320#32) 320
  nonceS : Disj c.nonce 12 (c.sp0 - 320#32) 320
  code : CodeAt c.m0 c.base B

namespace AValid
variable {c : ACall} (hv : AValid c)
include hv
theorem A_toNat : c.A.toNat = c.sp0.toNat - 144 := by
  have := hv.spLo; simp [ACall.A, BitVec.toNat_sub]; omega
theorem A_off (k : Nat) (hk : k < 160) : (c.A + BitVec.ofNat 32 k).toNat = c.A.toNat + k := by
  have := hv.spHi; have := hv.A_toNat; simp [BitVec.toNat_add]; omega
end AValid

theorem sp0_off (c : ACall) (k : Nat) : c.A + BitVec.ofNat 32 (144 + k) = c.sp0 + BitVec.ofNat 32 k := by
  rw [ACall.A, BitVec.ofNat_add, ← BitVec.add_assoc, show BitVec.ofNat 32 144 = 144#32 from rfl,
    BitVec.sub_add_cancel]

/-- The words above `CTX`/`BLK`: saved arguments, saved registers, caller arguments. -/
structure Hi (c : ACall) (m : Mem) : Prop where
  out : read32 m (c.A + 104#32) = c.out
  tag : read32 m (c.A + 108#32) = c.tag
  inp : read32 m (c.A + 112#32) = c.inp
  len : read32 m (c.A + 116#32) = c.len
  saved : ∀ i (hi : i < 5), read32 m (c.A + BitVec.ofNat 32 (124 + 4 * i)) =
    c.saved[i]'(by simp [ACall.saved]; omega)
  aad : read32 m (c.A + 144#32) = c.aad
  alen : read32 m (c.A + 148#32) = c.alen
  key : read32 m (c.A + 152#32) = c.key
  nonce : read32 m (c.A + 156#32) = c.nonce

theorem Hi.congr {c : ACall} {m m' : Mem} (h : Hi c m)
    (hm : ∀ o, 104 ≤ o → o < 160 → m' (c.A + BitVec.ofNat 32 o) = m (c.A + BitVec.ofNat 32 o)) : Hi c m' := by
  have r : ∀ a, 104 ≤ a → a + 4 ≤ 160 → read32 m' (c.A + BitVec.ofNat 32 a) = read32 m (c.A + BitVec.ofNat 32 a) :=
    fun a h1 h2 => read32_congr (fun k hk => by rw [ofNat_add_assoc]; exact hm _ (by omega) (by omega))
  exact ⟨(r 104 (by omega) (by omega)).trans h.out, (r 108 (by omega) (by omega)).trans h.tag,
    (r 112 (by omega) (by omega)).trans h.inp, (r 116 (by omega) (by omega)).trans h.len,
    fun i hi => (r _ (by omega) (by omega)).trans (h.saved i hi),
    (r 144 (by omega) (by omega)).trans h.aad, (r 148 (by omega) (by omega)).trans h.alen,
    (r 152 (by omega) (by omega)).trans h.key, (r 156 (by omega) (by omega)).trans h.nonce⟩

/-! ## The prologue run -/

/-- State at `e + proXorOff`, ready for `bl m0c_chacha20_xor`. -/
structure ProPost (c : ACall) (e : Nat) (p : State) : Prop where
  pc : p.pc = c.base + BitVec.ofNat 32 (e + proXorOff)
  sp : p.regs 13 = c.A
  r0 : p.regs 0 = c.A + 8#32
  r1 : p.regs 1 = c.A + 8#32
  r2 : p.regs 2 = 64#32
  r3 : p.regs 3 = c.key
  hi : ∀ r : Reg, 4 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → p.regs r = c.regs0 r
  ctx : ∀ o < 64, p.mem (c.A + BitVec.ofNat 32 (8 + o)) = 0#8
  nonce : read32 p.mem c.A = c.nonce
  ctr : read32 p.mem (c.A + 4#32) = 0#32
  high : Hi c p.mem
  out : ∀ y, (∀ o < 144, y ≠ c.A + BitVec.ofNat 32 o) → p.mem y = c.m0 y

theorem bc240 : bitCount 240#8 = 4 := by decide

theorem sp0_A (c : ACall) : c.sp0 = c.A + 144#32 := by rw [ACall.A, BitVec.sub_add_cancel]

theorem sp_al {l : List Instr} (h : spBlockB l (fun q => q.2 % 4 == 0) = true) :
    SpBlock l (fun q => q.2 % 4 = 0) := (spBlock_of_B h).mono (fun q hq => by simpa using hq)

theorem sp_wr {l : List Instr} (h : spBlockB l (fun q => q.1 == .read || q.2 + 4 ≤ 144) = true) :
    SpBlock l (fun q => q.1 = .read ∨ ∀ k < 4, q.2 + k < 144) := by
  apply (spBlock_of_B h).mono
  intro q hq
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
  rcases hq with h | h
  · exact .inl h
  · exact .inr fun k hk => by omega

theorem sp_writes {A : Word} {l : List Instr} (t : State) (ht : t.regs 13 = A)
    (h : spBlockB l (fun q => q.1 == .read || q.2 + 4 ≤ 144) = true) : WritesTo (SWr A) (traceAll l t) := by
  intro e he y hy
  obtain ⟨o, ho, rfl⟩ := traceAll_writes_sp' (fun o => o < 144) l t (sp_wr h) e he y hy
  rw [ht]; exact swr_A A o ho

theorem pro_reach (c : ACall) (hv : AValid c) (e : Nat) (hseq : seqAt B e pro = true) (he : e % 2 = 0)
    (s : State) (h : AEntry c e s) {Q : State → Prop}
    (k : ∀ p, ProPost c e p → Reach c.base (SWr c.A) p Q) : Reach c.base (SWr c.A) s Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have s13 : s.regs 13 = c.sp0 := by rw [h.regs, h.sp]
  have hpc : s.pc = c.base + BitVec.ofNat 32 e := by
    show s.regs 15 = _; rw [h.regs, h.pc]
  have hpush : c.sp0 - 20#32 = c.A + BitVec.ofNat 32 124 := by
    rw [sp0_A, show (144#32 : Word) = BitVec.ofNat 32 124 + 20#32 from rfl, ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  have hA4 : c.A.toNat % 4 = 0 := by have := hv.sp8; have := hv.spLo; rw [hv.A_toNat]; omega
  obtain ⟨a13, am, ar⟩ := proA_effect s
  rw [s13, hpush] at am
  replace a13 : (execAll proA s).regs 13 = c.A := by rw [a13, s13]; rfl
  generalize ht1 : execAll proA s = t1 at a13 am ar
  obtain ⟨bm, b0, br⟩ := proB_effect t1
  have b13 : (execAll proB t1).regs 13 = c.A := by rw [br 13 (by decide) (by decide), a13]
  rw [a13] at bm
  generalize ht2 : execAll proB t1 = t2 at bm b0 br b13
  have z13 : (execAll zeroCtx t2).regs 13 = c.A := by rw [zeroCtx_zs, zs_regs 16 t2 13 (by decide), b13]
  obtain ⟨cm, c0, c1, c2, c3, cr⟩ := proC_effect (execAll zeroCtx t2)
  have z0 : (execAll zeroCtx t2).regs 0 = 0#32 := by rw [zeroCtx_zs, zs_regs 16 t2 0 (by decide), b0]
  rw [z13, z0] at cm
  rw [z13] at c0 c1 c3
  refine Reach.block hb2 pro e hpc he hseq (by decide) ?_ ?_ ?_
  · rw [pro_split, alignedAll_append, alignedAll_append, alignedAll_append]
    simp only [execAll_append, ht1, ht2, Bool.and_eq_true]
    refine ⟨⟨⟨?_, alignedAll_sp _ _ (sp_al (by decide)) (by rw [a13]; exact hA4)⟩,
      alignedAll_sp _ _ (sp_al (by decide)) (by rw [b13]; exact hA4)⟩,
      alignedAll_sp _ _ (sp_al (by decide)) (by rw [z13]; exact hA4)⟩
    simp [alignedAll, proA, Instr.accesses, wordAccesses, Access.aligned, M0Crypto.Armv6M.State.sp,
      ChaChaRet.bitCount_f0, s13, bc240]
    intro x _; have := hv.sp8; have := hv.spLo; omega
  · rw [pro_split, traceAll_append, traceAll_append, traceAll_append]
    simp only [execAll_append, ht1, ht2]
    refine WritesTo.append (WritesTo.append (WritesTo.append ?_ (sp_writes _ a13 (by decide)))
      (sp_writes _ b13 (by decide))) (sp_writes _ z13 (by decide))
    intro e he y ⟨a, ha, hw, q, hq, hy⟩
    simp only [traceAll, proA, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [Instr.accesses, wordAccesses, M0Crypto.Armv6M.State.sp,
      ChaChaRet.bitCount_f0, s13, bc240] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only at hq
    rw [hy]; simp only
    rw [hpush, ofNat_add_assoc, ofNat_add_assoc]
    exact swr_A _ _ (by omega)
  · have ppc : (execAll pro s).pc = c.base + BitVec.ofNat 32 (e + proXorOff) := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    rw [pro_split, execAll_append, execAll_append, execAll_append, ht1, ht2] at ppc ⊢
    apply k
    have hm0 : s.mem = c.m0 := h.mem
    rw [hm0, h.regs] at am
    have t1r : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t1.regs r = c.regs0 r := fun r a b => by
      rw [ar r a b, h.regs]
    rw [t1r 0 (by decide) (by decide), t1r 1 (by decide) (by decide), t1r 2 (by decide) (by decide),
      t1r 3 (by decide) (by decide), h.r0, h.r1, h.r2, h.r3] at bm
    -- the high words after piece B
    have H2 : Hi c t2.mem := by
      rw [bm]
      have w4 : ∀ b, b % 4 = 0 → 120 ≤ b → b < 160 →
          read32 (write32 (write32 (write32 (write32 t1.mem (c.A + 104#32) c.out) (c.A + 108#32) c.tag)
            (c.A + 112#32) c.inp) (c.A + 116#32) c.len) (c.A + BitVec.ofNat 32 b) =
            read32 t1.mem (c.A + BitVec.ofNat 32 b) := fun b h1 h2 h3 => by
        rw [rd_wr_ne _ _ _ 116 b (by decide) h1 (by decide) (by omega) (by omega),
          rd_wr_ne _ _ _ 112 b (by decide) h1 (by decide) (by omega) (by omega),
          rd_wr_ne _ _ _ 108 b (by decide) h1 (by decide) (by omega) (by omega),
          rd_wr_ne _ _ _ 104 b (by decide) h1 (by decide) (by omega) (by omega)]
      have st : ∀ b, b % 4 = 0 → 144 ≤ b → b < 160 →
          read32 t1.mem (c.A + BitVec.ofNat 32 b) = read32 c.m0 (c.A + BitVec.ofNat 32 b) := fun b h1 h2 h3 => by
        rw [am]; exact rd_store_other _ _ _ 124 b (by simp [ACall.saved]; omega) (by simp; omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rd_wr_ne _ _ _ 116 104 (by decide) (by decide) (by decide) (by decide) (by decide),
          rd_wr_ne _ _ _ 112 104 (by decide) (by decide) (by decide) (by decide) (by decide),
          rd_wr_ne _ _ _ 108 104 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact M0Crypto.Armv6M.read32_write32_same _ _ _
      · rw [rd_wr_ne _ _ _ 116 108 (by decide) (by decide) (by decide) (by decide) (by decide),
          rd_wr_ne _ _ _ 112 108 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact M0Crypto.Armv6M.read32_write32_same _ _ _
      · rw [rd_wr_ne _ _ _ 116 112 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact M0Crypto.Armv6M.read32_write32_same _ _ _
      · exact M0Crypto.Armv6M.read32_write32_same _ _ _
      · intro i hi
        rw [w4 _ (by omega) (by omega) (by omega), am]
        exact rd_store_same _ _ _ 124 i (by simp [ACall.saved]; omega) (by simp [ACall.saved])
      · rw [w4 144 (by decide) (by decide) (by decide), st 144 (by decide) (by decide) (by decide),
          show c.A + BitVec.ofNat 32 144 = c.sp0 from (sp0_A c).symm]; exact h.aad
      · rw [w4 148 (by decide) (by decide) (by decide), st 148 (by decide) (by decide) (by decide),
          show c.A + BitVec.ofNat 32 148 = c.sp0 + 4#32 from sp0_off c 4]; exact h.alen
      · rw [w4 152 (by decide) (by decide) (by decide), st 152 (by decide) (by decide) (by decide),
          show c.A + BitVec.ofNat 32 152 = c.sp0 + 8#32 from sp0_off c 8]; exact h.key
      · rw [w4 156 (by decide) (by decide) (by decide), st 156 (by decide) (by decide) (by decide),
          show c.A + BitVec.ofNat 32 156 = c.sp0 + 12#32 from sp0_off c 12]; exact h.nonce
    have H3 : Hi c (execAll zeroCtx t2).mem := H2.congr fun o h1 h2 => zeroCtx_other t2 _ (fun o' ho' => by
      rw [b13]; exact off_ne _ (by omega) (by omega) (by omega))
    generalize hm3 : (execAll zeroCtx t2).mem = m3 at H3 cm
    have m3z : ∀ o < 64, m3 (c.A + BitVec.ofNat 32 (8 + o)) = 0#8 := fun o ho => by
      rw [← hm3, zeroCtx_zs, ← b13]; exact zs_zero 16 (by decide) t2 b0 o (by omega)
    have pass : ∀ y, (∀ o < 8, y ≠ c.A + BitVec.ofNat 32 o) →
        (execAll proC (execAll zeroCtx t2)).mem y = m3 y := fun y hy => by
      rw [cm, write32_other' _ _ _ _ (fun q hq => hy q (by omega)), write32_other' _ _ _ _ (fun q hq => by
        rw [ofNat_add_assoc]; exact hy _ (by omega))]
    have Hp : Hi c (execAll proC (execAll zeroCtx t2)).mem := H3.congr fun o h1 h2 =>
      pass _ (fun q hq => off_ne _ (by omega) (by omega) (by omega))
    refine ⟨ppc, by rw [cr 13 (by decide) (by decide) (by decide) (by decide) (by decide), z13], c0, c1, c2,
      by rw [c3]; exact Hp.key, ?_, ?_, ?_, ?_, Hp, ?_⟩
    · intro r a b c'
      rw [cr r (by omega) (by omega) (by omega) (by omega) c', zeroCtx_zs, zs_regs 16 t2 r c',
        br r (by omega) c', t1r r b c']
    · intro o ho
      rw [pass _ (fun q hq => off_ne _ (by omega) (by omega) (by omega)), m3z o ho]
    · rw [cm, M0Crypto.Armv6M.read32_write32_same,
        rd_wr_ne _ _ _ 4 156 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact H3.nonce
    · rw [cm, rd_wr0 _ _ _ 4 (by decide) (by decide) (by decide)]
      exact M0Crypto.Armv6M.read32_write32_same _ _ _
    · intro y hy
      rw [pass y (fun o ho => hy o (by omega)), ← hm3, zeroCtx_other t2 y (fun o ho => by
        rw [b13]; exact hy _ (by omega)), bm]
      rw [write32_other' _ _ _ _ (fun q hq => by rw [ofNat_add_assoc]; exact hy _ (by omega)),
        write32_other' _ _ _ _ (fun q hq => by rw [ofNat_add_assoc]; exact hy _ (by omega)),
        write32_other' _ _ _ _ (fun q hq => by rw [ofNat_add_assoc]; exact hy _ (by omega)),
        write32_other' _ _ _ _ (fun q hq => by rw [ofNat_add_assoc]; exact hy _ (by omega)), am]
      apply storeWords_other
      intro i q hi hq
      rw [ofNat_add_assoc, ofNat_add_assoc]
      simp [ACall.saved] at hi
      exact hy _ (by omega)

/-- AAD bytes shared by the encryption and decryption contracts. -/
def ACall.aadB (c : ACall) := Ctx.bytesAt c.m0 c.aad c.alen.toNat

end M0Crypto.Release.Aead
