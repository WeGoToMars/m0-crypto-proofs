import M0Crypto.Release.ChaCha20Setup
import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.ChaCha20Policy

set_option linter.unusedSimpArgs false

/-!
`m0c_chacha20_xor` offsets `accOff` to `bpreOff`: the public slots `LEN`, `OUTP`, `INP`,
and the input state `j[0..15]` (constants, key, counter, nonce) on the stack.
Ends in `BlockInv c 0` at `.Lblock`.
-/

namespace M0Crypto.Release.ChaCha20Init

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Setup (le32 le32_r0 setReg15_regs setReg15_pc fp4 fp_toNat wr_frame Acc)
open M0Crypto.Release.ChaCha20Layout (keyOff nonOff kchSize poolOff b7Off accOff stCtrOff ldrNonceOff stInpOff stLenOff litJ0Off litJ1Off litJ2Off litJ3Off bpreOff chFrameWords slotOutp slotInp slotLen slotCtr slotJ slotKey slotNon slotArgNonce chStackBytes chFrameBytes)
open M0Crypto.Spec.ChaCha20 (wordOfBytes)

set_option maxRecDepth 100000

/-! ## Single stores and loads -/

/-- A store chunk: register-only code ending in `str r0, [sp, #4k]`. -/
theorem store_effect (t : State) (is : List Instr) (k : Nat) (hk : k < 256)
    (hm : is.all (!·.writesMem) = true) :
    let t' := execAll (is ++ [.strSp 0 (BitVec.ofNat 8 k)]) t
    t'.mem = write32 t.mem (slot ((execAll is t).regs 13) k) ((execAll is t).regs 0) ∧
    (∀ r : Reg, r.val ≠ 15 → t'.regs r = (execAll is t).regs r) := by
  simp only [execAll_append, execAll, strSp_next _ _ _ hk, execAll_mem is t hm]
  refine ⟨rfl, fun r hr => ?_⟩
  exact setReg15_regs _ _ r hr

/-! ## Reading the caller's buffers -/

theorem mem_m0 (c : Ctx) {P : Nat} {m : Mem} (h : c.MemOk P m) (y : Word) (hf : c.OutF y)
    (hp : ¬ c.oidx y < P) (hs : ∀ k < 36, y ≠ c.sp0 - BitVec.ofNat 32 36 + BitVec.ofNat 32 k) :
    m y = c.m0 y := by
  rw [h y hf, ite_eq_right_of_eq_false _ _ (eq_false hp), ChaCha20Return.mP_other c y hs]

/-- Bytes of a buffer disjoint from the 176 stack bytes are outside the frame and the saved area. -/
theorem disj_out (c : Ctx) (hv : Valid c) {a : Word} {n : Nat} (hd : Disj a n c.fp chStackBytes) (i : Nat)
    (hi : i < n) : c.OutF (a + BitVec.ofNat 32 i) ∧
      ∀ k < 36, a + BitVec.ofNat 32 i ≠ c.sp0 - BitVec.ofNat 32 36 + BitVec.ofNat 32 k := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have sFB := ChaCha20Layout.chFrameBytes_eq
  obtain ⟨h1, h2, h3⟩ := hd
  have hs : c.sp0 - BitVec.ofNat 32 36 = c.fp + BitVec.ofNat 32 140 := by simp only [Ctx.fp]; bv_omega
  refine ⟨fun o ho => ne_of_disj h1 h2 h3 hi (by omega), fun k hk => ?_⟩
  rw [hs, ofNat_add_assoc]
  exact ne_of_disj h1 h2 h3 hi (by omega)

/-! ## `LOAD_LE32 r3, off; str r0, [sp, #4k]` -/

theorem le32_noW (off : Nat) : (le32 off).all (!·.writesMem) = true := by
  simp [le32, Instr.writesMem, MemOp.isLoad]

theorem le32_regs (t : State) (off : Nat) (r : Reg) (h0 : r.val ≠ 0) (h1 : r.val ≠ 1) (h15 : r.val ≠ 15) :
    (execAll (le32 off) t).regs r = t.regs r :=
  execAll_regs_other _ _ r h15 (by simp [le32, Instr.dsts, MemOp.isLoad]; omega)

theorem kch_effect (t : State) (off k : Nat) (hoff : off + 3 < 32) (hk : k < 256) :
    let t' := execAll (kch off k) t
    t'.mem = write32 t.mem (slot (t.regs 13) k)
      (wordOfBytes (t.mem (t.regs 3 + BitVec.ofNat 32 off)) (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 1)))
        (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 2))) (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 3)))) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) := by
  obtain ⟨hm, hr⟩ := store_effect t (le32 off) k hk (le32_noW off)
  refine ⟨?_, fun r h0 h1 h15 => ?_⟩
  · simp only [kch]; rw [hm, le32_regs t off 13 (by decide) (by decide) (by decide), le32_r0 t off hoff]
  · simp only [kch]; rw [hr r h15, le32_regs t off r h0 h1 h15]

theorem kch_size (off k : Nat) : seqSize (kch off k) = kchSize := rfl

/-- Consecutive `kch` chunks at stride `kchSize`. -/
theorem stride_succ (base i : Nat) : base + kchSize * i + kchSize = base + kchSize * (i + 1) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]

theorem stride_even (base i : Nat) (hb : base % 2 = 0) : (base + kchSize * i) % 2 = 0 := by
  have hn : kchSize % 2 = 0 := by decide
  rw [Nat.add_mod, Nat.mul_mod, hn]; simp [hb]

/-- A run of `n` chunks starting at `o` ends before the first output store. -/
theorem chunk_fits (o n i k j : Nat) (hi : i < n) (h : o + kchSize * n ≤ ChaCha20Layout.achOff) :
    o + kchSize * i + seqSize (kch k j) ≤ ChaCha20Layout.achOff := by
  rw [kch_size]
  have : kchSize * (i + 1) ≤ kchSize * n := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_succ] at this
  omega

theorem key_fits : keyOff + kchSize * 8 ≤ ChaCha20Layout.achOff := by decide
theorem nonce_fits : nonOff + kchSize * 3 ≤ ChaCha20Layout.achOff := by decide

theorem kch_pc (t : State) (off k : Nat) :
    (execAll (kch off k) t).pc = t.pc + BitVec.ofNat 32 kchSize := by
  rw [execAll_pc _ t (by simp [kch, le32, Instr.falls]), kch_size]

theorem kch_aligned (t : State) (off k : Nat) (h4 : (t.regs 13).toNat % 4 = 0) :
    alignedAll (kch off k) t = true := by
  have hr : ∀ u : State, (execAll (le32 off) u).regs 13 = u.regs 13 := fun u =>
    le32_regs u off 13 (by decide) (by decide) (by decide)
  simp only [kch, alignedAll_append]
  rw [Bool.and_eq_true]; constructor
  · simp [le32, alignedAll, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, Nat.mod_one]
  · simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.sp, hr, List.all_cons, List.all_nil,
      Access.aligned, Bool.and_true, beq_iff_eq]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem kch_frameWB (off k : Nat) (hk : k < chFrameWords) : frameWB chFrameWords (kch off k) = true := by
  rw [ChaCha20Layout.chFrameWords_eq] at hk ⊢
  simp [frameWB, kch, le32, Instr.writesMem, Instr.dsts, MemOp.isLoad, Nat.mod_eq_of_lt (show k < 256 by omega), hk]

theorem kch_at_key : (List.range 8).all (fun i => seqAt B (keyOff + kchSize * i) (kch (4 * i) (slotKey + i))) = true := by
  decide
theorem kch_at_nonce : (List.range 3).all (fun i => seqAt B (nonOff + kchSize * i) (kch (4 * i) (slotNon + i))) = true := by
  decide

/-- One chunk stores word `v` at slot `k`, with `v` read from the caller's buffer `a`. -/
theorem kch_step (c : Ctx) (hv : Valid c) (t : State) (a : Word) (n i k : Nat) (hd : Disj a (4 * n) c.fp chStackBytes)
    (hi : i < n) (h4i : 4 * i + 3 < 32) (hk : k < chFrameWords) (h13 : t.regs 13 = c.fp) (h3 : t.regs 3 = a)
    (hm : c.MemOk 0 t.mem) :
    let t' := execAll (kch (4 * i) k) t
    t'.mem = write32 t.mem (slot c.fp k)
      (wordOfBytes (c.m0 (a + BitVec.ofNat 32 (4 * i))) (c.m0 (a + BitVec.ofNat 32 (4 * i + 1)))
        (c.m0 (a + BitVec.ofNat 32 (4 * i + 2))) (c.m0 (a + BitVec.ofNat 32 (4 * i + 3)))) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t'.regs r = t.regs r) := by
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  obtain ⟨em, er⟩ := kch_effect t (4 * i) k h4i (by omega)
  refine ⟨?_, er⟩
  have rd : ∀ q < 4, t.mem (a + BitVec.ofNat 32 (4 * i + q)) = c.m0 (a + BitVec.ofNat 32 (4 * i + q)) := by
    intro q hq
    obtain ⟨hf, hs⟩ := disj_out c hv hd (4 * i + q) (by omega)
    exact mem_m0 c hm _ hf (by omega) hs
  have r0 := rd 0 (by omega); simp only [Nat.add_zero] at r0
  rw [em, h13, h3, r0, rd 1 (by omega), rd 2 (by omega), rd 3 (by omega)]

theorem traceAll_inv (R : State → Prop) : ∀ (is : List Instr) (s : State), R s →
    (∀ i ∈ is, ∀ u, R u → R (i.next u)) →
    ∀ e ∈ traceAll is s, ∃ u i, i ∈ is ∧ R u ∧ e = ⟨u.pc, i, i.accesses u⟩
  | [], _, _, _, e, he => by cases he
  | i :: is, s, hs, hR, e, he => by
    simp only [traceAll, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨s, i, List.mem_cons_self, hs, rfl⟩
    · obtain ⟨u, j, hj, hu, rfl⟩ := traceAll_inv R is (i.next s) (hR i List.mem_cons_self s hs)
        (fun j hj => hR j (List.mem_cons_of_mem _ hj)) e he
      exact ⟨u, j, List.mem_cons_of_mem _ hj, hu, rfl⟩

theorem ldrb_read (u : State) (a : Word) (h3 : u.regs 3 = a) (r : LowReg) (d : Nat) (hd : d < 32)
    (x : Access) (hx : x ∈ (Instr.memImm .ldrb r 3 (BitVec.ofNat 5 d)).accesses u) :
    x.kind = .read ∧ x.addr = a + BitVec.ofNat 32 d ∧ x.width = 1 := by
  simp [Instr.accesses, MemOp.isLoad, MemOp.width] at hx
  subst hx
  simp [M0Crypto.Armv6M.State.reg, ← h3, Nat.mod_eq_of_lt hd]
  rfl

theorem kch_reads (off k : Nat) (hoff : off + 3 < 32) (t : State) (a : Word) (h3 : t.regs 3 = a) :
    ∀ e ∈ traceAll (kch off k) t, ∀ x ∈ e.accesses, x.kind = .read →
      ∃ q < 4, x.addr = a + BitVec.ofNat 32 (off + q) ∧ x.width = 1 := by
  have hd : ∀ i ∈ kch off k, (3 : Reg).val ∉ i.dsts := by
    intro i hi
    simp only [kch, le32, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
      (simp [Instr.dsts, MemOp.isLoad]; try decide)
  intro e he x hx hk
  obtain ⟨u, i, hi, hu, rfl⟩ := traceAll_inv (fun u => u.regs 3 = a) _ t h3
    (fun i hi u hu => by rw [next_regs_other u 3 (by decide) (hd i hi)]; exact hu) e he
  simp only [kch, le32, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · obtain ⟨-, h1, h2⟩ := ldrb_read u a hu 0 off (by omega) x hx
    exact ⟨0, by omega, h1, h2⟩
  · obtain ⟨-, h1, h2⟩ := ldrb_read u a hu 1 (off + 1) (by omega) x hx
    exact ⟨1, by omega, h1, h2⟩
  · simp [Instr.accesses] at hx
  · simp [Instr.accesses] at hx
  · obtain ⟨-, h1, h2⟩ := ldrb_read u a hu 1 (off + 2) (by omega) x hx
    exact ⟨2, by omega, h1, h2⟩
  · simp [Instr.accesses] at hx
  · simp [Instr.accesses] at hx
  · obtain ⟨-, h1, h2⟩ := ldrb_read u a hu 1 (off + 3) (by omega) x hx
    exact ⟨3, by omega, h1, h2⟩
  · simp [Instr.accesses] at hx
  · simp [Instr.accesses] at hx
  · simp [Instr.accesses] at hx; subst hx; simp at hk

/-- The caller-memory bytes read by the key and nonce loads. -/
def KNRd (c : Ctx) (y : Word) : Prop :=
  (∃ o < 32, y = c.key + BitVec.ofNat 32 o) ∨ (∃ o < 12, y = c.nonce + BitVec.ofNat 32 o)

/-- The accesses of one `LOAD_LE32; str` chunk: reads lie in `Rd`, writes in the frame. -/
theorem kch_accesses (c : Ctx) {Rd : Word → Prop} (allowed : Word → Kind → Word → Prop)
    (hS : ChaCha20Policy.AdmitsSite c.base c.Wr Rd allowed) (t : State) (i k off0 : Nat) (a : Word)
    (h4i : 4 * i + 3 < 32) (hk : k < chFrameWords) (h13 : t.regs 13 = c.fp) (h3 : t.regs 3 = a)
    (hRd : ∀ q < 4, Rd (a + BitVec.ofNat 32 (4 * i + q)))
    (hpc : t.pc = c.base + BitVec.ofNat 32 off0)
    (hs : ∀ j < kchSize, ChaCha20Policy.KNOff (off0 + j)) :
    ConstantTime.EventAccessesTo allowed (traceAll (kch (4 * i) k) t) := by
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  intro e he x hx q hq
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset (kch (4 * i) k) t (by simp [kch, le32, Instr.falls]) e he
  have hsite : ChaCha20Policy.KNPC c.base e.pc :=
    ⟨off0 + j, hs j (by rw [kch_size] at hj; exact hj), by rw [hep, hpc, ofNat_add_assoc]⟩
  apply hS _ _ _ hsite
  · intro hw
    have := frameWB_writes _ t (kch_frameWB (4 * i) k hk) e he _ ⟨x, hx, hw, q, hq, rfl⟩
    rw [h13] at this
    exact wr_frame this (by omega)
  · intro hr
    obtain ⟨q', hq', h1, h2⟩ := kch_reads (4 * i) k h4i t a h3 e he x hx hr
    rw [h2] at hq
    obtain rfl : q = 0 := by omega
    rw [h1, BitVec.add_zero]
    exact hRd q' hq'

/-- Facts during the key loads (offset `keyOff + kchSize * i`). -/
structure KInv (c : Ctx) (i : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 (keyOff + kchSize * i)
  sp : t.regs 13 = c.fp
  r3 : t.regs 3 = c.key
  r4 : t.regs 4 = c.ctr
  mem : c.MemOk 0 t.mem
  len : c.fw t slotLen = c.len
  outp : c.fw t slotOutp = c.out
  inp : c.fw t slotInp = c.inp
  cst : ∀ j < 4, c.fw t (slotJ + j) = c.J 0 j
  key : ∀ j < i, c.fw t (slotKey + j) = keyW c j

theorem key_loop_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hS : ChaCha20Policy.AdmitsSite c.base c.Wr (KNRd c) allowed)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (Q : State → Prop) :
    ∀ m i, i + m = 8 → ∀ t, KInv c i t → (∀ t', KInv c 8 t' → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) →
      ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q
  | 0, i, hm, t, h, k => by obtain rfl : i = 8 := by omega
                            exact k t h
  | m + 1, i, hm, t, h, k => by
    have sFW := ChaCha20Layout.chFrameWords_eq
    have sSB := ChaCha20Layout.chStackBytes_eq
    have sSW := ChaCha20Layout.chStackWords_eq
    have sKey : slotKey = 20 := by decide
    have sLen : slotLen = 32 := by decide
    have sOut : slotOutp = 33 := by decide
    have sInp : slotInp = 34 := by decide
    have sJ : slotJ = 16 := by decide
    have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
    have hseq : seqAt B (keyOff + kchSize * i) (kch (4 * i) (slotKey + i)) = true := by
      have := kch_at_key; simp only [List.all_eq_true, List.mem_range] at this; exact this i (by omega)
    apply ChaCha20Policy.blockP hPc hb2 _ _ h.pc (stride_even keyOff i (by decide)) hseq (by simp [kch, le32, Instr.falls])
      (kch_aligned t _ _ (by rw [h.sp]; exact fp4 hv))
      (kch_accesses c allowed hS t i (slotKey + i) (keyOff + kchSize * i) c.key (by omega) (by omega) h.sp h.r3
        (fun q hq => Or.inl ⟨4 * i + q, by omega, rfl⟩) h.pc
        (fun j hj => by
          have : kchSize * (i + 1) ≤ kchSize * 8 := Nat.mul_le_mul_left _ (by omega)
          have hd : keyOff + kchSize * 8 = stCtrOff := rfl
          rw [Nat.mul_succ] at this
          unfold ChaCha20Policy.KNOff; omega))
      (by have := chunk_fits keyOff 8 i (4 * i) (slotKey + i) (by omega) key_fits
          have : ChaCha20Layout.achOff ≤ ChaCha20Policy.chaEnd := by decide +kernel
          omega)
    apply key_loop_S c hv allowed hA hS hPc Q m (i + 1) (by omega) _ _ k
    obtain ⟨em, er⟩ := kch_step c hv t c.key 8 i (slotKey + i) hv.keyF (by omega) (by omega) (by omega) h.sp h.r3 h.mem
    have fw' : ∀ j, j < 2 ^ 28 → c.fw (execAll (kch (4 * i) (slotKey + i)) t) j =
        if slotKey + i = j then keyW c i else c.fw t j := fun j hj => c.fw_write em j (by omega) hj
    exact {
      pc := by rw [kch_pc, h.pc, ofNat_add_assoc, stride_succ]
      sp := by rw [er 13 (by decide) (by decide) (by decide), h.sp]
      r3 := by rw [er 3 (by decide) (by decide) (by decide), h.r3]
      r4 := by rw [er 4 (by decide) (by decide) (by decide), h.r4]
      mem := by rw [em]; exact c.memOk_write_slot h.mem _ (by omega) _
      len := by rw [fw' slotLen (by omega), if_neg (by omega), h.len]
      outp := by rw [fw' slotOutp (by omega), if_neg (by omega), h.outp]
      inp := by rw [fw' slotInp (by omega), if_neg (by omega), h.inp]
      cst := fun j hj => by rw [fw' _ (by omega), if_neg (by omega), h.cst j hj]
      key := fun j hj => by
        rw [fw' _ (by omega)]
        by_cases e : j = i
        · subst e; rw [if_pos rfl]
        · rw [if_neg (by omega), h.key j (by omega)] }

/-! ## Nonce loads -/

structure NInv (c : Ctx) (i : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 (nonOff + kchSize * i)
  sp : t.regs 13 = c.fp
  r3 : t.regs 3 = c.nonce
  mem : c.MemOk 0 t.mem
  len : c.fw t slotLen = c.len
  outp : c.fw t slotOutp = c.out
  inp : c.fw t slotInp = c.inp
  cst : ∀ j < 4, c.fw t (slotJ + j) = c.J 0 j
  key : ∀ j < 8, c.fw t (slotKey + j) = keyW c j
  ctr : c.fw t slotCtr = c.ctr
  non : ∀ j < i, c.fw t (slotNon + j) = nonceW c j

theorem nonce_loop_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hS : ChaCha20Policy.AdmitsSite c.base c.Wr (KNRd c) allowed)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (Q : State → Prop) :
    ∀ m i, i + m = 3 → ∀ t, NInv c i t → (∀ t', NInv c 3 t' → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) →
      ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q
  | 0, i, hm, t, h, k => by obtain rfl : i = 3 := by omega
                            exact k t h
  | m + 1, i, hm, t, h, k => by
    have sFW := ChaCha20Layout.chFrameWords_eq
    have sSB := ChaCha20Layout.chStackBytes_eq
    have sSW := ChaCha20Layout.chStackWords_eq
    have sKey : slotKey = 20 := by decide
    have sNon : slotNon = 29 := by decide
    have sLen : slotLen = 32 := by decide
    have sOut : slotOutp = 33 := by decide
    have sInp : slotInp = 34 := by decide
    have sCtr : slotCtr = 28 := by decide
    have sJ : slotJ = 16 := by decide
    have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
    have hseq : seqAt B (nonOff + kchSize * i) (kch (4 * i) (slotNon + i)) = true := by
      have := kch_at_nonce; simp only [List.all_eq_true, List.mem_range] at this; exact this i (by omega)
    apply ChaCha20Policy.blockP hPc hb2 _ _ h.pc (stride_even nonOff i (by decide)) hseq (by simp [kch, le32, Instr.falls])
      (kch_aligned t _ _ (by rw [h.sp]; exact fp4 hv))
      (kch_accesses c allowed hS t i (slotNon + i) (nonOff + kchSize * i) c.nonce (by omega) (by omega) h.sp h.r3
        (fun q hq => Or.inr ⟨4 * i + q, by omega, rfl⟩) h.pc
        (fun j hj => by
          have : kchSize * (i + 1) ≤ kchSize * 3 := Nat.mul_le_mul_left _ (by omega)
          have hd : nonOff + kchSize * 3 = bpreOff := rfl
          rw [Nat.mul_succ] at this
          unfold ChaCha20Policy.KNOff; omega))
      (by have := chunk_fits nonOff 3 i (4 * i) (slotNon + i) (by omega) nonce_fits
          have : ChaCha20Layout.achOff ≤ ChaCha20Policy.chaEnd := by decide +kernel
          omega)
    apply nonce_loop_S c hv allowed hA hS hPc Q m (i + 1) (by omega) _ _ k
    obtain ⟨em, er⟩ := kch_step c hv t c.nonce 3 i (slotNon + i) hv.nonceF (by omega) (by omega) (by omega) h.sp h.r3 h.mem
    have fw' : ∀ j, j < 2 ^ 28 → c.fw (execAll (kch (4 * i) (slotNon + i)) t) j =
        if slotNon + i = j then nonceW c i else c.fw t j := fun j hj => c.fw_write em j (by omega) hj
    exact {
      pc := by rw [kch_pc, h.pc, ofNat_add_assoc, stride_succ]
      sp := by rw [er 13 (by decide) (by decide) (by decide), h.sp]
      r3 := by rw [er 3 (by decide) (by decide) (by decide), h.r3]
      mem := by rw [em]; exact c.memOk_write_slot h.mem _ (by omega) _
      len := by rw [fw' slotLen (by omega), if_neg (by omega), h.len]
      outp := by rw [fw' slotOutp (by omega), if_neg (by omega), h.outp]
      inp := by rw [fw' slotInp (by omega), if_neg (by omega), h.inp]
      cst := fun j hj => by rw [fw' _ (by omega), if_neg (by omega), h.cst j hj]
      key := fun j hj => by rw [fw' _ (by omega), if_neg (by omega), h.key j hj]
      ctr := by rw [fw' slotCtr (by omega), if_neg (by omega), h.ctr]
      non := fun j hj => by
        rw [fw' _ (by omega)]
        by_cases e : j = i
        · subst e; rw [if_pos rfl]
        · rw [if_neg (by omega), h.non j (by omega)] }

/-! ## Single-instruction blocks -/

theorem disj_mono {a b : Word} {n m m' : Nat} (h : Disj a n b m) (hm : m' ≤ m) : Disj a n b m' := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by omega⟩

theorem codeAt_of_memOk (c : Ctx) (hv : Valid c) {m : Mem} (h : c.MemOk 0 m) : CodeAt m c.base B := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  intro i hi
  rw [B_len] at hi
  obtain ⟨hf, hs⟩ := disj_out c hv (disj_mono hv.codeF (by omega)) i hi
  rw [mem_m0 c h _ hf (by omega) hs]
  exact hv.code i (by rw [B_len]; exact hi)

theorem memOk_read32 (c : Ctx) {P : Nat} {m : Mem} (h : c.MemOk P m) (a : Word)
    (ha : ∀ q < 4, c.OutF (a + BitVec.ofNat 32 q) ∧ ¬ c.oidx (a + BitVec.ofNat 32 q) < P) :
    read32 m a = read32 c.mP a := by
  apply read32_congr
  intro k hk
  rw [h _ (ha k hk).1, ite_eq_right_of_eq_false _ _ (eq_false (ha k hk).2)]

theorem str_block_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (t : State) (off k : Nat) (src : LowReg) (hk : k < chFrameWords)
    (ho : off % 2 = 0) (hpc : t.pc = c.base + BitVec.ofNat 32 off)
    (hseq : seqAt B off [.strSp src (BitVec.ofNat 8 k)] = true)
    (hlt : ChaCha20Policy.FrontRange off (seqSize [.strSp src (BitVec.ofNat 8 k)]))
    (h13 : t.regs 13 = c.fp) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (off + 2) →
      t'.mem = write32 t.mem (slot c.fp k) (t.regs src.toReg) →
      (∀ r : Reg, r.val ≠ 15 → t'.regs r = t.regs r) → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) :
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have hk' : (BitVec.ofNat 8 k).toNat = k := by simp; omega
  apply ChaCha20Policy.frontBlockP hA hPc hb2 _ off hpc ho hseq (by simp [Instr.falls])
    (by simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.sp, h13, List.all_cons, List.all_nil,
          Access.aligned, Bool.and_true, beq_iff_eq, hk', BitVec.toNat_add, BitVec.toNat_ofNat]
        have := fp4 hv; omega)
    (fun e he y hy => wr_frame (by
      have := frameWB_writes (n := chFrameWords) [.strSp src (BitVec.ofNat 8 k)] t (by simp [frameWB, hk', hk]) e he y hy
      rwa [h13] at this) (by omega))
    hlt
  apply cont
  · rw [execAll_pc _ _ (by simp [Instr.falls]), hpc, ofNat_add_assoc]; rfl
  · simp only [execAll, strSp_next t src k (by omega), h13]
  · intro r hr; simp only [execAll, strSp_next t src k (by omega)]; exact setReg15_regs _ _ r hr

/-- `ldr r0, [pc, #imm]; str r0, [sp, #4k]` at offset `off` (≡ 2 mod 4), loading the word at `pool`.
The ldr immediate is `litImm off pool`, so the literal pool offset is the only layout input. -/
theorem lit_block_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (t : State) (off pool k : Nat) (hk : k < chFrameWords) (ho : off % 4 = 2)
    (hp : pool % 4 = 0) (hle : (off + 4) / 4 * 4 ≤ pool) (hi : litImm off pool < 256)
    (hpsz : pool + 4 ≤ Artifacts.Release.size) (hpc : t.pc = c.base + BitVec.ofNat 32 off)
    (hseq : seqAt B off [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool)), .strSp 0 (BitVec.ofNat 8 k)] = true)
    (hlt : ChaCha20Policy.FrontRange off (seqSize [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool)), .strSp 0 (BitVec.ofNat 8 k)]))
    (h13 : t.regs 13 = c.fp) (hm : c.MemOk 0 t.mem) (Q : State → Prop)
    (cont : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (off + 4) →
      t'.mem = write32 t.mem (slot c.fp k) (codeWord pool) →
      (∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → t'.regs r = t.regs r) → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) :
    ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have hk' : (BitVec.ofNat 8 k).toNat = k := by simp; omega
  have hli : (BitVec.ofNat 8 (litImm off pool)).toNat = litImm off pool := by simp; omega
  have hcode := hv.codeF.1
  have hld := litImm_target off pool hp hle
  have hla : ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((BitVec.ofNat 8 (litImm off pool)).toNat * 4) =
      c.base + BitVec.ofNat 32 pool := by
    rw [hli, hpc, lit_addr c.base hv.base4 off (litImm off pool) (by omega), hld]
  have hv0 : read32 t.mem (c.base + BitVec.ofNat 32 pool) = codeWord pool :=
    read32_code (codeAt_of_memOk c hv hm) _ (by omega)
  obtain ⟨em, er⟩ := store_effect t [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool))] k (by omega)
    (by simp [Instr.writesMem])
  have e1 : execAll [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool))] t =
      (t.setReg 15 (t.pc + 2#32)).setReg 0 (codeWord pool) := by
    simp only [execAll, Instr.next, Instr.exec, M0Crypto.Proofs.toReg_0, hla, hv0]; rfl
  apply ChaCha20Policy.frontBlockP hA hPc hb2 _ off hpc (by omega) hseq (by simp [Instr.falls])
    (by simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.sp, List.all_cons, List.all_nil,
          Access.aligned, Bool.and_true, beq_iff_eq, hk']
        rw [hla]
        simp only [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Proofs.toReg_0]
        simp (config := { decide := true }) only [ite_false, h13, Bool.and_eq_true, decide_eq_true_eq,
          BitVec.toNat_add, BitVec.toNat_ofNat]
        have := fp4 hv; have := hv.base4
        simp only [beq_iff_eq, Bool.and_eq_true]; omega)
    (fun e he y hy => wr_frame (by
      have := frameWB_writes (n := chFrameWords) [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool)), .strSp 0 (BitVec.ofNat 8 k)] t
        (by simp [frameWB, hk', hk, Instr.writesMem, Instr.dsts]) e he y hy
      rwa [h13] at this) (by omega))
    hlt
  have r13 : (execAll [.ldrLit 0 (BitVec.ofNat 8 (litImm off pool))] t).regs 13 = t.regs 13 := by
    rw [e1]; rw [setReg_regs_ne _ _ _ _ (by decide), setReg15_regs _ _ 13 (by decide)]
  apply cont
  · rw [execAll_pc _ _ (by simp [Instr.falls]), hpc, ofNat_add_assoc]; rfl
  · show (execAll ([.ldrLit 0 (BitVec.ofNat 8 (litImm off pool))] ++ [.strSp 0 (BitVec.ofNat 8 k)]) t).mem = _
    rw [em, r13, h13, e1]; simp [M0Crypto.Armv6M.State.setReg]
  · intro r h0 h15
    show (execAll ([.ldrLit 0 (BitVec.ofNat 8 (litImm off pool))] ++ [.strSp 0 (BitVec.ofNat 8 k)]) t).regs r = _
    rw [er r h15, e1, setReg_regs_ne _ _ _ _ (fun e => h0 (by rw [e]; rfl)), setReg15_regs _ _ r h15]

/-! ## From the accepted check to `.Lblock` -/

theorem cw0 : codeWord poolOff = 0x61707865#32 := by decide
theorem cw1 : codeWord (poolOff + 4) = 0x3320646e#32 := by decide
theorem cw2 : codeWord (poolOff + 8) = 0x79622d32#32 := by decide
theorem cw3 : codeWord (poolOff + 12) = 0x6b206574#32 := by decide

theorem b48_at : instrAt B b7Off = some (.b 7) := by decide

/-- Fall-through steps between consecutive pieces of `init`, as decided facts for `rw`. -/
theorem stCtr_next : stCtrOff + 2 = ldrNonceOff := by decide
theorem ldrNonce_next : ldrNonceOff + 2 = nonOff := by decide
theorem litJ3_next : litJ3Off + 4 = b7Off := by decide
theorem nonce_end : nonOff + kchSize * 3 = bpreOff := by decide

/-- After a store to slot `k`, other slots keep their values. -/
theorem fw_other (c : Ctx) {t t' : State} {k : Nat} {v : Word} (h : t'.mem = write32 t.mem (slot c.fp k) v)
    (j : Nat) (hk : k < 64) (hj : j < 64) (hne : k ≠ j) : c.fw t' j = c.fw t j := by
  rw [c.fw_write h j (by omega) (by omega), if_neg hne]; rfl

theorem fw_same (c : Ctx) {t t' : State} {k : Nat} {v : Word} (h : t'.mem = write32 t.mem (slot c.fp k) v)
    (hk : k < 64) : c.fw t' k = v := by
  rw [c.fw_write h k (by omega) (by omega), if_pos rfl]

theorem init_S {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hS : ChaCha20Policy.AdmitsSite c.base c.Wr (KNRd c) allowed)
    (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc) (t : State) (h : Acc c t) (Q : State → Prop)
    (k : ∀ t', BlockInv c 0 t' → ReachS c.base (ChaCha20Policy.EvP Pc allowed) t' Q) : ReachS c.base (ChaCha20Policy.EvP Pc allowed) t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have m0 : c.MemOk 0 t.mem := by intro y _; rw [h.mem]; rfl
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have sOut : slotOutp = 33 := by decide
  have sInp : slotInp = 34 := by decide
  have sLen : slotLen = 32 := by decide
  have sJ : slotJ = 16 := by decide
  have sCtr : slotCtr = 28 := by decide
  have sAN : slotArgNonce = ChaCha20Layout.chStackWords := rfl
  have sKey : slotKey = 20 := by decide
  have sNon : slotNon = 29 := by decide
  -- OUTP, INP, LEN
  apply str_block_S c hv allowed hA hPc t accOff slotOutp 0 (by decide) (by decide) h.pc (by decide) (by decide) h.sp
  intro t1 p1 e1 r1
  apply str_block_S c hv allowed hA hPc t1 stInpOff slotInp 1 (by decide) (by decide) p1 (by decide) (by decide)
    (by rw [r1 13 (by decide), h.sp])
  intro t2 p2 e2 r2
  apply str_block_S c hv allowed hA hPc t2 stLenOff slotLen 2 (by decide) (by decide) p2 (by decide) (by decide)
    (by rw [r2 13 (by decide), r1 13 (by decide), h.sp])
  intro t3 p3 e3 r3
  have s3 : t3.regs 13 = c.fp := by rw [r3 13 (by decide), r2 13 (by decide), r1 13 (by decide), h.sp]
  have m3 : c.MemOk 0 t3.mem := by
    rw [e3, e2, e1]
    exact c.memOk_write_slot (c.memOk_write_slot (c.memOk_write_slot m0 _ (by decide) _) _ (by decide) _) _ (by decide) _
  -- constants
  apply lit_block_S c hv allowed hA hPc t3 litJ0Off poolOff slotJ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) p3 (by decide) (by decide) s3 m3
  intro t4 p4 e4 r4
  have s4 : t4.regs 13 = c.fp := by rw [r4 13 (by decide) (by decide), s3]
  have m4 : c.MemOk 0 t4.mem := by rw [e4]; exact c.memOk_write_slot m3 _ (by decide) _
  apply lit_block_S c hv allowed hA hPc t4 litJ1Off (poolOff + 4) (slotJ + 1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) p4 (by decide) (by decide) s4 m4
  intro t5 p5 e5 r5
  have s5 : t5.regs 13 = c.fp := by rw [r5 13 (by decide) (by decide), s4]
  have m5 : c.MemOk 0 t5.mem := by rw [e5]; exact c.memOk_write_slot m4 _ (by decide) _
  apply lit_block_S c hv allowed hA hPc t5 litJ2Off (poolOff + 8) (slotJ + 2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) p5 (by decide) (by decide) s5 m5
  intro t6 p6 e6 r6
  have s6 : t6.regs 13 = c.fp := by rw [r6 13 (by decide) (by decide), s5]
  have m6 : c.MemOk 0 t6.mem := by rw [e6]; exact c.memOk_write_slot m5 _ (by decide) _
  apply lit_block_S c hv allowed hA hPc t6 litJ3Off (poolOff + 12) (slotJ + 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) p6 (by decide) (by decide) s6 m6
  intro t7 p7 e7 r7
  have s7 : t7.regs 13 = c.fp := by rw [r7 13 (by decide) (by decide), s6]
  have m7 : c.MemOk 0 t7.mem := by rw [e7]; exact c.memOk_write_slot m6 _ (by decide) _
  -- b keyOff
  apply ChaCha20Policy.evB hb2 b7Off keyOff 7 p7 (by decide) b48_at (by decide) (by decide) (hr := ChaCha20Policy.chaAt hPc (by decide +kernel))
  have rr : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 15 → t7.regs r = t.regs r := fun r h0 h15 => by
    rw [r7 r h0 h15, r6 r h0 h15, r5 r h0 h15, r4 r h0 h15, r3 r h15, r2 r h15, r1 r h15]
  -- frame words from keyOff
  have f7 : ∀ j, j < 64 → j ≠ slotJ → j ≠ slotJ + 1 → j ≠ slotJ + 2 → j ≠ slotJ + 3 → c.fw t7 j = c.fw t3 j := by
    intro j hj a b d e
    rw [fw_other c e7 j (by omega) hj (by omega), fw_other c e6 j (by omega) hj (by omega),
      fw_other c e5 j (by omega) hj (by omega), fw_other c e4 j (by omega) hj (by omega)]
  apply key_loop_S c hv allowed hA hS hPc Q 8 0 rfl (t7.setReg 15 (c.base + BitVec.ofNat 32 keyOff)) {
    pc := by rw [setReg15_pc, Nat.mul_zero, Nat.add_zero]
    sp := by rw [setReg15_regs _ _ 13 (by decide), s7]
    r3 := by rw [setReg15_regs _ _ 3 (by decide), rr 3 (by decide) (by decide), h.r3]
    r4 := by rw [setReg15_regs _ _ 4 (by decide), rr 4 (by decide) (by decide), h.r4]
    mem := m7
    len := by
      show c.fw t7 slotLen = _
      rw [f7 slotLen (by omega) (by omega) (by omega) (by omega) (by omega), fw_same c e3 (by omega), M0Crypto.Proofs.toReg_2, r2 2 (by decide),
        r1 2 (by decide), h.r2]
    outp := by
      show c.fw t7 slotOutp = _
      rw [f7 slotOutp (by omega) (by omega) (by omega) (by omega) (by omega), fw_other c e3 slotOutp (by omega) (by omega) (by omega),
        fw_other c e2 slotOutp (by omega) (by omega) (by omega), fw_same c e1 (by omega), M0Crypto.Proofs.toReg_0, h.r0]
    inp := by
      show c.fw t7 slotInp = _
      rw [f7 slotInp (by omega) (by omega) (by omega) (by omega) (by omega), fw_other c e3 slotInp (by omega) (by omega) (by omega),
        fw_same c e2 (by omega), M0Crypto.Proofs.toReg_1, r1 1 (by decide), h.r1]
    cst := fun j hj => by
      obtain ⟨j0, j1, j2, j3⟩ := J_const c 0
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · show c.fw t7 slotJ = _
        rw [fw_other c e7 _ (by omega) (by omega) (by omega), fw_other c e6 _ (by omega) (by omega) (by omega),
          fw_other c e5 _ (by omega) (by omega) (by omega), fw_same c e4 (by omega), j0, cw0]
      · show c.fw t7 (slotJ + 1) = _
        rw [fw_other c e7 _ (by omega) (by omega) (by omega), fw_other c e6 _ (by omega) (by omega) (by omega),
          fw_same c e5 (by omega), j1, cw1]
      · show c.fw t7 (slotJ + 2) = _
        rw [fw_other c e7 _ (by omega) (by omega) (by omega), fw_same c e6 (by omega), j2, cw2]
      · show c.fw t7 (slotJ + 3) = _
        rw [fw_same c e7 (by omega), j3, cw3]
    key := fun j hj => absurd hj (by omega) }
  intro t8 h8
  -- str r4, [sp, #112]: j[12] = counter
  apply str_block_S c hv allowed hA hPc t8 stCtrOff slotCtr 4 (by decide) (by decide) h8.pc (by decide) (by decide) h8.sp
  intro t9 p9 e9 r9
  rw [stCtr_next] at p9
  have s9 : t9.regs 13 = c.fp := by rw [r9 13 (by decide), h8.sp]
  have m9 : c.MemOk 0 t9.mem := by rw [e9]; exact c.memOk_write_slot h8.mem _ (by decide) _
  -- ldr r3, [sp, #176]: the nonce pointer
  have hsl : c.fp + BitVec.ofNat 32 ((BitVec.ofNat 8 slotArgNonce).toNat * 4) = c.sp0 + BitVec.ofNat 32 0 := by
    rw [sAN, ChaCha20Layout.chStackWords_eq]; simp only [Ctx.fp]; simp; bv_omega
  have hn : read32 t9.mem (c.fp + BitVec.ofNat 32 ((BitVec.ofNat 8 slotArgNonce).toNat * 4)) = c.nonce := by
    rw [hsl, memOk_read32 c m9]
    · rw [ChaCha20Return.mP_above c hv 0 (by have := hv.outF; simp only [Disj] at this; rw [fp_toNat hv] at this; omega)]
      simpa using h.argN
    · intro q hq
      refine ⟨fun o ho e => ?_, by omega⟩
      have he := congrArg BitVec.toNat e
      have h1 := hv.spLo; have h2 := hv.outF.2.1; have hf := fp_toNat hv
      have sFB := ChaCha20Layout.chFrameBytes_eq
      rw [ofNat_add_assoc, toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at he
      omega
  apply ChaCha20Policy.frontBlockP hA hPc hb2 [.ldrSp 3 (BitVec.ofNat 8 slotArgNonce)] ldrNonceOff p9 (by decide) (by decide) (by decide)
    (by simp only [alignedAll, Instr.accesses, M0Crypto.Armv6M.State.sp, s9, List.all_cons, List.all_nil,
          Access.aligned, Bool.and_true, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := fp4 hv; simp; omega)
    (fun e he y ⟨a, ha, hw, _⟩ => by
      simp only [traceAll, List.mem_cons, List.not_mem_nil, or_false] at he; subst he
      simp only [Instr.accesses, List.mem_singleton] at ha; subst ha; cases hw)
    (by decide)
  have e10 : execAll [.ldrSp 3 (BitVec.ofNat 8 slotArgNonce)] t9 = (t9.setReg 15 (t9.pc + 2#32)).setReg 3 c.nonce := by
    simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.sp, s9, hn, M0Crypto.Proofs.toReg_3]; rfl
  rw [e10]
  have rr : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → t9.regs r = t8.regs r := fun r _ _ h15 => r9 r h15
  have f9 : ∀ j, j < 64 → j ≠ slotCtr → c.fw t9 j = c.fw t8 j := fun j hj hne =>
    fw_other c e9 j (by omega) hj (Ne.symm hne)
  apply nonce_loop_S c hv allowed hA hS hPc Q 3 0 rfl ((t9.setReg 15 (t9.pc + 2#32)).setReg 3 c.nonce) {
    pc := by
      show ((t9.setReg 15 (t9.pc + 2#32)).setReg 3 c.nonce).regs 15 = _
      rw [setReg_regs_ne _ _ _ _ (by decide)]
      show (t9.setReg 15 (t9.pc + 2#32)).pc = _
      rw [setReg15_pc, p9, ofNat_add_assoc, ldrNonce_next, Nat.mul_zero, Nat.add_zero]
    sp := by rw [setReg_regs_ne _ _ _ _ (by decide), setReg15_regs _ _ 13 (by decide), s9]
    r3 := by simp [M0Crypto.Armv6M.State.setReg]
    mem := m9
    len := by show c.fw t9 slotLen = _; rw [f9 slotLen (by omega) (by omega)]; exact h8.len
    outp := by show c.fw t9 slotOutp = _; rw [f9 slotOutp (by omega) (by omega)]; exact h8.outp
    inp := by show c.fw t9 slotInp = _; rw [f9 slotInp (by omega) (by omega)]; exact h8.inp
    cst := fun j hj => by show c.fw t9 (slotJ + j) = _; rw [f9 _ (by omega) (by omega)]; exact h8.cst j hj
    key := fun j hj => by show c.fw t9 (slotKey + j) = _; rw [f9 _ (by omega) (by omega), h8.key j hj]
    ctr := by show c.fw t9 slotCtr = _; rw [fw_same c e9 (by omega), M0Crypto.Proofs.toReg_4, h8.r4]
    non := fun j hj => absurd hj (by omega) }
  intro t11 h11
  apply k
  exact {
    pc := by rw [h11.pc, nonce_end]
    sp := h11.sp
    j := fun i hi => by
      by_cases a : i < 4
      · exact h11.cst i a
      by_cases b : i < 12
      · have := h11.key (i - 4) (by omega)
        rw [show slotKey + (i - 4) = slotJ + i by omega] at this
        rw [this, show i = 4 + (i - 4) by omega, J_key c 0 _ (by omega)]
        congr 1; omega
      by_cases d : i = 12
      · subst d; show c.fw t11 slotCtr = _; rw [h11.ctr, J_ctr]; simp
      · have := h11.non (i - 13) (by omega)
        rw [show slotNon + (i - 13) = slotJ + i by omega] at this
        rw [this, show i = 13 + (i - 13) by omega, J_nonce c 0 _ (by omega)]
        congr 1; omega
    len := by rw [h11.len]; simp
    outp := by rw [h11.outp]; simp
    inp := by rw [h11.inp]; simp
    mem := by simpa using h11.mem
    lt := by
      have := h.ne
      have : c.len.toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq (by simpa using e))
      omega
    ok := h.ok }

/-! ## Statements without access events -/

theorem init_events (c : Ctx) (hv : Valid c) (allowed : Word → Kind → Word → Prop) (hA : ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr allowed)
    (hS : ChaCha20Policy.AdmitsSite c.base c.Wr (KNRd c) allowed) (t : State) (h : Acc c t) (Q : State → Prop)
    (k : ∀ t', BlockInv c 0 t' → ConstantTime.ReachEvents c.base allowed t' Q) : ConstantTime.ReachEvents c.base allowed t Q :=
  ChaCha20Policy.ofEvP (init_S (Pc := fun _ => True) c hv allowed hA hS (fun _ _ => trivial) t h Q
    (fun t' h' => ChaCha20Policy.reachEvents_toEvP (k t' h')))

/-- The key and nonce loads and the frame set-up, with every program counter in `Pc`. -/
theorem init_w {Pc : Word → Prop} (c : Ctx) (hv : Valid c) (hPc : ∀ pc, ChaCha20Policy.ChaPc c.base pc → Pc pc)
    (t : State) (h : Acc c t) (Q : State → Prop)
    (k : ∀ t', BlockInv c 0 t' → ReachW c.base Pc c.Wr t' Q) : ReachW c.base Pc c.Wr t Q :=
  ChaCha20Policy.ofEvPW
    (init_S c hv _ (ChaCha20Policy.admits_writeOnly _ c.Wr) (ChaCha20Policy.admitsSite_writeOnly _ _ _) hPc t h Q
      (fun t' h' => ChaCha20Policy.reachW_toEvP (k t' h')))

theorem init (c : Ctx) (hv : Valid c) (t : State) (h : Acc c t) (Q : State → Prop)
    (k : ∀ t', BlockInv c 0 t' → Reach c.base c.Wr t' Q) : Reach c.base c.Wr t Q :=
  (init_w (Pc := fun _ => True) c hv (fun _ _ => trivial) t h Q
    (fun t' h' => (k t' h').toReachW)).toReach

end M0Crypto.Release.ChaCha20Init
