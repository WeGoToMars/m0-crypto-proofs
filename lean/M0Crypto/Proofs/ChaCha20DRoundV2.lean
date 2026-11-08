import M0Crypto.Proofs.ChaCha20DRound
import M0Crypto.Artifacts.ChaCha20DRoundV2

/-!
Schedule-change replay: refinement proof for `m0c_chacha20_dround_v2_frag`
(fixtures/chacha20_dround_v2.S). It is version 1 with `x[15]` kept in r3 across the
column → diagonal boundary (one `STR` and one `LDR` removed).

Reused unchanged from version 1 (`M0Crypto.Proofs.ChaCha20DRound`): the register
quarter-round core (`core_spec`, `core_frame`), the 4-word loads/stores, the full
`block_*` lemmas for the 6 unchanged blocks, `qroundF`/`innerBlockF`, and the
`Array` spec bridge. New: 3-word load/store wrappers and the two boundary blocks
with a register-residency hypothesis (`x[d]` lives in r3, not in its stack slot).
-/

namespace M0Crypto.Proofs.ChaCha20DRoundV2

open M0Crypto.Armv6M
open M0Crypto.Spec.ChaCha20 (quarterRound innerBlock)
open M0Crypto.Proofs
open M0Crypto.Proofs.ChaCha20DRound

/-! ## New wrappers and boundary blocks -/

def loads3 (a b c : Nat) : List Instr :=
  [ .ldrSp 0 (BitVec.ofNat 8 a), .ldrSp 1 (BitVec.ofNat 8 b), .ldrSp 2 (BitVec.ofNat 8 c) ]

def stores3 (a b c : Nat) : List Instr :=
  [ .strSp 0 (BitVec.ofNat 8 a), .strSp 1 (BitVec.ofNat 8 b), .strSp 2 (BitVec.ofNat 8 c) ]

/-- Quarter round that leaves `x[d]` in r3 instead of storing it. -/
def keepBlock (a b c d : Nat) : List Instr := loads a b c d ++ core ++ stores3 a b c

/-- Quarter round that takes `x[d]` from r3 instead of loading it. -/
def haveBlock (a b c d : Nat) : List Instr := loads3 a b c ++ core ++ stores a b c d

def instrs : List Instr :=
  block 0 4 8 12 ++ block 1 5 9 13 ++ block 2 6 10 14 ++ keepBlock 3 7 11 15 ++
  haveBlock 0 5 10 15 ++ block 1 6 11 12 ++ block 2 7 8 13 ++ block 3 4 9 14

def code : Code := ⟨Artifacts.ChaCha20DRoundV2.base, Artifacts.ChaCha20DRoundV2.bytes⟩

set_option maxRecDepth 20000 in
theorem instrs_length : instrs.length = 158 := by decide

set_option maxRecDepth 20000 in
/-- The extracted bytes decode exactly to `instrs` from the link address. -/
theorem decodes : decodesAt code code.base instrs = true := by decide

theorem loads3_frame (s : State) (a b c : Nat) :
    let s' := execAll (loads3 a b c) s
    s'.mem = s.mem ∧ (∀ r : Reg, 3 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) := by
  refine ⟨execAll_mem _ s (by simp [loads3, Instr.isStore]), fun r h3 h14 => ?_⟩
  apply execAll_regs_other _ s r (by omega)
  simp only [loads3, List.mem_cons, List.not_mem_nil, or_false]
  rintro i (rfl | rfl | rfl) <;> simp [Instr.dst] <;> omega

theorem loads3_spec (s : State) (a b c : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) :
    let s' := execAll (loads3 a b c) s
    s'.regs 0 = view s a ∧ s'.regs 1 = view s b ∧ s'.regs 2 = view s c := by
  simp only [execAll, loads3, exec, State.setReg, State.pc, toReg_0, toReg_1, toReg_2]
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false]
  simp only [spAddr_slot _ _ ha, spAddr_slot _ _ hb, spAddr_slot _ _ hc]
  simp (config := { decide := true }) only [Fin.isValue, ite_false, view, and_self]

theorem stores3_frame (s : State) (a b c : Nat) :
    let s' := execAll (stores3 a b c) s
    ∀ r : Reg, r.val ≠ 15 → s'.regs r = s.regs r := by
  intro s' r h15
  apply execAll_regs_other _ s r h15
  simp only [stores3, List.mem_cons, List.not_mem_nil, or_false]
  rintro i (rfl | rfl | rfl) <;> simp [Instr.dst] <;> omega

theorem stores3_spec (s : State) (a b c : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) :
    (execAll (stores3 a b c) s).mem =
      write32 (write32 (write32 s.mem (slot (s.regs 13) a) (s.regs 0))
        (slot (s.regs 13) b) (s.regs 1)) (slot (s.regs 13) c) (s.regs 2) := by
  simp only [execAll, stores3, exec, State.setReg, State.pc, State.reg, toReg_0, toReg_1, toReg_2]
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false]
  simp only [spAddr_slot _ _ ha, spAddr_slot _ _ hb, spAddr_slot _ _ hc]
  simp (config := { decide := true }) only [Fin.isValue, ite_false]

/-! ### `keepBlock` -/

theorem keep_regs (s : State) (a b c d : Nat) (r : Reg) (h4 : 4 ≤ r.val) (h14 : r.val ≤ 14) :
    (execAll (keepBlock a b c d) s).regs r = s.regs r := by
  simp only [keepBlock, execAll_append]
  rw [stores3_frame _ a b c r (by omega), (core_frame _).2 r h4 h14,
    (loads_frame s a b c d).2 r h4 h14]

theorem keep_rot (s : State) (a b c d : Nat) (h : RotRegs s) :
    RotRegs (execAll (keepBlock a b c d) s) :=
  ⟨by rw [keep_regs s a b c d 4 (by decide) (by decide)]; exact h.r4,
   by rw [keep_regs s a b c d 5 (by decide) (by decide)]; exact h.r5,
   by rw [keep_regs s a b c d 6 (by decide) (by decide)]; exact h.r6,
   by rw [keep_regs s a b c d 7 (by decide) (by decide)]; exact h.r7⟩

/-- Memory and r3 after `keepBlock`: three word writes, and `x[d]`'s new value in r3. -/
theorem keep_state (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    let q := quarterRound (view s a) (view s b) (view s c) (view s d)
    (execAll (keepBlock a b c d) s).mem =
      write32 (write32 (write32 s.mem (slot (s.regs 13) a) q.1)
        (slot (s.regs 13) b) q.2.1) (slot (s.regs 13) c) q.2.2.1 ∧
    (execAll (keepBlock a b c d) s).regs 3 = q.2.2.2 := by
  obtain ⟨l0, l1, l2, l3⟩ := loads_spec s a b c d ha hb hc hd
  obtain ⟨m1, r1⟩ := loads_frame s a b c d
  have hrot1 : RotRegs (execAll (loads a b c d) s) :=
    ⟨by rw [r1 4 (by decide) (by decide)]; exact h.r4,
     by rw [r1 5 (by decide) (by decide)]; exact h.r5,
     by rw [r1 6 (by decide) (by decide)]; exact h.r6,
     by rw [r1 7 (by decide) (by decide)]; exact h.r7⟩
  have hq := core_spec _ hrot1
  obtain ⟨m2, r2⟩ := core_frame (execAll (loads a b c d) s)
  rw [l0, l1, l2, l3] at hq
  simp only [keepBlock, execAll_append]
  refine ⟨?_, ?_⟩
  · rw [stores3_spec _ a b c ha hb hc, r2 13 (by decide) (by decide),
      r1 13 (by decide) (by decide), m2, m1]
    simp only [← hq]
  · rw [stores3_frame _ a b c 3 (by decide)]
    simp only [← hq]

/-- After `keepBlock`, every stack word except `x[d]` matches `qroundF`, and r3 holds
`x[d]`'s new value (its stack slot is stale). -/
theorem keep_spec (s : State) (h : RotRegs s) (f : Nat → Armv6M.Word) (hf : Agree (view s) f)
    (a b c d : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    (∀ k, k < 16 → k ≠ d →
      view (execAll (keepBlock a b c d) s) k = qroundF f a b c d k) ∧
    (execAll (keepBlock a b c d) s).regs 3 = qroundF f a b c d d := by
  obtain ⟨hm, h3⟩ := keep_state s h a b c d ha hb hc hd
  refine ⟨fun k hk hkd => ?_, ?_⟩
  · unfold view
    rw [keep_regs s a b c d 13 (by decide) (by decide), hm]
    simp only [read32_write32_slot _ _ _ _ _ hc hk, read32_write32_slot _ _ _ _ _ hb hk,
      read32_write32_slot _ _ _ _ _ ha hk]
    simp only [qroundF, upd, hf a ha, hf b hb, hf c hc, hf d hd, show ¬(d = k) from fun e => hkd e.symm,
      ite_false]
    have hk' : read32 s.mem (slot (s.regs 13) k) = f k := hf k hk
    rw [hk']
  · rw [h3]
    simp only [qroundF, upd, hf a ha, hf b hb, hf c hc, hf d hd, ite_true]

/-! ### `haveBlock` -/

theorem have_regs (s : State) (a b c d : Nat) (r : Reg) (h4 : 4 ≤ r.val) (h14 : r.val ≤ 14) :
    (execAll (haveBlock a b c d) s).regs r = s.regs r := by
  simp only [haveBlock, execAll_append]
  rw [stores_frame _ a b c d r (by omega), (core_frame _).2 r h4 h14,
    (loads3_frame s a b c).2 r (by omega) h14]

theorem have_rot (s : State) (a b c d : Nat) (h : RotRegs s) :
    RotRegs (execAll (haveBlock a b c d) s) :=
  ⟨by rw [have_regs s a b c d 4 (by decide) (by decide)]; exact h.r4,
   by rw [have_regs s a b c d 5 (by decide) (by decide)]; exact h.r5,
   by rw [have_regs s a b c d 6 (by decide) (by decide)]; exact h.r6,
   by rw [have_regs s a b c d 7 (by decide) (by decide)]; exact h.r7⟩

theorem have_mem (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    (execAll (haveBlock a b c d) s).mem =
      let q := quarterRound (view s a) (view s b) (view s c) (s.regs 3)
      write32 (write32 (write32 (write32 s.mem (slot (s.regs 13) a) q.1)
        (slot (s.regs 13) b) q.2.1) (slot (s.regs 13) c) q.2.2.1)
        (slot (s.regs 13) d) q.2.2.2 := by
  obtain ⟨l0, l1, l2⟩ := loads3_spec s a b c ha hb hc
  obtain ⟨m1, r1⟩ := loads3_frame s a b c
  have hrot1 : RotRegs (execAll (loads3 a b c) s) :=
    ⟨by rw [r1 4 (by decide) (by decide)]; exact h.r4,
     by rw [r1 5 (by decide) (by decide)]; exact h.r5,
     by rw [r1 6 (by decide) (by decide)]; exact h.r6,
     by rw [r1 7 (by decide) (by decide)]; exact h.r7⟩
  have hq := core_spec _ hrot1
  obtain ⟨m2, r2⟩ := core_frame (execAll (loads3 a b c) s)
  rw [l0, l1, l2, r1 3 (by decide) (by decide)] at hq
  simp only [haveBlock, execAll_append]
  rw [stores_spec _ a b c d ha hb hc hd, r2 13 (by decide) (by decide),
    r1 13 (by decide) (by decide), m2, m1]
  simp only [← hq]

/-- Residency hypothesis: the stack agrees with `g` except at slot `d`, whose current
value `g d` is in r3. Then `haveBlock` restores full agreement with `qroundF g`. -/
theorem have_spec (s : State) (h : RotRegs s) (g : Nat → Armv6M.Word)
    (a b c d : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hg : ∀ k, k < 16 → k ≠ d → view s k = g k) (h3 : s.regs 3 = g d) :
    Agree (view (execAll (haveBlock a b c d) s)) (qroundF g a b c d) := by
  intro k hk
  unfold view
  rw [have_regs s a b c d 13 (by decide) (by decide), have_mem s h a b c d ha hb hc hd]
  simp only [read32_write32_slot _ _ _ _ _ hd hk, read32_write32_slot _ _ _ _ _ hc hk,
    read32_write32_slot _ _ _ _ _ hb hk, read32_write32_slot _ _ _ _ _ ha hk]
  rw [hg a ha had, hg b hb hbd, hg c hc hcd, h3]
  simp only [qroundF, upd]
  by_cases hkd : d = k
  · simp only [hkd, ite_true]
  · simp only [hkd, ite_false]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact hg k hk (fun e => hkd e.symm)

/-! ### Memory frame for the boundary blocks -/

theorem keep_mem_other (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (y : Armv6M.Word)
    (hy : ∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) :
    (execAll (keepBlock a b c d) s).mem y = s.mem y := by
  have hw : ∀ (m : Mem) (i : Nat) (v : Armv6M.Word), i < 16 →
      write32 m (slot (s.regs 13) i) v y = m y := by
    intro m i v hi
    apply write32_other
    intro k hk
    have := hy (4 * i + k) (by omega)
    rwa [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [(keep_state s h a b c d ha hb hc hd).1]
  simp only [hw _ _ _ hc, hw _ _ _ hb, hw _ _ _ ha]

theorem have_mem_other (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (y : Armv6M.Word)
    (hy : ∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) :
    (execAll (haveBlock a b c d) s).mem y = s.mem y := by
  have hw : ∀ (m : Mem) (i : Nat) (v : Armv6M.Word), i < 16 →
      write32 m (slot (s.regs 13) i) v y = m y := by
    intro m i v hi
    apply write32_other
    intro k hk
    have := hy (4 * i + k) (by omega)
    rwa [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [have_mem s h a b c d ha hb hc hd]
  simp only [hw _ _ _ hd, hw _ _ _ hc, hw _ _ _ hb, hw _ _ _ ha]

/-! ## Composition -/

theorem instrs_exec (s : State) :
    execAll instrs s =
      execAll (block 3 4 9 14) (execAll (block 2 7 8 13) (execAll (block 1 6 11 12)
        (execAll (haveBlock 0 5 10 15) (execAll (keepBlock 3 7 11 15) (execAll (block 2 6 10 14)
          (execAll (block 1 5 9 13) (execAll (block 0 4 8 12) s))))))) := by
  simp only [instrs, execAll_append]

theorem dround_view (s : State) (h : RotRegs s) :
    Agree (view (execAll instrs s)) (innerBlockF (view s)) := by
  rw [instrs_exec]
  have a1 := block_agree s h _ (fun _ _ => rfl) 0 4 8 12 (by omega) (by omega) (by omega) (by omega)
  have r1 := block_rot s 0 4 8 12 h
  have a2 := block_agree _ r1 _ a1 1 5 9 13 (by omega) (by omega) (by omega) (by omega)
  have r2 := block_rot _ 1 5 9 13 r1
  have a3 := block_agree _ r2 _ a2 2 6 10 14 (by omega) (by omega) (by omega) (by omega)
  have r3 := block_rot _ 2 6 10 14 r2
  obtain ⟨k4, k4r3⟩ := keep_spec _ r3 _ a3 3 7 11 15 (by omega) (by omega) (by omega) (by omega)
  have r4 := keep_rot _ 3 7 11 15 r3
  have a5 := have_spec _ r4 _ 0 5 10 15 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) k4 k4r3
  have r5 := have_rot _ 0 5 10 15 r4
  have a6 := block_agree _ r5 _ a5 1 6 11 12 (by omega) (by omega) (by omega) (by omega)
  have r6 := block_rot _ 1 6 11 12 r5
  have a7 := block_agree _ r6 _ a6 2 7 8 13 (by omega) (by omega) (by omega) (by omega)
  have r7 := block_rot _ 2 7 8 13 r6
  exact block_agree _ r7 _ a7 3 4 9 14 (by omega) (by omega) (by omega) (by omega)

theorem dround_regs (s : State) (r : Reg) (h4 : 4 ≤ r.val) (h14 : r.val ≤ 14) :
    (execAll instrs s).regs r = s.regs r := by
  rw [instrs_exec]
  simp only [block_regs _ _ _ _ _ r h4 h14, keep_regs _ _ _ _ _ r h4 h14,
    have_regs _ _ _ _ _ r h4 h14]

theorem dround_mem_other (s : State) (h : RotRegs s) (y : Armv6M.Word)
    (hy : ∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) :
    (execAll instrs s).mem y = s.mem y := by
  rw [instrs_exec]
  have hsp : ∀ t : State, t.regs 13 = s.regs 13 →
      ∀ n : Nat, n < 64 → y ≠ t.regs 13 + BitVec.ofNat 32 n := by
    intro t ht; rw [ht]; exact hy
  have r1 := block_rot s 0 4 8 12 h
  have r2 := block_rot _ 1 5 9 13 r1
  have r3 := block_rot _ 2 6 10 14 r2
  have r4 := keep_rot _ 3 7 11 15 r3
  have r5 := have_rot _ 0 5 10 15 r4
  have r6 := block_rot _ 1 6 11 12 r5
  have r7 := block_rot _ 2 7 8 13 r6
  have sp_k : ∀ t : State, (execAll (keepBlock 3 7 11 15) t).regs 13 = t.regs 13 :=
    fun t => keep_regs t 3 7 11 15 13 (by decide) (by decide)
  have sp_h : ∀ t : State, (execAll (haveBlock 0 5 10 15) t).regs 13 = t.regs 13 :=
    fun t => have_regs t 0 5 10 15 13 (by decide) (by decide)
  rw [block_mem_other _ r7 3 4 9 14 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp, sp_k, sp_h])),
    block_mem_other _ r6 2 7 8 13 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp, sp_k, sp_h])),
    block_mem_other _ r5 1 6 11 12 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp, sp_k, sp_h])),
    have_mem_other _ r4 0 5 10 15 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp, sp_k])),
    keep_mem_other _ r3 3 7 11 15 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp])),
    block_mem_other _ r2 2 6 10 14 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp])),
    block_mem_other _ r1 1 5 9 13 (by omega) (by omega) (by omega) (by omega) y
      (hsp _ (by simp only [block_sp])),
    block_mem_other _ h 0 4 8 12 (by omega) (by omega) (by omega) (by omega) y hy]

/-! ## Final contract (same statement as version 1) -/

theorem run_eq (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base)
    (hsp : (s.regs 13).toNat % 4 = 0) :
    run code 158 s = .ok (execAll instrs s, execTrace instrs s) := by
  have htn : s.pc.toNat = code.base := by rw [hpc]; decide
  rw [← instrs_length]
  exact run_straight code instrs s (by rw [htn]; exact decodes)
    (alignedAll_of_sp instrs s hsp) (by rw [htn, instrs_length]; decide)

theorem trace_independent (s₁ s₂ : State)
    (h₁ : s₁.pc = BitVec.ofNat 32 code.base) (h₂ : s₂.pc = BitVec.ofNat 32 code.base)
    (hsp : s₁.regs 13 = s₂.regs 13) (ha : (s₁.regs 13).toNat % 4 = 0) :
    (run code 158 s₁).map Prod.snd = (run code 158 s₂).map Prod.snd := by
  rw [run_eq s₁ h₁ ha, run_eq s₂ h₂ (by rw [← hsp]; exact ha)]
  simp only [Except.map, execTrace_congr instrs s₁ s₂ (h₁.trans h₂.symm) hsp]

theorem dround_spec (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base)
    (hsp : (s.regs 13).toNat % 4 = 0) (h : RotRegs s) :
    ∃ s', run code 158 s = .ok (s', execTrace instrs s) ∧
      toArr (view s') = innerBlock (toArr (view s)) ∧
      s'.pc = BitVec.ofNat 32 (code.base + 316) ∧
      (∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) ∧
      (∀ y : Armv6M.Word, (∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) →
        s'.mem y = s.mem y) := by
  refine ⟨execAll instrs s, run_eq s hpc hsp, ?_, ?_, dround_regs s,
    dround_mem_other s h⟩
  · rw [innerBlock_toArr]
    exact toArr_agree _ _ (dround_view s h)
  · rw [execAll_pc, instrs_length, hpc]
    decide

end M0Crypto.Proofs.ChaCha20DRoundV2
