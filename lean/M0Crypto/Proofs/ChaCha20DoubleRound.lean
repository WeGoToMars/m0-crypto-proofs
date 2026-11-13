import M0Crypto.Spec.ChaCha20
import M0Crypto.Proofs.ChaCha20Common
import M0Crypto.Artifacts.ChaCha20DoubleRound

/-!
Refinement proof for the linked bytes of `m0c_chacha20_dround_frag`
(fixtures/chacha20_dround.S, extracted into `M0Crypto.Artifacts.ChaCha20DoubleRound`).


Structure:
1. `core_spec`: the 12 register-only quarter-round instructions (reusable by later
   schedules).
2. `loads_spec` / `stores_spec`: move four stack words to or from r0-r3.
3. `block_spec`: one quarter-round block = loads ++ core ++ stores, for any offsets.
4. Composition of the 8 blocks, the bridge to the RFC `Array` spec, and the final
   contract `dround_spec`.
-/

namespace M0Crypto.Proofs.ChaCha20DoubleRound

open M0Crypto.Armv6M
open M0Crypto.Spec.ChaCha20 (quarterRound qround innerBlock)
open M0Crypto.Proofs

/-! ## Instruction lists -/

/-- Register-only quarter round on r0-r3, rotation counts in r4-r7. -/
def core : List Instr :=
  [ .addsReg 0 0 1, .eorsReg 3 0, .rorsReg 3 4,
    .addsReg 2 2 3, .eorsReg 1 2, .rorsReg 1 5,
    .addsReg 0 0 1, .eorsReg 3 0, .rorsReg 3 6,
    .addsReg 2 2 3, .eorsReg 1 2, .rorsReg 1 7 ]

def loads (a b c d : Nat) : List Instr :=
  [ .ldrSp 0 (BitVec.ofNat 8 a), .ldrSp 1 (BitVec.ofNat 8 b),
    .ldrSp 2 (BitVec.ofNat 8 c), .ldrSp 3 (BitVec.ofNat 8 d) ]

def stores (a b c d : Nat) : List Instr :=
  [ .strSp 0 (BitVec.ofNat 8 a), .strSp 1 (BitVec.ofNat 8 b),
    .strSp 2 (BitVec.ofNat 8 c), .strSp 3 (BitVec.ofNat 8 d) ]

/-- One quarter round on stack words `a, b, c, d`. -/
def block (a b c d : Nat) : List Instr := loads a b c d ++ core ++ stores a b c d

/-- The instruction sequence the bytes must decode to. Checked by `decodes`, not trusted. -/
def instrs : List Instr :=
  block 0 4 8 12 ++ block 1 5 9 13 ++ block 2 6 10 14 ++ block 3 7 11 15 ++
  block 0 5 10 15 ++ block 1 6 11 12 ++ block 2 7 8 13 ++ block 3 4 9 14

/-- The linked code region of the fragment. -/
def code : Code := ⟨Artifacts.ChaCha20DoubleRound.base, Artifacts.ChaCha20DoubleRound.bytes⟩

set_option maxRecDepth 20000 in
theorem instrs_length : instrs.length = 160 := by decide

set_option maxRecDepth 20000 in
theorem code_length : code.bytes.length = 320 := by decide

set_option maxRecDepth 20000 in
/-- The extracted bytes decode exactly to `instrs` from the link address. -/
theorem decodes : decodesAt code code.base instrs = true := by decide

/-! ## Register quarter-round core -/

/-- r4-r7 hold the rotation counts for left rotations by 16, 12, 8, 7. -/
structure RotRegs (s : State) : Prop where
  r4 : s.regs 4 = 16#32
  r5 : s.regs 5 = 20#32
  r6 : s.regs 6 = 24#32
  r7 : s.regs 7 = 25#32

theorem core_spec (s : State) (h : RotRegs s) :
    let s' := execAll core s
    (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
      quarterRound (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) := by
  obtain ⟨h4, h5, h6, h7⟩ := h
  simp only [execAll, core, exec, State.setReg, State.setNZ, State.reg, State.pc,
    toReg_0, toReg_1, toReg_2, toReg_3, toReg_4, toReg_5, toReg_6, toReg_7, quarterRound]
  simp (config := { decide := true }) only [addWithCarry_fst, Fin.isValue,
    ite_true, ite_false, h4, h5, h6, h7, BitVec.toNat_ofNat]
  simp (config := { decide := true }) only [rorC_eq_rotl]

theorem core_frame (s : State) :
    let s' := execAll core s
    s'.mem = s.mem ∧ (∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) := by
  refine ⟨execAll_mem core s (by decide), fun r h4 h14 => ?_⟩
  apply execAll_regs_other core s r (by omega)
  intro i hi
  have : i.dst ≤ 3 := by revert i; decide
  omega

/-! ## Stack view, loads and stores -/

/-- Word `k` of the 16-word frame at SP. -/
def view (s : State) (k : Nat) : Armv6M.Word := read32 s.mem (slot (s.regs 13) k)

theorem spAddr_slot (s : State) (a : Nat) (ha : a < 16) :
    spAddr s (BitVec.ofNat 8 a) = slot (s.regs 13) a := by
  simp only [spAddr, slot, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem loads_frame (s : State) (a b c d : Nat) :
    let s' := execAll (loads a b c d) s
    s'.mem = s.mem ∧ (∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) := by
  refine ⟨execAll_mem _ s (by simp [loads, Instr.isStore]), fun r h4 h14 => ?_⟩
  apply execAll_regs_other _ s r (by omega)
  simp only [loads, List.mem_cons, List.not_mem_nil, or_false]
  rintro i (rfl | rfl | rfl | rfl) <;> simp [Instr.dst] <;> omega

theorem loads_spec (s : State) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    let s' := execAll (loads a b c d) s
    s'.regs 0 = view s a ∧ s'.regs 1 = view s b ∧ s'.regs 2 = view s c ∧ s'.regs 3 = view s d := by
  simp only [execAll, loads, exec, State.setReg, State.pc, toReg_0, toReg_1, toReg_2, toReg_3]
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false]
  simp only [spAddr_slot _ _ ha, spAddr_slot _ _ hb, spAddr_slot _ _ hc, spAddr_slot _ _ hd]
  simp (config := { decide := true }) only [Fin.isValue, ite_false, view, and_self]

theorem stores_frame (s : State) (a b c d : Nat) :
    let s' := execAll (stores a b c d) s
    ∀ r : Reg, r.val ≠ 15 → s'.regs r = s.regs r := by
  intro s' r h15
  apply execAll_regs_other _ s r h15
  simp only [stores, List.mem_cons, List.not_mem_nil, or_false]
  rintro i (rfl | rfl | rfl | rfl) <;> simp [Instr.dst] <;> omega

theorem stores_spec (s : State) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    (execAll (stores a b c d) s).mem =
      write32 (write32 (write32 (write32 s.mem (slot (s.regs 13) a) (s.regs 0))
        (slot (s.regs 13) b) (s.regs 1)) (slot (s.regs 13) c) (s.regs 2))
        (slot (s.regs 13) d) (s.regs 3) := by
  simp only [execAll, stores, exec, State.setReg, State.pc, State.reg,
    toReg_0, toReg_1, toReg_2, toReg_3]
  simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false]
  simp only [spAddr_slot _ _ ha, spAddr_slot _ _ hb, spAddr_slot _ _ hc, spAddr_slot _ _ hd]
  simp (config := { decide := true }) only [Fin.isValue, ite_false]

/-! ## One quarter-round block on the stack -/

/-- Functional update. -/
def upd (f : Nat → Armv6M.Word) (i : Nat) (v : Armv6M.Word) : Nat → Armv6M.Word :=
  fun j => if i = j then v else f j

/-- `QUARTERROUND(a, b, c, d)` on a word function, writing back in the order a, b, c, d
(the same order as RFC 8439 / the spec's `qround`). -/
def qroundF (f : Nat → Armv6M.Word) (a b c d : Nat) : Nat → Armv6M.Word :=
  let q := quarterRound (f a) (f b) (f c) (f d)
  upd (upd (upd (upd f a q.1) b q.2.1) c q.2.2.1) d q.2.2.2

theorem block_regs (s : State) (a b c d : Nat) (r : Reg) (h4 : 4 ≤ r.val) (h14 : r.val ≤ 14) :
    (execAll (block a b c d) s).regs r = s.regs r := by
  simp only [block, execAll_append]
  rw [stores_frame _ a b c d r (by omega), (core_frame _).2 r h4 h14,
    (loads_frame s a b c d).2 r h4 h14]

theorem block_rot (s : State) (a b c d : Nat) (h : RotRegs s) :
    RotRegs (execAll (block a b c d) s) :=
  ⟨by rw [block_regs s a b c d 4 (by decide) (by decide)]; exact h.r4,
   by rw [block_regs s a b c d 5 (by decide) (by decide)]; exact h.r5,
   by rw [block_regs s a b c d 6 (by decide) (by decide)]; exact h.r6,
   by rw [block_regs s a b c d 7 (by decide) (by decide)]; exact h.r7⟩

theorem block_sp (s : State) (a b c d : Nat) :
    (execAll (block a b c d) s).regs 13 = s.regs 13 :=
  block_regs s a b c d 13 (by decide) (by decide)

/-- Memory after one block, as four word writes into the frame. -/
theorem block_mem (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    (execAll (block a b c d) s).mem =
      let q := quarterRound (view s a) (view s b) (view s c) (view s d)
      write32 (write32 (write32 (write32 s.mem (slot (s.regs 13) a) q.1)
        (slot (s.regs 13) b) q.2.1) (slot (s.regs 13) c) q.2.2.1)
        (slot (s.regs 13) d) q.2.2.2 := by
  obtain ⟨l0, l1, l2, l3⟩ := loads_spec s a b c d ha hb hc hd
  obtain ⟨m1, r1⟩ := loads_frame s a b c d
  have hrot1 : RotRegs (execAll (loads a b c d) s) :=
    ⟨by rw [r1 4 (by decide) (by decide)]; exact h.r4,
     by rw [r1 5 (by decide) (by decide)]; exact h.r5,
     by rw [r1 6 (by decide) (by decide)]; exact h.r6,
     by rw [r1 7 (by decide) (by decide)]; exact h.r7⟩
  have hq := core_spec _ hrot1
  obtain ⟨m2, r2⟩ := core_frame (execAll (loads a b c d) s)
  simp only [block, execAll_append]
  rw [stores_spec _ a b c d ha hb hc hd, r2 13 (by decide) (by decide),
    r1 13 (by decide) (by decide), m2, m1]
  rw [l0, l1, l2, l3] at hq
  simp only [← hq]

theorem block_spec (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (k : Nat) (hk : k < 16) :
    view (execAll (block a b c d) s) k = qroundF (view s) a b c d k := by
  conv => lhs; unfold view
  rw [block_sp, block_mem s h a b c d ha hb hc hd]
  simp only [read32_write32_slot _ _ _ _ _ hd hk, read32_write32_slot _ _ _ _ _ hc hk,
    read32_write32_slot _ _ _ _ _ hb hk, read32_write32_slot _ _ _ _ _ ha hk]
  rfl

/-- One block changes no byte outside the 64-byte frame at SP. -/
theorem block_mem_other (s : State) (h : RotRegs s) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (y : Armv6M.Word)
    (hy : ∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) :
    (execAll (block a b c d) s).mem y = s.mem y := by
  have hw : ∀ (m : Mem) (i : Nat) (v : Armv6M.Word), i < 16 →
      write32 m (slot (s.regs 13) i) v y = m y := by
    intro m i v hi
    apply write32_other
    intro k hk
    have := hy (4 * i + k) (by omega)
    rwa [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [block_mem s h a b c d ha hb hc hd]
  simp only [hw _ _ _ hd, hw _ _ _ hc, hw _ _ _ hb, hw _ _ _ ha]

/-! ## Composition of the double round -/

/-- `f` and `g` agree on the 16 state indices. -/
def Agree (f g : Nat → Armv6M.Word) : Prop := ∀ k, k < 16 → f k = g k

theorem qroundF_agree (f g : Nat → Armv6M.Word) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (h : Agree f g) :
    Agree (qroundF f a b c d) (qroundF g a b c d) := by
  intro k hk
  simp only [qroundF, upd, h a ha, h b hb, h c hc, h d hd, h k hk]

theorem block_agree (s : State) (hs : RotRegs s) (f : Nat → Armv6M.Word) (hf : Agree (view s) f)
    (a b c d : Nat) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    Agree (view (execAll (block a b c d) s)) (qroundF f a b c d) := by
  intro k hk
  rw [block_spec s hs a b c d ha hb hc hd k hk]
  exact qroundF_agree _ _ a b c d ha hb hc hd hf k hk

/-- RFC 8439 `inner_block` on a word function. -/
def innerBlockF (f : Nat → Armv6M.Word) : Nat → Armv6M.Word :=
  let f := qroundF f 0 4  8 12
  let f := qroundF f 1 5  9 13
  let f := qroundF f 2 6 10 14
  let f := qroundF f 3 7 11 15
  let f := qroundF f 0 5 10 15
  let f := qroundF f 1 6 11 12
  let f := qroundF f 2 7  8 13
  let f := qroundF f 3 4  9 14
  f

theorem instrs_exec (s : State) :
    execAll instrs s =
      execAll (block 3 4 9 14) (execAll (block 2 7 8 13) (execAll (block 1 6 11 12)
        (execAll (block 0 5 10 15) (execAll (block 3 7 11 15) (execAll (block 2 6 10 14)
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
  have a4 := block_agree _ r3 _ a3 3 7 11 15 (by omega) (by omega) (by omega) (by omega)
  have r4 := block_rot _ 3 7 11 15 r3
  have a5 := block_agree _ r4 _ a4 0 5 10 15 (by omega) (by omega) (by omega) (by omega)
  have r5 := block_rot _ 0 5 10 15 r4
  have a6 := block_agree _ r5 _ a5 1 6 11 12 (by omega) (by omega) (by omega) (by omega)
  have r6 := block_rot _ 1 6 11 12 r5
  have a7 := block_agree _ r6 _ a6 2 7 8 13 (by omega) (by omega) (by omega) (by omega)
  have r7 := block_rot _ 2 7 8 13 r6
  exact block_agree _ r7 _ a7 3 4 9 14 (by omega) (by omega) (by omega) (by omega)

theorem dround_regs (s : State) (r : Reg) (h4 : 4 ≤ r.val) (h14 : r.val ≤ 14) :
    (execAll instrs s).regs r = s.regs r := by
  rw [instrs_exec]
  simp only [block_regs _ _ _ _ _ r h4 h14]

theorem dround_mem_other (s : State) (h : RotRegs s) (y : Armv6M.Word)
    (hy : ∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) :
    (execAll instrs s).mem y = s.mem y := by
  rw [instrs_exec]
  -- Each block preserves RotRegs and SP, so `hy` transfers to every intermediate state.
  have step : ∀ (t : State) (a b c d : Nat), RotRegs t → t.regs 13 = s.regs 13 →
      a < 16 → b < 16 → c < 16 → d < 16 →
      (execAll (block a b c d) t).mem y = t.mem y := by
    intro t a b c d ht hsp ha hb hc hd
    exact block_mem_other t ht a b c d ha hb hc hd y (by rw [hsp]; exact hy)
  have r1 := block_rot s 0 4 8 12 h
  have r2 := block_rot _ 1 5 9 13 r1
  have r3 := block_rot _ 2 6 10 14 r2
  have r4 := block_rot _ 3 7 11 15 r3
  have r5 := block_rot _ 0 5 10 15 r4
  have r6 := block_rot _ 1 6 11 12 r5
  have r7 := block_rot _ 2 7 8 13 r6
  rw [step _ 3 4 9 14 r7 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 2 7 8 13 r6 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 1 6 11 12 r5 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 0 5 10 15 r4 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 3 7 11 15 r3 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 2 6 10 14 r2 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 1 5 9 13 r1 (by simp only [block_sp]) (by omega) (by omega) (by omega) (by omega),
    step _ 0 4 8 12 h rfl (by omega) (by omega) (by omega) (by omega)]

/-! ## Bridge to the RFC `Array` specification -/

/-- The 16 state words as the spec's `Array`. -/
def toArr (f : Nat → Armv6M.Word) : Array Armv6M.Word := Array.ofFn (n := 16) fun i => f i.val

theorem toArr_getElem! (f : Nat → Armv6M.Word) (k : Nat) (hk : k < 16) :
    (toArr f)[k]! = f k := by
  simp [toArr, hk]

theorem toArr_set! (f : Nat → Armv6M.Word) (k : Nat) (v : Armv6M.Word) :
    (toArr f).set! k v = toArr (upd f k v) := by
  unfold toArr upd
  apply Array.ext
  · simp
  · intro i _ h2
    simp only [Array.size_ofFn] at h2
    simp only [Array.set!, Array.getElem_ofFn]
    split <;> simp_all

theorem toArr_agree (f g : Nat → Armv6M.Word) (h : Agree f g) : toArr f = toArr g := by
  simp only [toArr]
  congr 1
  funext i
  exact h i.val i.isLt

theorem qround_toArr (f : Nat → Armv6M.Word) (a b c d : Nat)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    qround (toArr f) a b c d = toArr (qroundF f a b c d) := by
  simp only [qround, toArr_getElem! f _ ha, toArr_getElem! f _ hb, toArr_getElem! f _ hc,
    toArr_getElem! f _ hd, toArr_set!]
  rfl

theorem innerBlock_toArr (f : Nat → Armv6M.Word) :
    innerBlock (toArr f) = toArr (innerBlockF f) := by
  simp only [innerBlock, innerBlockF]
  repeat rw [qround_toArr _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

/-! ## Final contract -/

theorem run_eq (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base)
    (hsp : (s.regs 13).toNat % 4 = 0) :
    run code 160 s = .ok (execAll instrs s, execTrace instrs s) := by
  have htn : s.pc.toNat = code.base := by rw [hpc]; decide
  rw [← instrs_length]
  exact run_straight code instrs s (by rw [htn]; exact decodes)
    (alignedAll_of_sp instrs s hsp) (by rw [htn, instrs_length]; decide)

/-- Constant-time property at the trace level: from the link address with the same SP,
any two starting states execute the same instructions at the same addresses with the
same data-access addresses, regardless of the state words, other registers or flags. -/
theorem trace_independent (s₁ s₂ : State)
    (h₁ : s₁.pc = BitVec.ofNat 32 code.base) (h₂ : s₂.pc = BitVec.ofNat 32 code.base)
    (hsp : s₁.regs 13 = s₂.regs 13) (ha : (s₁.regs 13).toNat % 4 = 0) :
    (run code 160 s₁).map Prod.snd = (run code 160 s₂).map Prod.snd := by
  rw [run_eq s₁ h₁ ha, run_eq s₂ h₂ (by rw [← hsp]; exact ha)]
  simp only [Except.map, execTrace_congr instrs s₁ s₂ (h₁.trans h₂.symm) hsp]

/-- Combined contract for the linked fragment. Started at its link address with SP
word-aligned and r4-r7 = 16/20/24/25, the bytes execute 160 instructions without
fault and leave RFC 8439 `innerBlock` of the 16 stack words in place, PC at the end
of the fragment, r4-r14 unchanged, and every byte outside `[SP, SP+64)` unchanged
(modulo 2^32). -/
theorem dround_spec (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base)
    (hsp : (s.regs 13).toNat % 4 = 0) (h : RotRegs s) :
    ∃ s', run code 160 s = .ok (s', execTrace instrs s) ∧
      toArr (view s') = innerBlock (toArr (view s)) ∧
      s'.pc = BitVec.ofNat 32 (code.base + 320) ∧
      (∀ r : Reg, 4 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) ∧
      (∀ y : Armv6M.Word, (∀ n : Nat, n < 64 → y ≠ s.regs 13 + BitVec.ofNat 32 n) →
        s'.mem y = s.mem y) := by
  refine ⟨execAll instrs s, run_eq s hpc hsp, ?_, ?_, dround_regs s,
    dround_mem_other s h⟩
  · rw [innerBlock_toArr]
    exact toArr_agree _ _ (dround_view s h)
  · rw [execAll_pc, instrs_length, hpc]
    decide

end M0Crypto.Proofs.ChaCha20DoubleRound
