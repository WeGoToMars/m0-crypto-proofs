import M0Crypto.Release.Ed25519CallProgRun
import M0Crypto.Release.Ed25519Contract

set_option linter.unusedSimpArgs false

/-!
# Call programs: the entries' ABI frame

`abi_enter` and `abi_leave` of `gen_ed25519.py`: save `r4`-`r11` and `lr` (36 bytes), move `sp`
down by the frame in steps of at most 508, and at the end zero the frame and the deepest
callee's window with an `stm` loop, move `sp` back, clear `r1`-`r3` and `r12`, and restore.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

/-! ## Code -/

/-- Steps of at most 508 bytes adding up to `n` (fuel `f`), as `prologue`/`abi_leave` emit. -/
def chunks : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else min n 508 :: chunks f (n - min n 508)

def subSps (n : Nat) : List Instr := (chunks n n).map fun k => .subSp (BitVec.ofNat 7 (k / 4))
def addSps (n : Nat) : List Instr := (chunks n n).map fun k => .addSp (BitVec.ofNat 7 (k / 4))

/-- `push {r4-r7, lr}; mov r4, r8; …; mov r7, r11; push {r4-r7}`. -/
def saveHi : List Instr :=
  [.push 0xf0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11, .push 0xf0 false]

def abiEnter (fs : Nat) : List Instr := saveHi ++ subSps fs

/-- `mov r12, r0; movs r1, #0; movs r2, #0; add r0, sp, #0; movs r3, #K`. -/
def wipeSet (K : Nat) : List Instr :=
  [.movHi 12 0, .movImm 1 0, .movImm 2 0, .addRdSp 0 0, .movImm 3 (BitVec.ofNat 8 K)]

/-- `movs r1, #0; mov r12, r1; pop {r4-r7}; mov r8, r4; …; mov r11, r7`. -/
def restoreHi : List Instr :=
  [.movImm 1 0, .movHi 12 1, .pop 0xf0 false, .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7]

/-- Before the wipe loop: `sp` down by the callee window `w`, `r12 = r0`, `r1 = r2 = 0`,
`r0 = sp`, `r3` the pair count. -/
def wipeHead (fs w : Nat) : List Instr := subSps w ++ wipeSet ((fs + w) / 8)

/-- One pass: `stm r0!, {r1, r2}; subs r3, #1` (then `bne`). -/
def wipeBody : List Instr := [.stm 0 0x06, .subImm8 3 1]

/-- After the loop: `r0` back, `sp` up, `r1 = r12 = 0`, `pop {r4-r7}; mov r8, r4; …`. -/
def leaveTail (fs w : Nat) : List Instr := [.movHi 0 12] ++ addSps w ++ addSps fs ++ restoreHi

/-- `abi_leave` with a wipe, at `o`: the head, the loop, the tail and `pop {r4-r7, pc}`. -/
def abiLeave (fs w o : Nat) : List Piece :=
  let ob := o + seqSize (wipeHead fs w)
  [.seq (wipeHead fs w), .seq wipeBody, .bcond 1 ob, .seq (leaveTail fs w), .seq [.pop 0xf0 true]]

/-! ## `sp` steps -/

theorem chunks_le : ∀ f n, ∀ k ∈ chunks f n, k ≤ 508 ∧ 0 < k
  | 0, _ => by simp [chunks]
  | f + 1, n => by
    unfold chunks; split
    · simp
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · exact chunks_le f _ k hk

theorem chunks_sum : ∀ f n, n ≤ 508 * f → (chunks f n).sum = n
  | 0, n, h => by simp [chunks]; omega
  | f + 1, n, h => by
    unfold chunks; split
    · simp; omega
    · simp only [List.sum_cons]; rw [chunks_sum f _ (by omega)]; omega

theorem chunks_four : ∀ f n, n % 4 = 0 → ∀ k ∈ chunks f n, k % 4 = 0
  | 0, _, _ => by simp [chunks]
  | f + 1, n, h => by
    unfold chunks; split
    · simp
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · exact chunks_four f _ (by omega) k hk


/-- One `sp` step of `k` bytes, up or down. -/
def spI (up : Bool) (k : Nat) : Instr :=
  if up then .addSp (BitVec.ofNat 7 (k / 4)) else .subSp (BitVec.ofNat 7 (k / 4))

theorem subSps_eq (n : Nat) : subSps n = (chunks n n).map (spI false) := rfl
theorem addSps_eq (n : Nat) : addSps n = (chunks n n).map (spI true) := rfl

section sp
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base sp0 : Word} {N : Nat}
variable {Pc Rd Wr : Word → Prop}

theorem spI_facts (up : Bool) {k : Nat} (hk : k ≤ 508) (h4 : k % 4 = 0) (t : State) :
    (spI up k).falls = true ∧ (spI up k).accesses t = [] ∧ (spI up k).size = 2 ∧
    ((spI up k).next t).pc = t.pc + 2#32 ∧ ((spI up k).next t).mem = t.mem ∧
    (∀ r : Reg, r ≠ 13 → r ≠ 15 → ((spI up k).next t).regs r = t.regs r) ∧
    ((spI up k).next t).regs 13 =
      (if up then t.regs 13 + BitVec.ofNat 32 k else t.regs 13 - BitVec.ofNat 32 k) := by
  have e : (BitVec.ofNat 7 (k / 4)).toNat * 4 = k := by simp; omega
  cases up
  · refine ⟨rfl, rfl, rfl, subSp_pc _ _, subSp_mem _ _, fun r h1 h2 => subSp_regs _ _ r h1 h2, ?_⟩
    simp only [spI, Bool.false_eq_true, ↓reduceIte]; rw [subSp_sp, e]
  · refine ⟨rfl, rfl, rfl, addSp_pc _ _, addSp_mem _ _, fun r h1 h2 => addSp_regs _ _ r h1 h2, ?_⟩
    simp only [spI, ↓reduceIte]; rw [addSp_sp, e]

/-- The trace of `sp` steps at `o`: no accesses. -/
def spTr (base : Word) (up : Bool) : Nat → List Nat → List Event
  | _, [] => []
  | o, k :: ks => ⟨base + BitVec.ofNat 32 o, spI up k, []⟩ :: spTr base up (o + 2) ks

/-- **`sp` steps**: `sub sp` steps from depth `d` down, or `add sp` steps up, inside the window. -/
theorem sps_run (hb : base.toNat % 2 = 0) (up : Bool) {Q : State → Prop} {Ψ : TrP} :
    ∀ (ks : List Nat) (o d : Nat) (t : State), (∀ k ∈ ks, k ≤ 508 ∧ k % 4 = 0) →
    t.pc = base + BitVec.ofNat 32 o → o % 2 = 0 → seqAt B o (ks.map (spI up)) = true →
    InRegion Pc base o (2 * ks.length) → t.regs 13 = sp0 - BitVec.ofNat 32 d → d ≤ N →
    (if up then ks.sum ≤ d else d + ks.sum ≤ N) →
    (∀ u, u.pc = base + BitVec.ofNat 32 (o + 2 * ks.length) →
      u.regs 13 = sp0 - BitVec.ofNat 32 (if up then d - ks.sum else d + ks.sum) →
      (∀ r : Reg, r ≠ 13 → r ≠ 15 → u.regs r = t.regs r) → u.mem = t.mem →
      ReachFT base Pc Rd Wr (InStackWindow sp0 N) u Q Ψ) →
    ReachFT base Pc Rd Wr (InStackWindow sp0 N) t Q (Tr.cat (Tr.is (spTr base up o ks)) Ψ)
  | [], o, d, t, _, hpc, _, _, _, h13, _, _, k => by
    exact ReachT.mono (k t (by simpa using hpc) (by simpa using h13) (fun _ _ _ => rfl) rfl) (fun _ _ h => h)
      (fun _ h => h) fun tr h => ⟨[], tr, rfl, rfl, h⟩
  | x :: ks, o, d, t, hks, hpc, ho, hseq, hr, h13, hd, hs, k => by
    obtain ⟨hx5, hx4⟩ := hks x List.mem_cons_self
    obtain ⟨hf, hacc, hsz, hpc1, hm1, hr1, h131⟩ := spI_facts up hx5 hx4 t
    simp only [List.map_cons, seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hseq
    have hd' : (if up then d - x else d + x) ≤ N := by cases up <;> simp at hs ⊢ <;> omega
    have h13' : ((spI up x).next t).regs 13 = sp0 - BitVec.ofNat 32 (if up then d - x else d + x) := by
      rw [h131, h13]
      cases up
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      · simp only [↓reduceIte] at hs ⊢; simp only [List.sum_cons] at hs
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
    refine ReachT.mono (ReachFT.step hb (spI up x) hpc ho hseq.1.1 hseq.1.2 (by rw [hacc]; rfl)
      (exec_ok_of_falls hf t) (by simpa using hr 0 (by simp only [List.length_cons]; omega)) (fun y hy => by rw [hacc] at hy; exact absurd hy (writes_nil y))
      (fun y hy => by rw [hacc] at hy; exact absurd hy (reads_nil y)) ⟨d, hd, h13⟩ (by rw [hpc, hacc])
      (sps_run hb up ks (o + 2) _ _ (fun k hk => hks k (List.mem_cons_of_mem _ hk))
        (by rw [hpc1]; exact pc_add hpc) (by omega) (by rw [← hsz]; exact hseq.2)
        (fun j hj => by
          have := hr (j + 2) (by simp only [List.length_cons] at *; omega)
          rwa [show o + (j + 2) = o + 2 + j by omega] at this) h13' hd'
        (by cases up <;> simp at hs ⊢ <;> omega) fun u hpu hu13 hur hum => k u
          (by rw [hpu]; congr 2; simp; omega)
          (by rw [hu13]; congr 2; cases up <;> simp <;> omega)
          (fun r h1 h2 => by rw [hur r h1 h2, hr1 r h1 h2]) (by rw [hum, hm1])))
      (fun _ _ h => h) (fun _ h => h) fun _ h => Tr.cat_is_cons h

end sp


theorem seqSize_sps (up : Bool) : ∀ ks : List Nat, seqSize (ks.map (spI up)) = 2 * ks.length
  | [] => rfl
  | k :: ks => by
    have ih := seqSize_sps up ks
    have h2 : (spI up k).size = 2 := by cases up <;> rfl
    simp only [seqSize, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih, h2]; omega

/-! ## Saving the registers -/

theorem lr_f0 : listRegs 240#8 = [4, 5, 6, 7] := by decide

theorem save_trOk : traceOk saveHi [13] = true := by decide

theorem save_facts (s : State) :
    (execAll saveHi s).regs 13 = s.regs 13 - 36#32 ∧ (execAll saveHi s).pc = s.pc + 12#32 ∧
    (∀ r : Reg, r.val < 4 ∨ (8 ≤ r.val ∧ r.val < 13) ∨ r.val = 14 → (execAll saveHi s).regs r = s.regs r) ∧
    (execAll saveHi s).mem = storeWords (storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 13 - 36#32)
      [s.regs 8, s.regs 9, s.regs 10, s.regs 11] := by
  simp [saveHi, execAll, Instr.next, Instr.exec, lr_f0, State.setReg, State.sp, State.pc, State.reg, Instr.size]
  refine ⟨by bv_omega, by bv_omega, fun r hr => ?_, by congr 1; bv_omega⟩
  have h : r ≠ 13 ∧ r ≠ 15 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
  simp [h]

section save
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base sp0 : Word} {N : Nat}
variable {Pc Rd Wr : Word → Prop}

theorem save_ok {o : Nat} (s : State) (hpc : s.pc = base + BitVec.ofNat 32 o) (hr : InRegion Pc base o 12)
    (h13 : s.regs 13 = sp0) (hN : 36 ≤ N) (hW : ∀ j < 36, Wr (sp0 - 36#32 + BitVec.ofNat 32 j)) :
    BlockOk (Step Pc Rd Wr (InStackWindow sp0 N)) saveHi s := by
  simp [BlockOk, saveHi, Step, Instr.next, Instr.exec, lr_f0, State.setReg, State.sp, State.pc, State.reg,
    Instr.size, Instr.accesses, h13, BitVec.add_assoc, writes_nil, reads_nil, words_no_reads]
  have pc : ∀ j < 12, Pc (s.regs 15 + BitVec.ofNat 32 j) := fun j hj => by
    have hp : s.regs 15 = base + BitVec.ofNat 32 o := hpc
    rw [hp, ofNat_add_assoc]; exact hr j hj
  have w : ∀ a k n, k + 4 * n ≤ 36 → a = sp0 - 36#32 + BitVec.ofNat 32 k →
      ∀ y, Writes (wordAccesses Kind.write a n) y → Wr y := by
    intro a k n hk ha y hy
    obtain ⟨o', ho', rfl⟩ := words_writes hy
    rw [ha, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hW _ (by omega)
  have sw : ∀ d ≤ 36, InStackWindow sp0 N (sp0 - BitVec.ofNat 32 d) := fun d hd => ⟨d, by omega, rfl⟩
  refine ⟨⟨by simpa using pc 0 (by omega), w _ 16 5 (by omega) (by bv_omega), by simpa using sw 0 (by omega)⟩,
    ⟨by simpa using pc 2 (by omega), sw 20 (by omega)⟩, ⟨by simpa using pc 4 (by omega), sw 20 (by omega)⟩,
    ⟨by simpa using pc 6 (by omega), sw 20 (by omega)⟩, ⟨by simpa using pc 8 (by omega), sw 20 (by omega)⟩,
    by simpa using pc 10 (by omega), w _ 0 4 (by omega) (by bv_omega), sw 20 (by omega)⟩

/-- **`abi_enter`**: the 36 saved bytes, then `sp` down by the frame `fs`. -/
theorem enter_run (hb : base.toNat % 2 = 0) {fs o : Nat} {s : State} {Q : State → Prop} {Ψ : TrP}
    (hpc : s.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0) (hseq : seqAt B o (abiEnter fs) = true)
    (hr : InRegion Pc base o (seqSize (abiEnter fs))) (h13 : s.regs 13 = sp0) (h4 : sp0.toNat % 4 = 0)
    (hfs : fs % 4 = 0) (hN : 36 + fs ≤ N)
    (hW : ∀ j < 36, Wr (sp0 - 36#32 + BitVec.ofNat 32 j))
    (k : ∀ t, t.pc = base + BitVec.ofNat 32 (o + seqSize (abiEnter fs)) →
      t.regs 13 = sp0 - BitVec.ofNat 32 (36 + fs) →
      (∀ r : Reg, r.val < 4 ∨ (8 ≤ r.val ∧ r.val < 13) ∨ r.val = 14 → t.regs r = s.regs r) →
      t.mem = storeWords (storeWords s.mem (sp0 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14])
        (sp0 - 36#32) [s.regs 8, s.regs 9, s.regs 10, s.regs 11] →
      ReachFT base Pc Rd Wr (InStackWindow sp0 N) t Q Ψ) :
    ReachFT base Pc Rd Wr (InStackWindow sp0 N) s Q
      (Tr.cat (Tr.is (blockTr saveHi (base + BitVec.ofNat 32 o) [13] [sp0]))
        (Tr.cat (Tr.is (spTr base false (o + 12) (chunks fs fs))) Ψ)) := by
  have hT := traceAll_blockTr (L := [13]) (by decide) save_trOk hpc (vs := [s.regs 13]) rfl
  rw [h13] at hT; rw [← hT]
  rw [abiEnter, seqAt_append, Bool.and_eq_true] at hseq
  have hsz : seqSize (abiEnter fs) = 12 + 2 * (chunks fs fs).length := by
    rw [abiEnter, seqSize_append, subSps_eq, seqSize_sps]; rfl
  rw [hsz] at hr k
  obtain ⟨f13, fpc, fregs, fmem⟩ := save_facts s
  refine ReachT.block hb saveHi o s hpc ho hseq.1 rfl ?_ (save_ok s hpc (fun j hj => hr j (by omega)) h13
    (by omega) hW) ?_
  · simp [alignedAll, saveHi, Instr.next, Instr.exec, lr_f0, State.setReg, State.sp, Instr.accesses, h13]
    exact ⟨List.all_eq_true.mp (words_aligned _ _ _ (by bv_omega)),
      List.all_eq_true.mp (words_aligned _ _ _ (by bv_omega))⟩
  refine sps_run hb false (chunks fs fs) (o + 12) 36 _ (fun x hx => ⟨(chunks_le fs fs x hx).1,
      chunks_four fs fs hfs x hx⟩) (by rw [fpc, hpc, ofNat_add_assoc]) (by omega) hseq.2
    (fun j hj => by have := hr (12 + j) (by omega); rwa [← Nat.add_assoc] at this)
    (by rw [f13, h13]) (by omega) (by simp only [Bool.false_eq_true, ↓reduceIte]; rw [chunks_sum fs fs (by omega)]; omega)
    fun u hpu hu13 hur hum => k u (by rw [hpu]; congr 2; omega)
      (by rw [hu13, chunks_sum fs fs (by omega)]; rfl)
      (fun r hr' => by
        rw [hur r (fun h => by subst h; revert hr'; decide) (fun h => by subst h; revert hr'; decide)]
        exact fregs r hr')
      (by rw [hum, fmem, h13])

end save


/-! ## The wipe loop -/

theorem sw_append (m : Mem) (a : Word) (xs ys : List Word) :
    storeWords m a (xs ++ ys) = storeWords (storeWords m a xs) (a + BitVec.ofNat 32 (4 * xs.length)) ys := by
  induction xs generalizing m a with
  | nil => simp [storeWords]
  | cons x xs ih =>
    simp only [List.cons_append, storeWords, ih, List.length_cons]
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc,
      show 4 * (xs.length + 1) = 4 + 4 * xs.length by omega]

theorem lr_06 : listRegs 6#8 = [1, 2] := by decide

theorem wipe_facts (t : State) :
    (execAll wipeBody t).pc = t.pc + 4#32 ∧ (execAll wipeBody t).regs 0 = t.regs 0 + 8#32 ∧
    (execAll wipeBody t).regs 3 = t.regs 3 - 1#32 ∧
    (∀ r : Reg, r ≠ 0 → r ≠ 3 → r ≠ 15 → (execAll wipeBody t).regs r = t.regs r) ∧
    (execAll wipeBody t).mem = storeWords t.mem (t.regs 0) [t.regs 1, t.regs 2] ∧
    (execAll wipeBody t).z = (t.regs 3 - 1#32 == 0#32) := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  have e1 : LowReg.toReg 1 = 1 := rfl
  have e2 : LowReg.toReg 2 = 2 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  have bc : bitCount 6#8 = 2 := by decide
  simp [wipeBody, execAll, Instr.next, Instr.exec, lr_06, State.setReg, State.setNZ, State.reg, State.pc,
    Instr.size, addFlags, State.setNZCV, Routine.addWithCarry_true_fst, e0, e1, e2, e3, bc,
    show ∀ x : Word, x + 4294967294#32 + 1#32 = x - 1#32 from fun x => by bv_omega]
  refine ⟨by bv_omega, fun r h0 h3 h15 => ?_⟩
  simp [h0, h3, h15]


theorem wipe_trOk : traceOk wipeBody [0] = true := by decide

/-- One wipe pass from `r0 = a` and its `bne`. -/
def wipeTr (pb a : Word) (imm : BitVec 8) : TrP :=
  Tr.cat (Tr.is (blockTr wipeBody pb [0] [a])) (Tr.is [⟨pb + 4#32, .bcond 1 imm, []⟩])

theorem cond_same {b : Bool} {Φ : TrP} : ∀ tr, Tr.cond b Φ Φ tr → Φ tr := fun tr h => by
  cases b
  · exact h.2 rfl
  · exact h.1 rfl

section wipe
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}
variable {Pc Rd Wr Sp : Word → Prop}

theorem wipe_ok {ob : Nat} (t : State) (hpc : t.pc = base + BitVec.ofNat 32 ob) (hr : InRegion Pc base ob 4)
    (hW : ∀ j < 8, Wr (t.regs 0 + BitVec.ofNat 32 j)) (hsp : Sp (t.regs 13)) :
    BlockOk (Step Pc Rd Wr Sp) wipeBody t := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  have bc : bitCount 6#8 = 2 := by decide
  simp [BlockOk, wipeBody, Step, Instr.next, Instr.exec, Instr.accesses, lr_06, State.setReg, State.reg, State.pc,
    State.setNZ, addFlags, State.setNZCV, Instr.size, e0, bc, writes_nil, reads_nil, words_no_reads, hsp]
  have hp : t.regs 15 = base + BitVec.ofNat 32 ob := hpc
  refine ⟨⟨by rw [hp]; simpa using hr 0 (by omega), fun y hy => ?_⟩, by
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hr 2 (by omega)⟩
  obtain ⟨o', ho', rfl⟩ := words_writes hy
  exact hW o' (by omega)

/-- **The wipe loop**: `i` passes of `stm r0!, {r1, r2}; subs r3, #1; bne` zero `8 i` bytes from `r0`. -/
theorem wipe_run (hb : base.toNat % 2 = 0) {ob : Nat} {lo : Word} {R : Reg → Word} {m : Mem}
    {Q : State → Prop} {Ψ : TrP} (ho : ob % 2 = 0) (hseq : seqAt B ob wipeBody = true)
    (hbc : seqAt B (ob + 4) [.bcond 1 (brImm8 (ob + 4) ob)] = true)
    (ht : BitVec.ofNat 32 (ob + 4) + 4#32 + (brImm8 (ob + 4) ob ++ 0#1).signExtend 32 = BitVec.ofNat 32 ob)
    (hr : InRegion Pc base ob 6) (h13 : R 13 = lo) (hsp : Sp lo) (h4 : lo.toNat % 4 = 0) (h1 : R 1 = 0)
    (h2 : R 2 = 0) {K : Nat}
    (hK : 8 * K < 2 ^ 32) (hW : ∀ j < 8 * K, Wr (lo + BitVec.ofNat 32 j))
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (ob + 6) → u.regs 0 = lo + BitVec.ofNat 32 (8 * K) →
      u.regs 3 = 0 → (∀ r : Reg, r ≠ 0 → r ≠ 3 → r ≠ 15 → u.regs r = R r) →
      u.mem = storeWords m lo (List.replicate (2 * K) 0) → ReachFT base Pc Rd Wr Sp u Q Ψ) :
    ∀ i j t, i + j = K → 0 < i → t.pc = base + BitVec.ofNat 32 ob → t.regs 0 = lo + BitVec.ofNat 32 (8 * j) →
      t.regs 3 = BitVec.ofNat 32 i → (∀ r : Reg, r ≠ 0 → r ≠ 3 → r ≠ 15 → t.regs r = R r) →
      t.mem = storeWords m lo (List.replicate (2 * j) 0) →
      ReachFT base Pc Rd Wr Sp t Q
        (Tr.rep (fun j => wipeTr (base + BitVec.ofNat 32 ob) (lo + BitVec.ofNat 32 (8 * j)) (brImm8 (ob + 4) ob))
          j i Ψ)
  | 0, _, _, _, hi, _, _, _, _, _ => absurd hi (by omega)
  | i + 1, j, t, hij, _, hpc, h0, h3, hR, hm => by
    obtain ⟨fpc, f0, f3, fR, fm, fz⟩ := wipe_facts t
    have hR13 : t.regs 13 = lo := by rw [hR 13 (by decide) (by decide) (by decide), h13]
    have hrm : t.regs 1 = 0 ∧ t.regs 2 = 0 := ⟨by rw [hR 1 (by decide) (by decide) (by decide), h1],
      by rw [hR 2 (by decide) (by decide) (by decide), h2]⟩
    have hT := traceAll_blockTr (L := [0]) (by decide) wipe_trOk hpc (vs := [t.regs 0]) rfl
    rw [h0] at hT
    have hz : condPassed 1 (execAll wipeBody t) = !(i == 0) := by
      have e : (BitVec.ofNat 32 i == 0#32) = (i == 0) := by
        rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
        constructor
        · intro he; have := congrArg BitVec.toNat he; simp at this; omega
        · rintro rfl; rfl
      simp [condPassed, fz, f3, h3, ofNat_succ_sub i (by omega), e]
    have hpc1 : (execAll wipeBody t).pc = base + BitVec.ofNat 32 (ob + 4) := by
      rw [fpc, hpc, ofNat_add_assoc]
    have hsz : ob + 4 + 2 ≤ BS := by
      have := (CodeBytes.len : B.length = BS)
      simp only [seqAt, Bool.and_eq_true, decide_eq_true_eq] at hbc
      exact this ▸ hbc.1.2
    have h13' : (execAll wipeBody t).regs 13 = lo := by rw [fR 13 (by decide) (by decide) (by decide), hR13]
    have hrest : ∀ r : Reg, r ≠ 0 → r ≠ 3 → r ≠ 15 → (execAll wipeBody t).regs r = R r := fun r a b c => by
      rw [fR r a b c, hR r a b c]
    have hm' : (execAll wipeBody t).mem = storeWords m lo (List.replicate (2 * (j + 1)) 0) := by
      rw [fm, hm, h0, hrm.1, hrm.2, show 2 * (j + 1) = 2 * j + 2 by omega,
        ← List.replicate_append_replicate (n := 2 * j) (m := 2), sw_append, List.length_replicate,
        show 4 * (2 * j) = 8 * j by omega]; rfl
    have h0' : (execAll wipeBody t).regs 0 = lo + BitVec.ofNat 32 (8 * (j + 1)) := by
      rw [f0, h0, ofNat_add_assoc]; congr 2
    have hev : base + BitVec.ofNat 32 (ob + 4) = base + BitVec.ofNat 32 ob + 4#32 := by
      rw [ofNat_add_assoc]
    refine ReachT.mono (ReachT.block hb wipeBody ob t hpc ho hseq (by decide) ?_
      (wipe_ok t hpc (fun j hj => hr j (by omega)) (fun j' hj' => ?_) (by rw [hR13]; exact hsp))
      (ReachFT.bcond (ΨT := Tr.rep (fun j => wipeTr (base + BitVec.ofNat 32 ob) (lo + BitVec.ofNat 32 (8 * j))
          (brImm8 (ob + 4) ob)) (j + 1) i Ψ) (ΨF := Tr.rep (fun j => wipeTr (base + BitVec.ofNat 32 ob)
          (lo + BitVec.ofNat 32 (8 * j)) (brImm8 (ob + 4) ob)) (j + 1) i Ψ)
        hb ob (1 : BitVec 4) _ hpc1 (by omega) (instrAt_of_seqAt hbc) hsz ht (hr 4 (by omega))
        (by rw [h13']; exact hsp) hz (fun hc => ?_) (fun hc => ?_)))
      (fun _ _ h => h) (fun _ h => h) (fun tr h => ?_)
    · simp only [alignedAll, wipeBody, Instr.accesses, State.reg, List.all_append, Bool.and_eq_true]
      have e0 : LowReg.toReg 0 = 0 := rfl
      have bc : bitCount 6#8 = 2 := by decide
      simp [e0, h0, bc, Instr.next, Instr.exec, State.reg]
      exact List.all_eq_true.mp (words_aligned _ _ _ (by bv_omega))
    · rw [h0, ofNat_add_assoc]; exact hW _ (by omega)
    · rw [hz] at hc
      exact wipe_run hb ho hseq hbc ht hr h13 hsp h4 h1 h2 hK hW k i (j + 1) _ (by omega)
        (by cases i <;> simp_all) (by simp [State.setReg, State.pc]) (by simp [State.setReg, h0'])
        (by simp [State.setReg, f3, h3, ofNat_succ_sub i (by omega)])
        (fun r a b c => by simp [State.setReg, c, hrest r a b c]) (by simp [State.setReg, hm'])
    · rw [hz] at hc
      have hi0 : i = 0 := by cases i <;> simp_all
      subst hi0
      obtain rfl : K = j + 1 := by omega
      exact k _ (by simp [State.setReg, State.pc]) (by simp [State.setReg, h0'])
        (by simp [State.setReg, f3, h3]) (fun r a b c => by simp [State.setReg, c, hrest r a b c])
        (by simp [State.setReg, hm'])
    · rw [hT] at h
      exact Tr.cat_assoc _ (Tr.cat_mono (fun _ h => h) (Tr.cat_mono (fun _ h => by rw [hev] at h; exact h)
        cond_same) _ h)

end wipe


/-! ## Blocks without accesses -/

section quiet
variable {Pc Rd Wr Sp : Word → Prop} {base : Word}

/-- A block whose instructions access no memory and keep `sp`. -/
theorem blockOk_quiet : ∀ (is : List Instr) {o : Nat} (s : State),
    (∀ i ∈ is, ∀ s : State, i.accesses s = [] ∧ (i.next s).regs 13 = s.regs 13 ∧
      (i.next s).pc = s.pc + BitVec.ofNat 32 i.size) →
    s.pc = base + BitVec.ofNat 32 o → InRegion Pc base o (seqSize is) → Sp (s.regs 13) →
    BlockOk (Step Pc Rd Wr Sp) is s
  | [], _, _, _, _, _, _ => trivial
  | i :: is, o, s, h, hpc, hr, hsp => by
    obtain ⟨ha, h13, hp⟩ := h i List.mem_cons_self s
    have hsz : seqSize (i :: is) = i.size + seqSize is := by simp [seqSize]
    refine ⟨⟨by rw [hpc]; simpa using hr 0 (by rw [hsz]; have := instr_size_pos i; omega),
      fun y hy => by rw [ha] at hy; exact absurd hy (writes_nil y),
      fun y hy => by rw [ha] at hy; exact absurd hy (reads_nil y), hsp⟩, ?_⟩
    exact blockOk_quiet is (o := o + i.size) _ (fun j hj => h j (List.mem_cons_of_mem _ hj))
      (by rw [hp, hpc, ofNat_add_assoc]) (fun j hj => by
        have := hr (i.size + j) (by rw [hsz]; omega); rwa [← Nat.add_assoc] at this) (by rw [h13]; exact hsp)

/-- The trace of a block without accesses at `o`. -/
def quietTr (base : Word) : Nat → List Instr → List Event
  | _, [] => []
  | o, i :: is => ⟨base + BitVec.ofNat 32 o, i, []⟩ :: quietTr base (o + i.size) is

theorem traceAll_quiet : ∀ (is : List Instr) {o : Nat} (s : State),
    (∀ i ∈ is, ∀ s : State, i.accesses s = [] ∧ (i.next s).regs 13 = s.regs 13 ∧
      (i.next s).pc = s.pc + BitVec.ofNat 32 i.size) →
    s.pc = base + BitVec.ofNat 32 o → traceAll is s = quietTr base o is
  | [], _, _, _, _ => rfl
  | i :: is, o, s, h, hpc => by
    obtain ⟨ha, _, hp⟩ := h i List.mem_cons_self s
    simp only [traceAll, quietTr, ha, hpc, List.cons.injEq, true_and]
    exact traceAll_quiet is _ (fun j hj => h j (List.mem_cons_of_mem _ hj)) (by rw [hp, hpc, ofNat_add_assoc])

/-- **A block without accesses**, in the code region, keeping `sp`. -/
theorem quiet_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (hb : base.toNat % 2 = 0)
    {is : List Instr} {o : Nat} {s : State} {Q : State → Prop} {Ψ : TrP}
    (h : ∀ i ∈ is, ∀ s : State, i.accesses s = [] ∧ (i.next s).regs 13 = s.regs 13 ∧
      (i.next s).pc = s.pc + BitVec.ofNat 32 i.size) (hf : is.all Instr.falls = true)
    (hpc : s.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0) (hseq : seqAt B o is = true)
    (hr : InRegion Pc base o (seqSize is)) (hsp : Sp (s.regs 13))
    (k : ReachFT base Pc Rd Wr Sp (execAll is s) Q Ψ) :
    ReachFT base Pc Rd Wr Sp s Q (Tr.cat (Tr.is (quietTr base o is)) Ψ) := by
  rw [← traceAll_quiet is s h hpc]
  refine ReachT.block hb is o s hpc ho hseq hf ?_ (blockOk_quiet is s h hpc hr hsp) k
  clear hseq hr k hpc hsp
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [alignedAll, (h i List.mem_cons_self s).1, List.all_nil, Bool.true_and]
    simp only [List.all_cons, Bool.and_eq_true] at hf
    exact ih (s := i.next s) (fun j hj => h j (List.mem_cons_of_mem _ hj)) hf.2

end quiet

theorem lr0 : LowReg.toReg 0 = 0 := rfl
theorem lr1 : LowReg.toReg 1 = 1 := rfl
theorem lr2 : LowReg.toReg 2 = 2 := rfl
theorem lr3 : LowReg.toReg 3 = 3 := rfl
theorem lr4 : LowReg.toReg 4 = 4 := rfl
theorem lr5 : LowReg.toReg 5 = 5 := rfl
theorem lr6 : LowReg.toReg 6 = 6 := rfl
theorem lr7 : LowReg.toReg 7 = 7 := rfl

theorem wipeSet_quiet (K : Nat) : ∀ i ∈ wipeSet K, ∀ s : State, i.accesses s = [] ∧
    (i.next s).regs 13 = s.regs 13 ∧ (i.next s).pc = s.pc + BitVec.ofNat 32 i.size := by
  simp [lr0, lr1, lr2, lr3, wipeSet, Instr.accesses, Instr.next, Instr.exec, State.setReg, State.setNZ, State.pc, Instr.size]

theorem set_facts {K : Nat} (hK : K < 256) (t : State) :
    (execAll (wipeSet K) t).regs 0 = t.regs 13 ∧ (execAll (wipeSet K) t).regs 1 = 0 ∧
    (execAll (wipeSet K) t).regs 2 = 0 ∧ (execAll (wipeSet K) t).regs 3 = BitVec.ofNat 32 K ∧
    (execAll (wipeSet K) t).regs 12 = t.regs 0 ∧
    (∀ r : Reg, 4 ≤ r.val → r ≠ 12 → r ≠ 15 → (execAll (wipeSet K) t).regs r = t.regs r) ∧
    (execAll (wipeSet K) t).mem = t.mem ∧ (execAll (wipeSet K) t).pc = t.pc + 10#32 := by
  simp [wipeSet, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, State.sp, State.pc,
    Instr.size, lr0, lr1, lr2, lr3, setWidth8 hK]
  refine ⟨fun r h4 h12 h15 => ?_, by bv_omega⟩
  have h : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h4 <;> decide
  simp [h, h12, h15]


theorem restore_facts (t : State) :
    (execAll restoreHi t).regs 1 = 0 ∧ (execAll restoreHi t).regs 12 = 0 ∧
    (execAll restoreHi t).regs 13 = t.regs 13 + 16#32 ∧
    (execAll restoreHi t).regs 8 = read32 t.mem (t.regs 13) ∧
    (execAll restoreHi t).regs 9 = read32 t.mem (t.regs 13 + 4#32) ∧
    (execAll restoreHi t).regs 10 = read32 t.mem (t.regs 13 + 8#32) ∧
    (execAll restoreHi t).regs 11 = read32 t.mem (t.regs 13 + 12#32) ∧
    (∀ r : Reg, r.val < 4 ∨ r.val = 14 → r ≠ 1 → (execAll restoreHi t).regs r = t.regs r) ∧
    (execAll restoreHi t).mem = t.mem ∧ (execAll restoreHi t).pc = t.pc + 14#32 := by
  simp [restoreHi, execAll, Instr.next, Instr.exec, lr_f0, loadRegs, State.setReg, State.setNZ, State.reg,
    State.sp, State.pc, Instr.size, lr1, lr4, lr5, lr6, lr7, BitVec.add_assoc]
  intro r hr h1
  have h : r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 15 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
  simp [h, h1]

section restore
variable {Pc Rd Wr : Word → Prop} {base sp0 : Word} {N : Nat}

theorem restore_ok {o d : Nat} (t : State) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (hr : InRegion Pc base o 14) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hd : d ≤ N) (h16 : 16 ≤ d)
    (hRd : ∀ j < 16, Rd (sp0 - BitVec.ofNat 32 d + BitVec.ofNat 32 j)) :
    BlockOk (Step Pc Rd Wr (InStackWindow sp0 N)) restoreHi t := by
  simp [BlockOk, restoreHi, Step, Instr.next, Instr.exec, Instr.accesses, lr_f0, loadRegs, State.setReg,
    State.setNZ, State.reg, State.sp, State.pc, Instr.size, lr1, lr4, lr5, lr6, lr7, h13, writes_nil, reads_nil,
    words_no_writes, BitVec.add_assoc]
  have hp : t.regs 15 = base + BitVec.ofNat 32 o := hpc
  have pc : ∀ j < 14, Pc (t.regs 15 + BitVec.ofNat 32 j) := fun j hj => by
    rw [hp, ofNat_add_assoc]; exact hr j hj
  have w0 : InStackWindow sp0 N (sp0 - BitVec.ofNat 32 d) := ⟨d, hd, rfl⟩
  have w1 : InStackWindow sp0 N (sp0 - BitVec.ofNat 32 d + 16#32) :=
    ⟨d - 16, by omega, by
      rw [show BitVec.ofNat 32 d = BitVec.ofNat 32 (d - 16) + 16#32 by rw [← BitVec.ofNat_add]; congr 1; omega]
      bv_omega⟩
  refine ⟨⟨by simpa using pc 0 (by omega), w0⟩, ⟨pc 2 (by omega), w0⟩, ⟨pc 4 (by omega), fun y hy => ?_, w0⟩,
    ⟨pc 6 (by omega), w1⟩, ⟨pc 8 (by omega), w1⟩, ⟨pc 10 (by omega), w1⟩, pc 12 (by omega), w1⟩
  obtain ⟨o', ho', rfl⟩ := words_reads hy
  exact hRd o' (by omega)

end restore


theorem restore_trOk : traceOk restoreHi [13] = true := by decide

theorem mov012_quiet : ∀ i ∈ [Instr.movHi 0 12], ∀ s : State, i.accesses s = [] ∧
    (i.next s).regs 13 = s.regs 13 ∧ (i.next s).pc = s.pc + BitVec.ofNat 32 i.size := by
  simp [Instr.accesses, Instr.next, Instr.exec, State.setReg, State.pc, Instr.size]

theorem pop_facts (s : State) :
    (popState s 0xf0).regs 4 = read32 s.mem (s.regs 13) ∧
    (popState s 0xf0).regs 5 = read32 s.mem (s.regs 13 + 4#32) ∧
    (popState s 0xf0).regs 6 = read32 s.mem (s.regs 13 + 8#32) ∧
    (popState s 0xf0).regs 7 = read32 s.mem (s.regs 13 + 12#32) ∧
    (popState s 0xf0).pc = read32 s.mem (s.regs 13 + 16#32) &&& ~~~1#32 ∧
    (popState s 0xf0).regs 13 = s.regs 13 + 20#32 ∧
    (∀ r : Reg, r.val < 4 ∨ (8 ≤ r.val ∧ r.val < 13) ∨ r.val = 14 → (popState s 0xf0).regs r = s.regs r) ∧
    (popState s 0xf0).mem = s.mem := by
  simp [popState, lr_f0, loadRegs, State.setReg, State.sp, State.pc, lr4, lr5, lr6, lr7, nSaved, BitVec.add_assoc]
  intro r hr
  have h : r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 13 ∧ r ≠ 15 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
  simp [h]

/-- The trace of `abi_leave fs w` at `o`. -/
def leaveTr (base sp0 : Word) (fs w o : Nat) (Ψ : TrP) : TrP :=
  let cw := chunks w w
  let ob := o + 2 * cw.length + 10
  let ot := ob + 8 + 2 * (cw.length + (chunks fs fs).length)
  Tr.cat (Tr.is (spTr base false o cw)) <|
  Tr.cat (Tr.is (quietTr base (o + 2 * cw.length) (wipeSet ((fs + w) / 8)))) <|
  Tr.rep (fun j => wipeTr (base + BitVec.ofNat 32 ob) (sp0 - BitVec.ofNat 32 (36 + fs + w) + BitVec.ofNat 32 (8 * j))
    (brImm8 (ob + 4) ob)) 0 ((fs + w) / 8) <|
  Tr.cat (Tr.is (quietTr base (ob + 6) [.movHi 0 12])) <|
  Tr.cat (Tr.is (spTr base true (ob + 8) (cw ++ chunks fs fs))) <|
  Tr.cat (Tr.is (blockTr restoreHi (base + BitVec.ofNat 32 ot) [13] [sp0 - 36#32])) <|
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (ot + 14), .pop 0xf0 true, wordAccesses .read (sp0 - 20#32) 5⟩]) Ψ

/-! Address facts of the saved words, kept out of the composition's context. -/

theorem ad_sp (x : Word) : x - 36#32 + 16#32 = x - 20#32 := by bv_omega
theorem ad_lr (x : Word) : x - 20#32 + 16#32 = x - 36#32 + BitVec.ofNat 32 (4 * 8) := by bv_omega
theorem ad_lr' (x : Word) : x - 36#32 + BitVec.ofNat 32 (4 * 8) = x - 4#32 := by bv_omega
theorem ad_rd (x : Word) (o : Nat) : x - 36#32 + BitVec.ofNat 32 (16 + o) = x - 20#32 + BitVec.ofNat 32 o := by
  rw [BitVec.ofNat_add]; bv_omega
theorem ad_top (x : Word) : x - 20#32 + 20#32 = x := by bv_omega
theorem ad_hi (x : Word) (k : Nat) : x - 20#32 + BitVec.ofNat 32 (4 * k) = x - 36#32 + BitVec.ofNat 32 (4 * (4 + k)) := by
  rw [show 4 * (4 + k) = 16 + 4 * k by omega, BitVec.ofNat_add]; bv_omega
theorem ad_al (x : Word) (h4 : x.toNat % 4 = 0) : (x - 20#32).toNat % 4 = 0 := by
  rw [BitVec.toNat_sub]; simp; omega
theorem ad_36 (x : Word) (h : 36 ≤ x.toNat) : (x - 36#32).toNat = x.toNat - 36 := by
  rw [BitVec.toNat_sub]; simp; omega

section leave
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base sp0 : Word} {N : Nat}
variable {Pc Rd Wr : Word → Prop}

/-- **`abi_leave`**: the wipe of the frame and the deepest callee window, `sp` back, `r1`-`r3` and
`r12` cleared, `r4`-`r11` restored from the saved words and the return through the saved `lr`. -/
theorem leave_run (hb : base.toNat % 2 = 0) {fs w o : Nat} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0) (hseq : piecesAt B o (abiLeave fs w o) = true)
    (ht : BitVec.ofNat 32 (o + 2 * (chunks w w).length + 10 + 4) + 4#32 +
      (brImm8 (o + 2 * (chunks w w).length + 10 + 4) (o + 2 * (chunks w w).length + 10) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 (o + 2 * (chunks w w).length + 10))
    (hr : InRegion Pc base o (piecesSize (abiLeave fs w o)))
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 (36 + fs)) (h4 : sp0.toNat % 4 = 0)
    (hroom : 36 + fs + w ≤ sp0.toNat) (hfs : fs % 4 = 0) (hw : w % 4 = 0) (h8 : (fs + w) % 8 = 0)
    (hpos : 0 < fs + w) (hK : fs + w < 2048) (hN : 36 + fs + w ≤ N)
    (hW : ∀ j < fs + w, Wr (sp0 - BitVec.ofNat 32 (36 + fs + w) + BitVec.ofNat 32 j))
    (hRd : ∀ j < 36, Rd (sp0 - 36#32 + BitVec.ofNat 32 j))
    (hlr : (read32 t.mem (sp0 - 4#32)).getLsbD 0 = true)
    (k : ∀ u, u.pc = read32 t.mem (sp0 - 4#32) &&& ~~~1#32 → u.regs 13 = sp0 → u.regs 0 = t.regs 0 →
      u.regs 1 = 0 → u.regs 2 = 0 → u.regs 3 = 0 → u.regs 12 = 0 → u.regs 14 = t.regs 14 →
      (∀ i < 8, u.regs Ed25519.savedRegs[i]! = read32 t.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i))) →
      u.mem = storeWords t.mem (sp0 - BitVec.ofNat 32 (36 + fs + w)) (List.replicate (2 * ((fs + w) / 8)) 0) →
      ReachFT base Pc Rd Wr (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base Pc Rd Wr (InStackWindow sp0 N) t Q (leaveTr base sp0 fs w o Ψ) := by
  simp only [abiLeave, piecesAt, Piece.instrs, Piece.size, Bool.and_eq_true] at hseq
  simp only [abiLeave, piecesSize_cons, piecesSize_nil, Piece.size] at hr
  have hszW : seqSize (subSps w) = 2 * (chunks w w).length := by rw [subSps_eq, seqSize_sps]
  have hszH : seqSize (wipeHead fs w) = 2 * (chunks w w).length + 10 := by
    rw [wipeHead, seqSize_append, hszW]; rfl
  have hTl : leaveTail fs w = [.movHi 0 12] ++ ((chunks w w ++ chunks fs fs).map (spI true) ++ restoreHi) := by
    simp [leaveTail, addSps_eq, List.map_append]
  have hszT : seqSize (leaveTail fs w) = 2 * (chunks w w ++ chunks fs fs).length + 16 := by
    rw [hTl, seqSize_append, seqSize_append, seqSize_sps]; simp [seqSize, Instr.size, restoreHi]; omega
  obtain ⟨ob, hob⟩ : ∃ ob, ob = o + 2 * (chunks w w).length + 10 := ⟨_, rfl⟩
  obtain ⟨ot, hot⟩ : ∃ ot, ot = ob + 8 + 2 * ((chunks w w).length + (chunks fs fs).length) := ⟨_, rfl⟩
  rw [hszH, show seqSize wipeBody = 4 from rfl, show brSize = 2 from rfl, hszT,
    show o + (2 * (chunks w w).length + 10) = ob by omega] at hseq
  rw [hszH, hszT, show seqSize wipeBody = 4 from rfl, show brSize = 2 from rfl] at hr
  obtain ⟨hH, hB, hC, hT, hP, -⟩ := hseq
  rw [show ob + 4 + 2 + (2 * (chunks w w ++ chunks fs fs).length + 16) = ot + 14 by
    simp only [List.length_append] at *; omega] at hP
  rw [wipeHead, seqAt_append, hszW, Bool.and_eq_true] at hH
  rw [hTl, seqAt_append, seqAt_append, seqSize_sps, Bool.and_eq_true, Bool.and_eq_true] at hT
  rw [← hob] at ht
  have hsw : (chunks w w).sum = w := chunks_sum w w (by omega)
  have hsf : (chunks fs fs).sum = fs := chunks_sum fs fs (by omega)
  simp only [leaveTr]
  rw [← hob, ← hot]
  rw [show seqSize [Instr.movHi 0 12] = 2 from rfl, show ob + 4 + 2 = ob + 6 by omega,
    show ob + 6 + 2 = ob + 8 by omega,
    show ob + 8 + 2 * (chunks w w ++ chunks fs fs).length = ot by simp only [List.length_append]; omega] at hT
  obtain ⟨hT1, hT2, hT3⟩ := hT
  rw [show seqSize [Instr.pop 240 true] = 2 from rfl] at hr
  have reg : ∀ a n, o ≤ a → a + n ≤ ot + 16 → InRegion Pc base a n := fun a n h1 h2 j hj => by
    have := hr (a - o + j) (by simp only [List.length_append] at *; omega)
    rwa [show o + (a - o + j) = a + j by omega] at this
  have hK8 : (fs + w) / 8 < 256 := by omega
  have hsp := sp0.isLt
  have hlo : (sp0 - BitVec.ofNat 32 (36 + fs + w)).toNat = sp0.toNat - (36 + fs + w) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hlo4 : (sp0 - BitVec.ofNat 32 (36 + fs + w)).toNat % 4 = 0 := by rw [hlo]; omega
  refine sps_run hb false (chunks w w) o (36 + fs) t (fun x hx => ⟨(chunks_le w w x hx).1, chunks_four w w hw x hx⟩)
    hpc ho hH.1 (reg o _ (Nat.le_refl _) (by omega)) h13 (by omega)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) fun u1 hpu1 hu13 hur1 hum1 => ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hsw, ← Nat.add_assoc] at hu13
  obtain ⟨s0, s1, s2, s3, s12, sR, sm, spc⟩ := set_facts hK8 u1
  refine quiet_run hb (wipeSet_quiet _) rfl hpu1 (by omega) hH.2
    (reg _ _ (by omega) (by rw [show seqSize (wipeSet ((fs + w) / 8)) = 10 from rfl]; omega))
    ⟨36 + fs + w, hN, hu13⟩ ?_
  refine wipe_run hb (ob := ob) (lo := sp0 - BitVec.ofNat 32 (36 + fs + w))
    (R := (execAll (wipeSet ((fs + w) / 8)) u1).regs) (m := (execAll (wipeSet ((fs + w) / 8)) u1).mem)
    (K := (fs + w) / 8) (by omega) hB hC ht (reg _ _ (by omega) (by omega))
    (by rw [sR 13 (by decide) (by decide) (by decide), hu13]) ⟨_, hN, rfl⟩ hlo4 s1 s2 (by omega)
    (fun j hj => hW j (by omega)) (fun u3 hpu3 h03 h33 hR3 hm3 => ?_) _ 0 _ (by omega) (by omega)
    (by rw [spc, hpu1, ofNat_add_assoc, hob]) (by rw [s0, hu13]; simp) s3 (fun _ _ _ _ => rfl) rfl
  have e13 : u3.regs 13 = sp0 - BitVec.ofNat 32 (36 + fs + w) := by
    rw [hR3 13 (by decide) (by decide) (by decide), sR 13 (by decide) (by decide) (by decide), hu13]
  refine quiet_run hb mov012_quiet rfl hpu3 (by omega) hT1
    (reg _ _ (by omega) (by rw [show seqSize [Instr.movHi 0 12] = 2 from rfl]; omega))
    ⟨36 + fs + w, hN, e13⟩ ?_
  have m4 : ∀ r : Reg, r ≠ 0 → r ≠ 15 → (execAll [Instr.movHi 0 12] u3).regs r = u3.regs r := fun r a b => by
    simp [execAll, Instr.next, Instr.exec, State.setReg, a, b]
  have m40 : (execAll [Instr.movHi 0 12] u3).regs 0 = u3.regs 12 := by
    simp [execAll, Instr.next, Instr.exec, State.setReg]
  have m4pc : (execAll [Instr.movHi 0 12] u3).pc = u3.pc + 2#32 := by
    simp [execAll, Instr.next, Instr.exec, State.setReg, State.pc, Instr.size]
  have m4m : (execAll [Instr.movHi 0 12] u3).mem = u3.mem := by
    simp [execAll, Instr.next, Instr.exec, State.setReg]
  refine sps_run hb true (chunks w w ++ chunks fs fs) (ob + 8) (36 + fs + w) _
    (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨(chunks_le w w x hx).1, chunks_four w w hw x hx⟩
      · exact ⟨(chunks_le fs fs x hx).1, chunks_four fs fs hfs x hx⟩)
    (by rw [m4pc, hpu3, ofNat_add_assoc]) (by omega) hT2 (reg _ _ (by omega) (by simp only [List.length_append]; omega))
    (by rw [m4 13 (by decide) (by decide), e13]) hN (by simp only [↓reduceIte, List.sum_append, hsw, hsf]; omega)
    fun u5 hpu5 hu5 hur5 hum5 => ?_
  have e5 : u5.regs 13 = sp0 - 36#32 := by
    rw [hu5]; simp only [↓reduceIte, List.sum_append, hsw, hsf]; congr 2; omega
  have hT3' : traceAll restoreHi u5 = blockTr restoreHi (base + BitVec.ofNat 32 ot) [13] [sp0 - 36#32] :=
    traceAll_blockTr (by decide) restore_trOk
      (by rw [hpu5, hot]; congr 2; simp only [List.length_append]) (by simp [e5])
  have hpc5 : u5.pc = base + BitVec.ofNat 32 ot := by
    rw [hpu5, hot]; congr 2; simp only [List.length_append]
  rw [← hT3']
  obtain ⟨r1, r12, r13, r8, r9, r10, r11, rR, rm, rpc⟩ := restore_facts u5
  refine ReachT.block hb restoreHi ot u5 hpc5 (by omega) hT3 (by decide) ?_
    (restore_ok u5 hpc5 (reg _ _ (by omega) (by omega)) (d := 36) e5 (by omega) (by omega)
      (fun j hj => hRd j (by omega))) ?_
  · simp [alignedAll, restoreHi, Instr.accesses, Instr.next, Instr.exec, lr_f0, State.setReg, State.setNZ,
      State.sp, State.reg, lr1, e5]
    exact List.all_eq_true.mp (words_aligned _ _ _ (by rw [BitVec.toNat_sub]; simp; omega))
  have ha : (sp0 - 36#32).toNat = sp0.toNat - 36 := ad_36 sp0 (by omega)
  have hA : ∀ i < 9, ∀ x, x = sp0 - 36#32 + BitVec.ofNat 32 (4 * i) →
      read32 u5.mem x = read32 t.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) := fun i hi x hx => by
    rw [hx, hum5, m4m, hm3, sm, hum1]
    exact Field25519Slot.read32_storeWords_disj _ _ _ _ (n := 36)
      ⟨by rw [ha]; omega, by rw [List.length_replicate, hlo]; omega,
        Or.inr (by rw [List.length_replicate, hlo, ha]; omega)⟩ i (by omega)
  have e6 : (execAll restoreHi u5).regs 13 = sp0 - 20#32 := by rw [r13, e5, ad_sp]
  have bc : bitCount (240 : BitVec 8) = 4 := by decide
  have hlr6 : (read32 (execAll restoreHi u5).mem ((execAll restoreHi u5).regs 13 +
      BitVec.ofNat 32 (4 * bitCount (240 : BitVec 8)))).getLsbD 0 = true := by
    rw [rm, bc, e6, hA 8 (by omega) _ (ad_lr sp0), ad_lr']
    exact hlr
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hP
  refine ReachFT.step hb (.pop 240 true) (off := ot + 14) (by rw [rpc, hpc5, ofNat_add_assoc]) (by omega)
    hP.1.1 hP.1.2 ?_ (pop_exec _ _ hlr6)
    (by simpa using reg (ot + 14) 2 (by omega) (by omega) 0 (by omega))
    (fun y hy => by simp only [Instr.accesses] at hy; exact absurd hy words_no_writes)
    (fun y hy => ?_) ⟨20, by omega, e6⟩ ?_ ?_
  · simp only [Instr.accesses, State.sp, e6]
    exact words_aligned _ _ _ (ad_al sp0 h4)
  · simp only [Instr.accesses, State.sp, e6] at hy
    obtain ⟨o', ho', rfl⟩ := words_reads hy
    have := hRd (16 + o') (by simp [bc] at ho'; omega)
    rwa [ad_rd] at this
  · have hp6 : (execAll restoreHi u5).regs 15 = base + BitVec.ofNat 32 (ot + 14) := by
      have := rpc; rw [hpc5, ofNat_add_assoc] at this; exact this
    simp only [Instr.accesses, State.sp, e6, bc, State.pc, hp6]; rfl
  obtain ⟨p4, p5, p6, p7, ppc, p13, pR, pm⟩ := pop_facts (execAll restoreHi u5)
  refine k _ ?_ (by rw [p13, e6, ad_top]) ?_ (by rw [pR 1 (by decide), r1]) ?_ ?_ (by rw [pR 12 (by decide), r12])
    ?_ ?_ (by rw [pm, rm, hum5, m4m, hm3, sm, hum1])
  · rw [ppc, rm, e6, hA 8 (by omega) _ (ad_lr sp0), ad_lr']
  · rw [pR 0 (by decide), rR 0 (by decide) (by decide), hur5 0 (by decide) (by decide), m40,
      hR3 12 (by decide) (by decide) (by decide), s12, hur1 0 (by decide) (by decide)]
  · rw [pR 2 (by decide), rR 2 (by decide) (by decide), hur5 2 (by decide) (by decide), m4 2 (by decide) (by decide),
      hR3 2 (by decide) (by decide) (by decide), s2]
  · rw [pR 3 (by decide), rR 3 (by decide) (by decide), hur5 3 (by decide) (by decide), m4 3 (by decide) (by decide),
      h33]
  · rw [pR 14 (by decide), rR 14 (by decide) (by decide), hur5 14 (by decide) (by decide),
      m4 14 (by decide) (by decide), hR3 14 (by decide) (by decide) (by decide),
      sR 14 (by decide) (by decide) (by decide), hur1 14 (by decide) (by decide)]
  · intro i hi
    have s8 : Ed25519.savedRegs[0]! = 8 := rfl
    have s9 : Ed25519.savedRegs[1]! = 9 := rfl
    have s10 : Ed25519.savedRegs[2]! = 10 := rfl
    have s11 : Ed25519.savedRegs[3]! = 11 := rfl
    have s4 : Ed25519.savedRegs[4]! = 4 := rfl
    have s5 : Ed25519.savedRegs[5]! = 5 := rfl
    have s6 : Ed25519.savedRegs[6]! = 6 := rfl
    have s7 : Ed25519.savedRegs[7]! = 7 := rfl
    obtain _ | _ | _ | _ | _ | _ | _ | _ | i := i
    · rw [s8, pR 8 (by decide), r8, e5, hA 0 (by omega) _ (by simp)]
    · rw [s9, pR 9 (by decide), r9, e5, hA 1 (by omega) _ rfl]
    · rw [s10, pR 10 (by decide), r10, e5, hA 2 (by omega) _ rfl]
    · rw [s11, pR 11 (by decide), r11, e5, hA 3 (by omega) _ rfl]
    · rw [s4, p4, rm, e6, hA 4 (by omega) _ (by simpa using ad_hi sp0 0)]
    · rw [s5, p5, rm, e6, hA 5 (by omega) _ (ad_hi sp0 1)]
    · rw [s6, p6, rm, e6, hA 6 (by omega) _ (ad_hi sp0 2)]
    · rw [s7, p7, rm, e6, hA 7 (by omega) _ (ad_hi sp0 3)]
    · omega

end leave

end M0Crypto.Release.Ed25519CallProg
