import M0Crypto.Release.X25519EntryCode
import M0Crypto.Release.X25519Decode

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
Pieces of the prologue proof of `m0c_x25519` (plan `x25519-proofs.md`, phase 9, step 2).

* The input words as the code builds them: `kWords c` (the clamped scalar, `kWords_val`) and
  `uWords c` (u with bit 255 masked, `uWords_val`), both as `X25519Decode.words` of the input
  bytes. `feVal_words` reads a field element written as eight words.
* The word adjustments of `scalarWord` and `pointWord` (`adjK`, `adjU`) and their values
  (`adjK_val`, `adjU_val`), generic in the word index.
* Splitting `words f` at word `i` (`words_split`), so a segment lemma generic in `i` gets its
  `seqAt` from the whole list.
-/

namespace M0Crypto.Release.X25519Prologue
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region)
open M0Crypto.Release.Frame (Disj InFrame)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Bytes (loadLe32)
open M0Crypto.Release.X25519Val (val Words)
open M0Crypto.Release.X25519Routines (feVal)

/-! ## Input words -/

/-- The clamped scalar as the eight words the code stores in `S_K`. -/
def kWords (c : X25519.Ctx) : List Nat :=
  X25519Decode.words c.scalarB (fun w => w / 8 * 8) (fun w => w % 2 ^ 30 + 2 ^ 30)

/-- u with bit 255 masked, as the eight words the code stores in `X1` and `X3`. -/
def uWords (c : X25519.Ctx) : List Nat :=
  X25519Decode.words c.pointB id (fun w => w % 2 ^ 31)

theorem scalarB_length (c : X25519.Ctx) : c.scalarB.length = 32 := Frame.bytesAt_length _ _ _
theorem pointB_length (c : X25519.Ctx) : c.pointB.length = 32 := Frame.bytesAt_length _ _ _

theorem kWords_val (c : X25519.Ctx) :
    val (kWords c) = Spec.X25519.decodeScalar25519 c.scalarB :=
  (X25519Decode.decodeScalar_val _ (scalarB_length c)).symm

theorem uWords_val (c : X25519.Ctx) :
    val (uWords c) = Spec.X25519.decodeUCoordinate c.pointB :=
  (X25519Decode.decodeU_val _ (pointB_length c)).symm

theorem words_length (bs : List X25519Decode.Byte) (f0 f7 : Nat → Nat) :
    (X25519Decode.words bs f0 f7).length = 8 := rfl

/-- Word `i` of `words`: `f0` applied at 0, `f7` at 7, the plain word elsewhere. -/
theorem words_getD (bs : List X25519Decode.Byte) (f0 f7 : Nat → Nat) {i : Nat} (hi : i < 8) :
    (X25519Decode.words bs f0 f7).getD i 0 =
      if i = 0 then f0 (X25519Decode.leWord bs 0)
      else if i = 7 then f7 (X25519Decode.leWord bs 7) else X25519Decode.leWord bs i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Byte `j` of an input buffer read from memory. -/
theorem bytesAt_getD (m : Mem) (a : Word) {n j : Nat} (hj : j < n) :
    (Frame.Ctx.bytesAt m a n).getD j 0 = m (a + BitVec.ofNat 32 j) := by
  rw [List.getD_eq_getElem?_getD, Frame.bytesAt_get m a n j hj]; rfl

/-- `feVal` of eight words that read as the list `ws`. -/
theorem feVal_words (m : Mem) (a : Word) (ws : List Nat) (hl : ws.length = 8)
    (h : ∀ i < 8, (read32 m (a + BitVec.ofNat 32 (4 * i))).toNat = ws.getD i 0) :
    feVal m a = val ws := by
  match ws, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    rw [X25519Val.val_eight, X25519MulcFacts.feVal_psum]
    have e : ∀ i < 8, (read32 m (slot a i)).toNat = [w0, w1, w2, w3, w4, w5, w6, w7].getD i 0 :=
      fun i hi => h i hi
    simp only [X25519MulcChain.psum, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]
    simp

/-! ## Word adjustments -/

/-- The instructions of `scalarWord i` between the load and the store. -/
def adjK (i : Nat) : List Instr :=
  (if i = 0 then [.lsrImm 4 4 3, .lslImm 4 4 3] else []) ++
  (if i = 7 then [.lslImm 4 4 2, .lsrImm 4 4 2, .movImm 3 1, .lslImm 3 3 30, .dp .orrs 4 3] else [])

/-- The instructions of `pointWord i` between the load and the stores. -/
def adjU (i : Nat) : List Instr :=
  if i = 7 then [.lslImm 4 4 1, .lsrImm 4 4 1] else []

theorem scalarWord_eq (i : Nat) :
    scalarWord i = loadLe32 4 3 1 (4 * i) ++
      (adjK i ++ [.strSp 4 (BitVec.ofNat 8 (sK / 4 + i))]) := by
  simp only [scalarWord, adjK, List.append_assoc]

theorem pointWord_eq (i : Nat) :
    pointWord i = loadLe32 4 3 2 (4 * i) ++
      (adjU i ++ [.strSp 4 (BitVec.ofNat 8 (sX1 / 4 + i)), .strSp 4 (BitVec.ofNat 8 (sX3 / 4 + i))]) := by
  simp only [pointWord, adjU, List.append_assoc, List.singleton_append, List.cons_append]

theorem adjK_reg (i : Nat) : (adjK i).all X25519Mul.regOnly = true ∧ (adjK i).all (!·.writesMem) = true := by
  unfold adjK; split <;> split <;> exact ⟨rfl, rfl⟩

theorem adjU_reg (i : Nat) : (adjU i).all X25519Mul.regOnly = true ∧ (adjU i).all (!·.writesMem) = true := by
  unfold adjU; split <;> exact ⟨rfl, rfl⟩

theorem adjK_falls (i : Nat) : (adjK i).all Instr.falls = true := by
  unfold adjK; split <;> split <;> rfl

theorem adjU_falls (i : Nat) : (adjU i).all Instr.falls = true := by
  unfold adjU; split <;> rfl

/-- The scalar adjustment on a word value: clear bits 0-2 of word 0, clear bit 31 and set bit
30 of word 7. -/
def adjKv (i w : Nat) : Nat :=
  if i = 0 then w / 8 * 8 else if i = 7 then w % 2 ^ 30 + 2 ^ 30 else w

/-- The u adjustment: clear bit 31 of word 7. -/
def adjUv (i w : Nat) : Nat := if i = 7 then w % 2 ^ 31 else w

theorem regs_lsl (s : State) (d m : LowReg) (n : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lslImm d m n).next s).regs r =
      if r = d.toReg then (lslC (s.reg m) n.toNat s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, hr]

theorem regs_lsr (s : State) (d m : LowReg) (n : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lsrImm d m n).next s).regs r =
      if r = d.toReg then (lsrC (s.reg m) (if n.toNat = 0 then 32 else n.toNat)).1 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, hr]

theorem regs_movImm (s : State) (d : LowReg) (n : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.movImm d n).next s).regs r = if r = d.toReg then n.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_orrs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .orrs d m).next s).regs r = if r = d.toReg then s.reg d ||| s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem toNat_shr_shl (x : Word) (n : Nat) : ((x >>> n) <<< n).toNat = x.toNat / 2 ^ n * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  have := x.isLt
  have := Nat.div_mul_le_self x.toNat (2 ^ n)
  omega

theorem shl_shr_nat (x n : Nat) (hn : n ≤ 32) : (x <<< n % 2 ^ 32) >>> n = x % 2 ^ (32 - n) := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ 32 = 2 ^ (32 - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos n)]

/-- The registers an adjustment leaves alone. -/
theorem adjK_other (s : State) (i : Nat) {r : Reg} (h3 : r ≠ 3) (h4 : r ≠ 4) (h15 : r ≠ 15) :
    (execAll (adjK i) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e))
  unfold adjK
  have a3 : r.val ≠ 3 := fun e => h3 (Fin.ext e)
  have a4 : r.val ≠ 4 := fun e => h4 (Fin.ext e)
  have v3 : ((3 : LowReg) : Nat) = 3 := rfl
  have v4 : ((4 : LowReg) : Nat) = 4 := rfl
  split <;> split <;> simp [Instr.dsts, LowReg.toReg, a3, a4, v3, v4]

theorem adjU_other (s : State) (i : Nat) {r : Reg} (h4 : r ≠ 4) (h15 : r ≠ 15) :
    (execAll (adjU i) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e))
  unfold adjU
  have a4 : r.val ≠ 4 := fun e => h4 (Fin.ext e)
  have v4 : ((4 : LowReg) : Nat) = 4 := rfl
  split <;> simp [Instr.dsts, LowReg.toReg, a4, v4]

theorem adjK_val (s : State) (i : Nat) :
    ((execAll (adjK i) s).regs 4).toNat = adjKv i (s.regs 4).toNat := by
  unfold adjK adjKv
  by_cases h0 : i = 0
  · subst h0
    simp [execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.reg, lslC, lsrC,
      X25519Mem.toReg4]
    exact toNat_shr_shl _ 3
  · by_cases h7 : i = 7
    · subst h7
      simp [execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZ, State.reg, lslC,
        lsrC, X25519Mem.toReg4, X25519Mem.toReg3]
      have e := shl_shr_nat (s.regs 4).toNat 2 (by omega)
      simp only [Nat.reducePow, Nat.reduceSub] at e
      rw [e]
      have h := X25519Decode.or_shift ((s.regs 4).toNat % 2 ^ 30) 1 30 (Nat.mod_lt _ (by decide))
      simp only [Nat.reducePow, Nat.one_shiftLeft, Nat.mul_one] at h
      exact h
    · simp only [if_neg h0, if_neg h7, List.append_nil, execAll]

theorem adjU_val (s : State) (i : Nat) :
    ((execAll (adjU i) s).regs 4).toNat = adjUv i (s.regs 4).toNat := by
  unfold adjU adjUv
  by_cases h7 : i = 7
  · subst h7
    simp [execAll, Instr.next, Instr.exec, State.setReg, State.setNZC, State.reg, lslC, lsrC,
      X25519Mem.toReg4]
    have e := shl_shr_nat (s.regs 4).toNat 1 (by omega)
    simp only [Nat.reducePow, Nat.reduceSub] at e
    exact e
  · simp only [if_neg h7, execAll]

theorem adjKv_words (c : X25519.Ctx) {i : Nat} (hi : i < 8) :
    adjKv i (X25519Decode.leWord c.scalarB i) = (kWords c).getD i 0 := by
  rw [kWords, words_getD _ _ _ hi, adjKv]
  split
  · subst_vars; rfl
  · split
    · subst_vars; rfl
    · rfl

theorem adjUv_words (c : X25519.Ctx) {i : Nat} (hi : i < 8) :
    adjUv i (X25519Decode.leWord c.pointB i) = (uWords c).getD i 0 := by
  rw [uWords, words_getD _ _ _ hi, adjUv]
  split
  · subst_vars; rfl
  · split
    · subst_vars; rfl
    · rfl

/-! ## Splitting `words` -/

theorem words_split (f : Nat → List Instr) {i : Nat} (hi : i < 8) :
    words f = (List.range i).flatMap f ++ f i ++ (List.range' (i + 1) (7 - i)).flatMap f := by
  have e : List.range 8 = List.range i ++ [i] ++ List.range' (i + 1) (7 - i) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [words, e, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]

theorem words_succ (f : Nat → List Instr) (i : Nat) :
    (List.range (i + 1)).flatMap f = (List.range i).flatMap f ++ f i := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

end M0Crypto.Release.X25519Prologue
