import M0Crypto.Release.Blake2sPro
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace M0Crypto.Release.Blake2sTail

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode
open M0Crypto.Release.Blake2sPro
open M0Crypto.Release.Blake2s (toReg_ne15 mem_dp mem_movHi mem_ldrSp mem_movImm regs_movImm)

theorem RA_ldrImm {s : State} {R : Reg → Word} (h : RA s R) (d n : LowReg) (i : BitVec 5) :
    RA ((Instr.memImm .ldr d n i).next s)
      (upd R d.toReg (read32 s.mem (R n.toReg + BitVec.ofNat 32 (i.toNat * 4)))) := by
  intro r hr
  have e : ((Instr.memImm .ldr d n i).next s).regs r =
      if r = d.toReg then read32 s.mem (s.regs n.toReg + BitVec.ofNat 32 (i.toNat * 4)) else s.regs r := by
    simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, hr, MemOp.width]
  rw [e]
  by_cases e1 : r = d.toReg
  · subst e1; simp [upd, h _ (toReg_ne15 n)]
  · simp [upd, e1, h r hr]

theorem mem_ldrImm (s : State) (d n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .ldr d n i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg]

theorem RA_subImm8 {s : State} {R : Reg → Word} (h : RA s R) (d : LowReg) (i : BitVec 8) :
    RA ((Instr.subImm8 d i).next s) (upd R d.toReg (R d.toReg - i.setWidth 32)) := by
  intro r hr
  have e : ((Instr.subImm8 d i).next s).regs r =
      if r = d.toReg then s.regs d.toReg - i.setWidth 32 else s.regs r := by
    simp [Instr.next, Instr.exec, addFlags, State.setReg, State.reg, hr]
    rw [M0Crypto.Release.sub_flags]
  rw [e]
  by_cases e1 : r = d.toReg
  · subst e1; simp [upd, h _ (toReg_ne15 d)]
  · simp [upd, e1, h r hr]

theorem mem_subImm8 (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.subImm8 d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ]

theorem mem_stm2e (s : State) : ((Instr.stm 4 0x2e).next s).mem =
    storeWords s.mem (s.regs 4) [s.regs 1, s.regs 2, s.regs 3, s.regs 5] := by
  rw [mem_stm]
  have : listRegs 0x2e#8 = [1, 2, 3, 5] := by decide
  simp [this, LowReg.toReg] <;> rfl

theorem mem_stm0f (s : State) : ((Instr.stm 4 0x0f).next s).mem =
    storeWords s.mem (s.regs 4) [s.regs 0, s.regs 1, s.regs 2, s.regs 3] := by
  rw [mem_stm]
  have : listRegs 0x0f#8 = [0, 1, 2, 3] := by decide
  simp [this, LowReg.toReg] <;> rfl

theorem regs_stm4 (s : State) (l : BitVec 8) (hb : bitCount l = 4) (r : Reg) (hr : r ≠ 15) :
    ((Instr.stm 4 l).next s).regs r = if r = 4 then s.regs 4 + 16#32 else s.regs r := by
  rw [regs_stm _ _ _ r hr]
  simp [State.reg, hb, LowReg.toReg] <;> rfl

theorem RA_stm4 {s : State} {R : Reg → Word} (l : BitVec 8) (hb : bitCount l = 4) (h : RA s R) :
    RA ((Instr.stm 4 l).next s) (upd R 4 (R 4 + 16#32)) := by
  intro r hr
  rw [regs_stm4 _ _ hb _ hr]
  by_cases e : r = 4
  · subst e; simp [upd, h 4 (by decide)]
  · simp [upd, e, h r hr]

theorem RA_ldm4f {s : State} {R : Reg → Word} (h : RA s R) :
    RA ((Instr.ldm 4 0x0f).next s)
      (upd (upd (upd (upd (upd R 0 (read32 s.mem (R 4))) 1 (read32 s.mem (R 4 + 4#32))) 2
        (read32 s.mem (R 4 + 8#32))) 3 (read32 s.mem (R 4 + 12#32))) 4 (R 4 + 16#32)) := by
  have l : listRegs 0x0f#8 = [0, 1, 2, 3] := by decide
  have hb : bitCount 0x0f#8 = 4 := by decide
  have h4 := h 4 (by decide)
  intro r hr
  have e : ((Instr.ldm 4 0x0f).next s).regs r =
      if r = 0 then read32 s.mem (s.regs 4) else if r = 1 then read32 s.mem (s.regs 4 + 4#32)
      else if r = 2 then read32 s.mem (s.regs 4 + 8#32) else if r = 3 then read32 s.mem (s.regs 4 + 12#32)
      else if r = 4 then s.regs 4 + 16#32 else s.regs r := by
    simp (config := {decide := true}) [Instr.next, Instr.exec, l, hb, loadRegs, State.setReg, State.reg, hr, LowReg.toReg]
    have e8 : s.regs 4 + 4#32 + 4#32 = s.regs 4 + 8#32 := by bv_omega
    have e12 : s.regs 4 + 8#32 + 4#32 = s.regs 4 + 12#32 := by bv_omega
    have e12b : s.regs 4 + 4#32 + 4#32 + 4#32 = s.regs 4 + 12#32 := by bv_omega
    try simp only [e8, e12, e12b]
    obtain ⟨rv, hrv⟩ := r
    simp (config := {decide := true}) only [Fin.ext_iff] at hr ⊢
    repeat' split
    all_goals first | rfl | (exfalso; omega) | exact congrArg (read32 s.mem) e8 | exact congrArg (read32 s.mem) e12b | exact congrArg (read32 s.mem) e12
  rw [e, h4]
  by_cases e0 : r = 0
  · subst e0; simp [upd]
  · by_cases e1 : r = 1
    · subst e1; simp [upd]
    · by_cases e2 : r = 2
      · subst e2; simp [upd]
      · by_cases e3 : r = 3
        · subst e3; simp [upd]
        · by_cases e4 : r = 4
          · subst e4; simp [upd]
          · simp [upd, e0, e1, e2, e3, e4, h r hr]

theorem RA_addSp {s : State} {R : Reg → Word} (h : RA s R) (i : BitVec 7) :
    RA ((Instr.addSp i).next s) (upd R 13 (R 13 + BitVec.ofNat 32 (i.toNat * 4))) := by
  intro r hr
  have e : ((Instr.addSp i).next s).regs r =
      if r = 13 then s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
    simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]
  rw [e]
  by_cases e1 : r = 13
  · subst e1; simp [upd, h 13 (by decide)]
  · simp [upd, e1, h r hr]

theorem mem_addSp (s : State) (i : BitVec 7) : ((Instr.addSp i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem RA_movImm {s : State} {R : Reg → Word} (h : RA s R) (d : LowReg) (i : BitVec 8) :
    RA ((Instr.movImm d i).next s) (upd R d.toReg (i.setWidth 32)) := by
  intro r hr
  rw [regs_movImm _ _ _ _ hr]
  by_cases e : r = d.toReg
  · subst e; simp [upd]
  · simp [upd, e, h r hr]

theorem storeWords_append (M : Mem) : ∀ (l1 l2 : List Word) (a : Word),
    storeWords M a (l1 ++ l2) = storeWords (storeWords M a l1) (a + BitVec.ofNat 32 (4 * l1.length)) l2
  | [], l2, a => by simp [storeWords]
  | v :: l1, l2, a => by
    simp only [List.cons_append, storeWords, List.length_cons]
    rw [storeWords_append _ l1 l2 (a + 4#32)]
    have : a + 4#32 + BitVec.ofNat 32 (4 * l1.length) = a + BitVec.ofNat 32 (4 * (l1.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      rw [show (4#32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]; congr 1; omega
    rw [this]

/-- `n` batches `stm r5!, {r0-r4}` with r0-r4 zero store `5 * n` zero words from r5 and change no
register but r5. One lemma for any batch count. -/
theorem fill_eff : ∀ (n : Nat) (t : State), (∀ r : Reg, r.val < 5 → t.regs r = 0#32) →
    (execAll (List.replicate n (Instr.stm 5 0x1f)) t).mem =
        storeWords t.mem (t.regs 5) (List.replicate (5 * n) 0#32) ∧
      (execAll (List.replicate n (Instr.stm 5 0x1f)) t).regs 5 = t.regs 5 + BitVec.ofNat 32 (20 * n) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 5 → (execAll (List.replicate n (Instr.stm 5 0x1f)) t).regs r = t.regs r
  | 0, t, _ => ⟨rfl, by simp [execAll], fun _ _ _ => rfl⟩
  | n + 1, t, hz => by
    obtain ⟨u, hu⟩ : ∃ x, x = (Instr.stm 5 0x1f).next t := ⟨_, rfl⟩
    have hb : bitCount (0x1f : BitVec 8) = 5 := by decide
    have hl : listRegs (0x1f : BitVec 8) = [0, 1, 2, 3, 4] := by decide
    have hr5 : u.regs 5 = t.regs 5 + BitVec.ofNat 32 20 := by
      rw [hu, regs_stm _ _ _ 5 (by decide), hb]; rfl
    have hro : ∀ r : Reg, r ≠ 15 → r ≠ 5 → u.regs r = t.regs r := by
      intro r h15 h5
      have h5' : ¬ r = (5 : LowReg).toReg := h5
      rw [hu, regs_stm _ _ _ r h15]; simp [h5']
    have hm : u.mem = storeWords t.mem (t.regs 5) (List.replicate 5 0#32) := by
      rw [hu, mem_stm, hl]
      show storeWords t.mem (t.regs 5) [t.regs 0, t.regs 1, t.regs 2, t.regs 3, t.regs 4] = _
      rw [hz 0 (by decide), hz 1 (by decide), hz 2 (by decide), hz 3 (by decide), hz 4 (by decide)]
      rfl
    have hz' : ∀ r : Reg, r.val < 5 → u.regs r = 0#32 := by
      intro r h5
      rw [hro r (by rintro rfl; exact absurd h5 (by decide)) (by rintro rfl; exact absurd h5 (by decide))]
      exact hz r h5
    obtain ⟨im, i5, io⟩ := fill_eff n u hz'
    have hx : execAll (List.replicate (n + 1) (Instr.stm 5 0x1f)) t =
        execAll (List.replicate n (Instr.stm 5 0x1f)) u := by rw [hu]; rfl
    rw [hx]
    refine ⟨?_, ?_, fun r h15 h5 => (io r h15 h5).trans (hro r h15 h5)⟩
    · have e : List.replicate (5 * (n + 1)) (0#32 : Word) =
          List.replicate 5 0#32 ++ List.replicate (5 * n) 0#32 := by
        rw [List.replicate_append_replicate]; congr 1; omega
      rw [im, hm, hr5, e, storeWords_append]
      rfl
    · rw [i5, hr5, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega


open M0Crypto.Release.Frame (read32_congr Disj)

/-- A word read from outside a run of stored words is unchanged. -/
theorem read32_storeWords_ne (m : Mem) (a : Word) (vs : List Word) (b : Word)
    (h : Disj a (4 * vs.length) b 4) : read32 (storeWords m a vs) b = read32 m b := by
  obtain ⟨h1, h2, h3⟩ := h
  apply read32_congr
  intro k hk
  apply storeWords_other
  intro i q hi hq e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega


/-- The feed-forward of the working-vector half held in registers and slots 1, 3. -/
def S1 : List Instr :=
  [ .dp .eors 0 6, .movHi 6 8, .dp .eors 2 6, .ldrSp 6 1, .dp .eors 5 6, .ldrSp 6 3, .dp .eors 7 6,
    .ldrSp 4 HPTR_WORDS ]

theorem S1_eq : S1 = tail.take 8 := by decide

theorem mem_eors (s : State) (d m : LowReg) : ((Instr.dp .eors d m).next s).mem = s.mem :=
  mem_dp s .eors d m (Or.inl rfl)

theorem S1_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S1 t) R' ∧
      R' 0 = R 0 ^^^ R 6 ∧ R' 1 = R 1 ∧ R' 2 = R 2 ^^^ R 8 ∧ R' 3 = R 3 ∧
      R' 4 = read32 t.mem (R 13 + BitVec.ofNat 32 HPTR_SLOT) ∧
      R' 5 = R 5 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 4) ∧
      R' 6 = read32 t.mem (R 13 + BitVec.ofNat 32 12) ∧
      R' 7 = R 7 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 12) ∧
      (∀ r : Reg, 8 ≤ r.val → r ≠ 15 → R' r = R r) := by
  have a1 := RA_eors h 0 6
  have a2 := RA_movHi a1 6 8 (by decide) (by decide)
  have a3 := RA_eors a2 2 6
  have a4 := RA_ldrSp a3 6 1
  have a5 := RA_eors a4 5 6
  have a6 := RA_ldrSp a5 6 3
  have a7 := RA_eors a6 7 6
  have a8 := RA_ldrSp a7 4 HPTR_WORDS
  refine ⟨_, (a8 : RA (execAll S1 t) _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp]; done)
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp]; rfl)
    | (intro r h8 h15
       obtain ⟨rv, hrv⟩ := r
       simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp, Fin.ext_iff] at h8 h15 ⊢
       repeat' split
       all_goals first | rfl | (exfalso; omega))


def S2a : List Instr :=
  [ .memImm .ldr 1 4 0, .dp .eors 1 2, .memImm .ldr 2 4 1, .dp .eors 2 5,
    .memImm .ldr 3 4 2, .dp .eors 3 0, .memImm .ldr 5 4 3, .dp .eors 5 7 ]

theorem S2a_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S2a t) R' ∧ (execAll S2a t).mem = t.mem ∧
      R' 1 = read32 t.mem (R 4) ^^^ R 2 ∧
      R' 2 = read32 t.mem (R 4 + 4#32) ^^^ R 5 ∧
      R' 3 = read32 t.mem (R 4 + 8#32) ^^^ R 0 ∧
      R' 5 = read32 t.mem (R 4 + 12#32) ^^^ R 7 ∧
      (∀ r : Reg, r ≠ 15 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 5 → R' r = R r) := by
  have a1 := RA_ldrImm h 1 4 0
  have a2 := RA_eors a1 1 2
  have a3 := RA_ldrImm a2 2 4 1
  have a4 := RA_eors a3 2 5
  have a5 := RA_ldrImm a4 3 4 2
  have a6 := RA_eors a5 3 0
  have a7 := RA_ldrImm a6 5 4 3
  have a8 := RA_eors a7 5 7
  have hm : (execAll S2a t).mem = t.mem := execAll_mem S2a t (by decide)
  refine ⟨_, (a8 : RA (execAll S2a t) _), hm, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_ldrImm]; done)
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_ldrImm]; rfl)
    | (intro r h15 h1 h2 h3 h5
       obtain ⟨rv, hrv⟩ := r
       simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_ldrImm, Fin.ext_iff] at h15 h1 h2 h3 h5 ⊢
       repeat' split
       all_goals first | rfl | (exfalso; omega))

def S2b : List Instr := [ .stm 4 0x2e, .ldm 4 0x0f ]

theorem S2b_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S2b t) R' ∧
      (execAll S2b t).mem = storeWords t.mem (R 4) [R 1, R 2, R 3, R 5] ∧
      R' 0 = read32 (storeWords t.mem (R 4) [R 1, R 2, R 3, R 5]) (R 4 + 16#32) ∧
      R' 1 = read32 (storeWords t.mem (R 4) [R 1, R 2, R 3, R 5]) (R 4 + 20#32) ∧
      R' 2 = read32 (storeWords t.mem (R 4) [R 1, R 2, R 3, R 5]) (R 4 + 24#32) ∧
      R' 3 = read32 (storeWords t.mem (R 4) [R 1, R 2, R 3, R 5]) (R 4 + 28#32) ∧
      R' 4 = R 4 + 32#32 ∧
      (∀ r : Reg, r ≠ 15 → 5 ≤ r.val → R' r = R r) := by
  have a1 := RA_stm4 0x2e (by decide) h
  have hm1 := mem_stm2e t
  have hm1' : ((Instr.stm 4 46).next t).mem = storeWords t.mem (R 4) [R 1, R 2, R 3, R 5] := by
    rw [hm1, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 5 (by decide), h 4 (by decide)]
  have e20 : R 4 + 16#32 + 4#32 = R 4 + 20#32 := by bv_omega
  have e24 : R 4 + 16#32 + 4#32 + 4#32 = R 4 + 24#32 := by bv_omega
  have e28 : R 4 + 16#32 + 4#32 + 4#32 + 4#32 = R 4 + 28#32 := by bv_omega
  have e24' : R 4 + 16#32 + 8#32 = R 4 + 24#32 := by bv_omega
  have e28' : R 4 + 16#32 + 12#32 = R 4 + 28#32 := by bv_omega
  have e32 : R 4 + 16#32 + 16#32 = R 4 + 32#32 := by bv_omega
  have a2 := RA_ldm4f a1
  rw [hm1'] at a2
  have hm2 : (execAll S2b t).mem = storeWords t.mem (R 4) [R 1, R 2, R 3, R 5] := by
    show ((Instr.ldm 4 0x0f).next ((Instr.stm 4 0x2e).next t)).mem = _
    rw [mem_ldm, hm1, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 5 (by decide), h 4 (by decide)]
  refine ⟨_, (a2 : RA (execAll S2b t) _), hm2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r h15 h5
       obtain ⟨rv, hrv⟩ := r
       simp (config := {decide := true}) [upd, Fin.ext_iff] at h15 h5 ⊢
       repeat' split
       all_goals first | rfl | (exfalso; omega))
    | (simp (config := {decide := true}) [upd, hm1', e20, e24, e28, e32, e24', e28']; done)
    | (simp (config := {decide := true}) [upd, hm1', e20, e24, e28, e32, e24', e28']; bv_omega)

def S3a : List Instr :=
  [ .ldrSp 6 4, .dp .eors 0 6, .movHi 6 9, .dp .eors 0 6,
    .ldrSp 6 5, .dp .eors 1 6, .movHi 6 10, .dp .eors 1 6,
    .ldrSp 6 6, .dp .eors 2 6, .movHi 6 11, .dp .eors 2 6,
    .ldrSp 6 7, .dp .eors 3 6, .movHi 6 12, .dp .eors 3 6,
    .subImm8 4 16 ]

theorem S3a_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S3a t) R' ∧ (execAll S3a t).mem = t.mem ∧
      R' 0 = R 0 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 16) ^^^ R 9 ∧
      R' 1 = R 1 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 20) ^^^ R 10 ∧
      R' 2 = R 2 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 24) ^^^ R 11 ∧
      R' 3 = R 3 ^^^ read32 t.mem (R 13 + BitVec.ofNat 32 28) ^^^ R 12 ∧
      R' 4 = R 4 - 16#32 ∧ R' 6 = R 12 ∧
      (∀ r : Reg, r ≠ 15 → r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 6 → R' r = R r) := by
  have a1 := RA_ldrSp h 6 4
  have a2 := RA_eors a1 0 6
  have a3 := RA_movHi a2 6 9 (by decide) (by decide)
  have a4 := RA_eors a3 0 6
  have a5 := RA_ldrSp a4 6 5
  have a6 := RA_eors a5 1 6
  have a7 := RA_movHi a6 6 10 (by decide) (by decide)
  have a8 := RA_eors a7 1 6
  have a9 := RA_ldrSp a8 6 6
  have a10 := RA_eors a9 2 6
  have a11 := RA_movHi a10 6 11 (by decide) (by decide)
  have a12 := RA_eors a11 2 6
  have a13 := RA_ldrSp a12 6 7
  have a14 := RA_eors a13 3 6
  have a15 := RA_movHi a14 6 12 (by decide) (by decide)
  have a16 := RA_eors a15 3 6
  have a17 := RA_subImm8 a16 4 16
  have hm : (execAll S3a t).mem = t.mem := by
    refine execAll_mem S3a t (by decide)
  refine ⟨_, (a17 : RA (execAll S3a t) _), hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp, mem_subImm8]; done)
    | (simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp, mem_subImm8]; rfl)
    | (intro r h15 h0 h1 h2 h3 h4 h6
       obtain ⟨rv, hrv⟩ := r
       simp (config := {decide := true}) [upd, LowReg.toReg, mem_eors, mem_movHi, mem_ldrSp, mem_subImm8, Fin.ext_iff] at h15 h0 h1 h2 h3 h4 h6 ⊢
       repeat' split
       all_goals first | rfl | (exfalso; omega))

def S3b : List Instr := [ .stm 4 0x0f ]

theorem S3b_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S3b t) R' ∧
      (execAll S3b t).mem = storeWords t.mem (R 4) [R 0, R 1, R 2, R 3] ∧
      R' 4 = R 4 + 16#32 ∧ (∀ r : Reg, r ≠ 15 → r ≠ 4 → R' r = R r) := by
  have a1 := RA_stm4 0x0f (by decide) h
  have hm := mem_stm0f t
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)] at hm
  refine ⟨_, (a1 : RA (execAll S3b t) _), hm, ?_, ?_⟩
  · simp [upd]
  · intro r _ h4; simp [upd, h4]

/-- The frame clear. -/
def S3c : List Instr := clearI

/-- The clear's batches cover the locals exactly. -/
theorem clear_words : 5 * clearBatches = LOCALS_WORDS := by decide

theorem S3c_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S3c t) R' ∧
      (execAll S3c t).mem = storeWords t.mem (R 13) (List.replicate LOCALS_WORDS 0#32) ∧
      (∀ r : Reg, r.val < 4 → R' r = 0#32) ∧ R' 12 = 0#32 ∧
      (∀ r : Reg, r ≠ 15 → 6 ≤ r.val → r.val ≠ 12 → R' r = R r) := by
  obtain ⟨t1, ht1⟩ : ∃ x, x = execAll [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0,
    .movImm 4 0, .addRdSp 5 0] t := ⟨_, rfl⟩
  have a6 := RA_addRdSp (RA_movImm (RA_movImm (RA_movImm (RA_movImm (RA_movImm h 0 0) 1 0) 2 0) 3 0) 4 0) 5 0
  change RA (execAll [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0, .addRdSp 5 0] t) _ at a6
  rw [← ht1] at a6
  have hm1 : t1.mem = t.mem := by rw [ht1]; exact execAll_mem _ t (by decide)
  have hz : ∀ r : Reg, r.val < 5 → t1.regs r = 0#32 := by
    intro r h5
    rw [a6 r (by rintro rfl; exact absurd h5 (by decide))]
    obtain ⟨rv, hrv⟩ := r
    simp (config := {decide := true}) [upd, LowReg.toReg, Fin.ext_iff] at h5 ⊢
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  have h5 : t1.regs 5 = R 13 := by
    rw [a6 5 (by decide)]; simp (config := {decide := true}) [upd, LowReg.toReg]
  have ho : ∀ r : Reg, r ≠ 15 → 6 ≤ r.val → t1.regs r = R r := by
    intro r h15 h6
    rw [a6 r h15]
    obtain ⟨rv, hrv⟩ := r
    simp (config := {decide := true}) [upd, LowReg.toReg, Fin.ext_iff] at h15 h6 ⊢
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  obtain ⟨fm, _, fo⟩ := fill_eff clearBatches t1 hz
  obtain ⟨t2, ht2⟩ : ∃ x, x = execAll (List.replicate clearBatches (Instr.stm 5 0x1f)) t1 := ⟨_, rfl⟩
  rw [← ht2] at fm fo
  have hx : execAll S3c t = (Instr.movHi 12 0).next t2 := by
    rw [ht2, ht1]; simp only [S3c, clearI, execAll_append]; rfl
  have hr : ∀ r : Reg, r ≠ 15 → ((Instr.movHi 12 0).next t2).regs r =
      upd t2.regs 12 (t2.regs 0) r := RA_movHi (fun _ _ => rfl) 12 0 (by decide) (by decide)
  have z0 : t2.regs 0 = 0#32 := (fo 0 (by decide) (by decide)).trans (hz 0 (by decide))
  refine ⟨_, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · rw [hx, mem_movHi, fm, hm1, h5, clear_words]
  · intro r h4
    have h15 : r ≠ 15 := by rintro rfl; exact absurd h4 (by decide)
    have n12 : r ≠ 12 := by rintro rfl; exact absurd h4 (by decide)
    have n5 : r ≠ 5 := by rintro rfl; exact absurd h4 (by decide)
    rw [hx, hr r h15]
    simp only [upd, n12, if_false]
    exact (fo r h15 n5).trans (hz r (by omega))
  · rw [hx, hr 12 (by decide)]; simp [upd, z0]
  · intro r h15 h6 h12
    have n12 : r ≠ 12 := by rintro rfl; exact h12 rfl
    have n5 : r ≠ 5 := by rintro rfl; exact absurd h6 (by decide)
    rw [hx, hr r h15]
    simp only [upd, n12, if_false]
    exact (fo r h15 n5).trans (ho r h15 h6)

/-- The cleared locals do not reach the saved registers above them. -/
theorem rd_clear (m : Mem) (sp : Word) (hs : sp.toNat + COMPRESS_FRAME ≤ 2 ^ 32) (o : Nat)
    (h1 : LOCALS_BYTES ≤ o) (h2 : o + 4 ≤ COMPRESS_FRAME) :
    read32 (storeWords m sp (List.replicate LOCALS_WORDS 0#32)) (sp + BitVec.ofNat 32 o) =
      read32 m (sp + BitVec.ofNat 32 o) := by
  have e := M0Crypto.Release.Frame.toNat_add_ofNat sp o (by omega)
  refine read32_storeWords_ne m _ _ _ ⟨?_, ?_, ?_⟩ <;> (try simp only [List.length_replicate]) <;> omega

theorem mem_pop4f (s : State) : ((Instr.pop 0xF0 false).next s).mem = s.mem := by
  have key : ∀ (rs : List Reg) (a : Word) (t : State), (loadRegs t a rs).mem = t.mem := by
    intro rs; induction rs with
    | nil => intros; rfl
    | cons r rs ih => intro a t; simp [loadRegs, ih, State.setReg]
  simp [Instr.next, Instr.exec, key, State.setReg]

theorem RA_pop4f {s : State} {R : Reg → Word} (h : RA s R) :
    RA ((Instr.pop 0xF0 false).next s)
      (upd (upd (upd (upd (upd R 4 (read32 s.mem (R 13))) 5 (read32 s.mem (R 13 + 4#32))) 6
        (read32 s.mem (R 13 + 8#32))) 7 (read32 s.mem (R 13 + 12#32))) 13 (R 13 + 16#32)) := by
  have l : listRegs 0xF0#8 = [4, 5, 6, 7] := by decide
  have hb : bitCount 0xF0#8 = 4 := by decide
  have h13 := h 13 (by decide)
  intro r hr
  have e : ((Instr.pop 0xF0 false).next s).regs r =
      if r = 13 then s.regs 13 + 16#32 else if r = 4 then read32 s.mem (s.regs 13)
      else if r = 5 then read32 s.mem (s.regs 13 + 4#32)
      else if r = 6 then read32 s.mem (s.regs 13 + 8#32)
      else if r = 7 then read32 s.mem (s.regs 13 + 12#32) else s.regs r := by
    have e8 : s.regs 13 + 4#32 + 4#32 = s.regs 13 + 8#32 := by bv_omega
    have e12 : s.regs 13 + 8#32 + 4#32 = s.regs 13 + 12#32 := by bv_omega
    have e12b : s.regs 13 + 4#32 + 4#32 + 4#32 = s.regs 13 + 12#32 := by bv_omega
    simp (config := {decide := true}) [Instr.next, Instr.exec, l, hb, loadRegs, State.setReg, State.reg,
      State.sp, hr, LowReg.toReg]
    obtain ⟨rv, hrv⟩ := r
    simp (config := {decide := true}) only [Fin.ext_iff] at hr ⊢
    repeat' split
    all_goals first | rfl | (exfalso; omega) | exact congrArg (read32 s.mem) e8 | exact congrArg (read32 s.mem) e12b | exact congrArg (read32 s.mem) e12
  rw [e, h13]
  by_cases e13 : r = 13
  · subst e13; simp [upd, h13]
  · by_cases e4 : r = 4
    · subst e4; simp [upd, h13]
    · by_cases e5 : r = 5
      · subst e5; simp [upd, h13]
      · by_cases e6 : r = 6
        · subst e6; simp [upd, h13]
        · by_cases e7 : r = 7
          · subst e7; simp [upd, h13]
          · simp [upd, e13, e4, e5, e6, e7, h r hr]

def S4 : List Instr :=
  [ .addSp LOCALS_WORDS, .pop 0xF0 false, .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7 ]

theorem S4_eff {t : State} {R : Reg → Word} (h : RA t R) :
    ∃ R', RA (execAll S4 t) R' ∧ (execAll S4 t).mem = t.mem ∧
      R' 4 = read32 t.mem (R 13 + SAVED_0_W) ∧ R' 5 = read32 t.mem (R 13 + SAVED_1_W) ∧
      R' 6 = read32 t.mem (R 13 + SAVED_2_W) ∧ R' 7 = read32 t.mem (R 13 + SAVED_3_W) ∧
      R' 8 = read32 t.mem (R 13 + SAVED_0_W) ∧ R' 9 = read32 t.mem (R 13 + SAVED_1_W) ∧
      R' 10 = read32 t.mem (R 13 + SAVED_2_W) ∧ R' 11 = read32 t.mem (R 13 + SAVED_3_W) ∧
      R' 13 = R 13 + SAVED_4_W ∧
      (∀ r : Reg, r ≠ 15 → r.val < 4 ∨ r.val = 12 → R' r = R r) := by
  have a1 := RA_addSp h LOCALS_WORDS
  have a2 := RA_pop4f a1
  have a3 := RA_movHi a2 8 4 (by decide) (by decide)
  have a4 := RA_movHi a3 9 5 (by decide) (by decide)
  have a5 := RA_movHi a4 10 6 (by decide) (by decide)
  have a6 := RA_movHi a5 11 7 (by decide) (by decide)
  have hm : (execAll S4 t).mem = t.mem := by
    show ((Instr.movHi 11 7).next ((Instr.movHi 10 6).next ((Instr.movHi 9 5).next ((Instr.movHi 8 4).next
      ((Instr.pop 0xF0 false).next ((Instr.addSp LOCALS_WORDS).next t)))))).mem = _
    rw [mem_movHi, mem_movHi, mem_movHi, mem_movHi, mem_pop4f, mem_addSp]
  have e1 : R 13 + BitVec.ofNat 32 ((LOCALS_WORDS : BitVec 7).toNat * 4) = R 13 + SAVED_0_W := by bv_omega
  have e2 : R 13 + SAVED_0_W + 4#32 = R 13 + SAVED_1_W := by bv_omega
  have e3 : R 13 + SAVED_0_W + 8#32 = R 13 + SAVED_2_W := by bv_omega
  have e4 : R 13 + SAVED_0_W + 12#32 = R 13 + SAVED_3_W := by bv_omega
  have e5 : R 13 + SAVED_0_W + 16#32 = R 13 + SAVED_4_W := by bv_omega
  rw [mem_addSp] at a2
  refine ⟨_, (a6 : RA (execAll S4 t) _), hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (config := {decide := true}) [upd, mem_movHi, mem_addSp, mem_pop4f, e1, e2, e3, e4, e5]; done)
    | (simp (config := {decide := true}) [upd, mem_movHi, mem_addSp, mem_pop4f, e1, e2, e3, e4, e5]; rfl)
    | (intro r h15 hr
       obtain ⟨rv, hrv⟩ := r
       simp (config := {decide := true}) [upd, Fin.ext_iff] at h15 hr ⊢
       repeat' split
       all_goals first | rfl | (exfalso; omega))

def tailBody : List Instr := S1 ++ S2a ++ S2b ++ S3a ++ S3b ++ S3c ++ S4

theorem tail_split : tail = tailBody ++ [.pop 0xF0 true] := by decide

theorem S1_mem (t : State) : (execAll S1 t).mem = t.mem := execAll_mem S1 t (by decide)

theorem disj_frame (hp sp : Word) (dj : Disj hp 32 sp COMPRESS_FRAME) (n : Nat) (hn : n ≤ 32) (o : Nat)
    (ho : o + 4 ≤ COMPRESS_FRAME) : Disj hp n (sp + BitVec.ofNat 32 o) 4 := by
  obtain ⟨h1, h2, h3⟩ := dj
  have := M0Crypto.Release.Frame.toNat_add_ofNat sp o (by omega)
  refine ⟨by omega, by omega, by omega⟩

theorem disj_self (hp : Word) (h : hp.toNat + 32 ≤ 2 ^ 32) (n : Nat) (hn : n ≤ 16) (o : Nat) (ho : 16 ≤ o) (ho2 : o + 4 ≤ 32) :
    Disj hp n (hp + BitVec.ofNat 32 o) 4 := by
  have := M0Crypto.Release.Frame.toNat_add_ofNat hp o (by omega)
  refine ⟨by omega, by omega, by omega⟩

theorem rd_ne4 (m : Mem) (hp v0 v1 v2 v3 : Word) (h : hp.toNat + 32 ≤ 2 ^ 32) (o : Nat) (ho : 16 ≤ o)
    (ho2 : o + 4 ≤ 32) :
    read32 (storeWords m hp [v0, v1, v2, v3]) (hp + BitVec.ofNat 32 o) = read32 m (hp + BitVec.ofNat 32 o) :=
  read32_storeWords_ne m hp [v0, v1, v2, v3] _ (disj_self hp h _ (by simp) o ho ho2)

theorem rd_nesp (m : Mem) (hp sp v0 v1 v2 v3 : Word) (dj : Disj hp 32 sp COMPRESS_FRAME) (o : Nat) (ho : o + 4 ≤ COMPRESS_FRAME) :
    read32 (storeWords m hp [v0, v1, v2, v3]) (sp + BitVec.ofNat 32 o) = read32 m (sp + BitVec.ofNat 32 o) :=
  read32_storeWords_ne m hp [v0, v1, v2, v3] _ (disj_frame hp sp dj _ (by simp) o ho)

theorem rd_nesp2 (m : Mem) (hp sp v0 v1 v2 v3 : Word) (dj : Disj hp 32 sp COMPRESS_FRAME) (o : Nat)
    (ho : o + 4 ≤ COMPRESS_FRAME) :
    read32 (storeWords m (hp + 16#32) [v0, v1, v2, v3]) (sp + BitVec.ofNat 32 o) =
      read32 m (sp + BitVec.ofNat 32 o) := by
  obtain ⟨h1, h2, h3⟩ := dj
  have e1 := M0Crypto.Release.Frame.toNat_add_ofNat hp 16 (by omega)
  have e2 := M0Crypto.Release.Frame.toNat_add_ofNat sp o (by omega)
  refine read32_storeWords_ne m _ _ _ ⟨?_, ?_, ?_⟩ <;> (try simp only [List.length_cons, List.length_nil]) <;> omega

theorem x3 (a b c : BitVec 32) : a ^^^ (c ^^^ b) = a ^^^ b ^^^ c := by
  rw [BitVec.xor_assoc a b c, BitVec.xor_comm b c]

theorem tailBody_eff (t0 : State) (V : Nat → Word) (sp hp : Word)
    (h13 : t0.regs 13 = sp) (r0 : t0.regs 0 = V 2) (r2 : t0.regs 2 = V 8) (r5 : t0.regs 5 = V 9)
    (r6 : t0.regs 6 = V 10) (r7 : t0.regs 7 = V 11) (r8 : t0.regs 8 = V 0)
    (r9 : t0.regs 9 = V 12) (r10 : t0.regs 10 = V 13) (r11 : t0.regs 11 = V 14)
    (r12 : t0.regs 12 = V 15)
    (mV : ∀ i, 1 ≤ i → i < 8 → i ≠ 2 → read32 t0.mem (sp + BitVec.ofNat 32 (4 * i)) = V i)
    (hH : read32 t0.mem (sp + BitVec.ofNat 32 HPTR_SLOT) = hp)
    (dj : Disj hp 32 sp COMPRESS_FRAME) :
    ∃ R1, RA (execAll tailBody t0) R1 ∧
      (execAll tailBody t0).mem =
        storeWords (storeWords (storeWords t0.mem hp
          [read32 t0.mem hp ^^^ V 0 ^^^ V 8, read32 t0.mem (hp + 4#32) ^^^ V 1 ^^^ V 9,
           read32 t0.mem (hp + 8#32) ^^^ V 2 ^^^ V 10, read32 t0.mem (hp + 12#32) ^^^ V 3 ^^^ V 11])
          (hp + 16#32)
          [read32 t0.mem (hp + 16#32) ^^^ V 4 ^^^ V 12, read32 t0.mem (hp + 20#32) ^^^ V 5 ^^^ V 13,
           read32 t0.mem (hp + 24#32) ^^^ V 6 ^^^ V 14, read32 t0.mem (hp + 28#32) ^^^ V 7 ^^^ V 15])
          sp (List.replicate LOCALS_WORDS 0#32) ∧
      R1 13 = sp + SAVED_4_W ∧
      R1 8 = read32 t0.mem (sp + SAVED_0_W) ∧ R1 9 = read32 t0.mem (sp + SAVED_1_W) ∧
      R1 10 = read32 t0.mem (sp + SAVED_2_W) ∧ R1 11 = read32 t0.mem (sp + SAVED_3_W) ∧
      (∀ r : Reg, r.val < 4 → R1 r = 0#32) ∧ R1 12 = 0#32 := by
  have R0 : RA t0 t0.regs := fun _ _ => rfl
  obtain ⟨Ra, ha, a0, a1, a2, a3, a4, a5, a6, a7, ao⟩ := S1_eff R0
  obtain ⟨Rb, hb, bm, b1, b2, b3, b5, bo⟩ := S2a_eff ha
  obtain ⟨Rc, hc, cm, c0, c1, c2, c3, c4, co⟩ := S2b_eff hb
  obtain ⟨Rd, hd, dm, d0, d1, d2, d3, d4, d6, dO⟩ := S3a_eff hc
  obtain ⟨Re, he, em, e4, eo⟩ := S3b_eff hd
  obtain ⟨Rg, hg, gm, gz, g12, go⟩ := S3c_eff he
  obtain ⟨Rf, hf, fm, f4, f5, f6, f7, f8, f9, f10, f11, f13, fo⟩ := S4_eff hg
  have hj := dj
  obtain ⟨hj1, hj2, hj3⟩ := dj
  have m1 : read32 t0.mem (sp + BitVec.ofNat 32 4) = V 1 := mV 1 (by omega) (by omega) (by omega)
  have m3 : read32 t0.mem (sp + BitVec.ofNat 32 12) = V 3 := mV 3 (by omega) (by omega) (by omega)
  have m4 : read32 t0.mem (sp + BitVec.ofNat 32 16) = V 4 := mV 4 (by omega) (by omega) (by omega)
  have m5 : read32 t0.mem (sp + BitVec.ofNat 32 20) = V 5 := mV 5 (by omega) (by omega) (by omega)
  have m6 : read32 t0.mem (sp + BitVec.ofNat 32 24) = V 6 := mV 6 (by omega) (by omega) (by omega)
  have m7 : read32 t0.mem (sp + BitVec.ofNat 32 28) = V 7 := mV 7 (by omega) (by omega) (by omega)
  rw [h13] at a4 a5 a6 a7
  rw [S1_mem] at b1 b2 b3 b5 bm
  have hpA : Ra 4 = hp := by rw [a4, hH]
  have s13 : Ra 13 = sp := (ao 13 (by decide) (by decide)).trans h13
  have s9 : Ra 9 = V 12 := (ao 9 (by decide) (by decide)).trans r9
  have s10 : Ra 10 = V 13 := (ao 10 (by decide) (by decide)).trans r10
  have s11 : Ra 11 = V 14 := (ao 11 (by decide) (by decide)).trans r11
  have s12 : Ra 12 = V 15 := (ao 12 (by decide) (by decide)).trans r12
  have n0 : Rb 1 = read32 t0.mem hp ^^^ V 0 ^^^ V 8 := by
    rw [b1, hpA, a2, r2, r8]; exact x3 _ _ _
  have n1 : Rb 2 = read32 t0.mem (hp + 4#32) ^^^ V 1 ^^^ V 9 := by
    rw [b2, hpA, a5, r5, m1]; exact x3 _ _ _
  have n2 : Rb 3 = read32 t0.mem (hp + 8#32) ^^^ V 2 ^^^ V 10 := by
    rw [b3, hpA, a0, r0, r6]; exact (BitVec.xor_assoc _ _ _).symm
  have n3 : Rb 5 = read32 t0.mem (hp + 12#32) ^^^ V 3 ^^^ V 11 := by
    rw [b5, hpA, a7, r7, m3]; exact x3 _ _ _
  have hp4 : Rb 4 = hp := (bo 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpA
  have t13 : Rb 13 = sp := (bo 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s13
  have u13 : Rc 13 = sp := (co 13 (by decide) (by decide)).trans t13
  have u9 : Rc 9 = V 12 := (co 9 (by decide) (by decide)).trans
    ((bo 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s9)
  have u10 : Rc 10 = V 13 := (co 10 (by decide) (by decide)).trans
    ((bo 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s10)
  have u11 : Rc 11 = V 14 := (co 11 (by decide) (by decide)).trans
    ((bo 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s11)
  have u12 : Rc 12 = V 15 := (co 12 (by decide) (by decide)).trans
    ((bo 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s12)
  rw [bm, hp4, n0, n1, n2, n3] at cm
  rw [bm, hp4, n0, n1, n2, n3] at c0 c1 c2 c3
  have h16 : hp.toNat + 32 ≤ 2 ^ 32 := hj1
  rw [rd_ne4 _ hp _ _ _ _ h16 16 (by omega) (by omega)] at c0
  rw [show hp + 20#32 = hp + BitVec.ofNat 32 20 from rfl, rd_ne4 _ hp _ _ _ _ h16 20 (by omega) (by omega)] at c1
  rw [rd_ne4 _ hp _ _ _ _ h16 24 (by omega) (by omega)] at c2
  rw [rd_ne4 _ hp _ _ _ _ h16 28 (by omega) (by omega)] at c3
  rw [cm] at d0 d1 d2 d3
  rw [dm, cm] at em
  rw [u13] at d0 d1 d2 d3
  rw [rd_nesp _ hp sp _ _ _ _ hj 16 (by omega), m4, c0, u9] at d0
  rw [rd_nesp _ hp sp _ _ _ _ hj 20 (by omega), m5, c1, u10] at d1
  rw [rd_nesp _ hp sp _ _ _ _ hj 24 (by omega), m6, c2, u11] at d2
  rw [rd_nesp _ hp sp _ _ _ _ hj 28 (by omega), m7, c3, u12] at d3
  have d4' : Rd 4 = hp + 16#32 := by rw [d4, c4, hp4]; bv_omega
  rw [d4', d0, d1, d2, d3] at em
  have s13' : Re 13 = sp := (eo 13 (by decide) (by decide)).trans
    ((dO 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans u13)
  have g13 : Rg 13 = sp := (go 13 (by decide) (by decide) (by decide)).trans s13'
  rw [s13'] at gm
  rw [gm, g13] at f8 f9 f10 f11
  rw [rd_clear _ sp hj2 SAVED_0 (by omega) (by omega)] at f8
  rw [rd_clear _ sp hj2 SAVED_1 (by omega) (by omega)] at f9
  rw [rd_clear _ sp hj2 SAVED_2 (by omega) (by omega)] at f10
  rw [rd_clear _ sp hj2 SAVED_3 (by omega) (by omega)] at f11
  rw [em] at f8 f9 f10 f11 gm
  rw [rd_nesp2 _ hp sp _ _ _ _ hj SAVED_0 (by omega), rd_nesp _ hp sp _ _ _ _ hj SAVED_0 (by omega)] at f8
  rw [rd_nesp2 _ hp sp _ _ _ _ hj SAVED_1 (by omega), rd_nesp _ hp sp _ _ _ _ hj SAVED_1 (by omega)] at f9
  rw [rd_nesp2 _ hp sp _ _ _ _ hj SAVED_2 (by omega), rd_nesp _ hp sp _ _ _ _ hj SAVED_2 (by omega)] at f10
  rw [rd_nesp2 _ hp sp _ _ _ _ hj SAVED_3 (by omega), rd_nesp _ hp sp _ _ _ _ hj SAVED_3 (by omega)] at f11
  simp only [tailBody, execAll_append]
  refine ⟨Rf, hf, ?_, ?_, f8, f9, f10, f11, ?_, ?_⟩
  · rw [fm, gm]
  · rw [f13, g13]
  · intro r h4
    rw [fo r (by rintro rfl; exact absurd h4 (by decide)) (Or.inl h4)]; exact gz r h4
  · rw [fo 12 (by decide) (Or.inr rfl)]; exact g12

/-- Register facts of the intermediate tail states, for the alignment and write checks of the
stage blocks. -/
theorem tail_regs (t0 : State) (sp hp : Word)
    (h13 : t0.regs 13 = sp) (hH : read32 t0.mem (sp + BitVec.ofNat 32 HPTR_SLOT) = hp) :
    let t1 := execAll S1 t0
    let t2 := execAll S2a t1
    let t3 := execAll S2b t2
    let t4 := execAll S3a t3
    let t5 := execAll S3b t4
    let t6 := execAll S3c t5
    t1.regs 4 = hp ∧ t1.regs 13 = sp ∧ t2.regs 4 = hp ∧ t3.regs 13 = sp ∧
      t4.regs 4 = hp + 16#32 ∧ t4.regs 13 = sp ∧ t5.regs 13 = sp ∧ t6.regs 13 = sp := by
  intro t1 t2 t3 t4 t5 t6
  have R0 : RA t0 t0.regs := fun _ _ => rfl
  obtain ⟨Ra, ha, a0, a1, a2, a3, a4, a5, a6, a7, ao⟩ := S1_eff R0
  obtain ⟨Rb, hb, bm, b1, b2, b3, b5, bo⟩ := S2a_eff ha
  obtain ⟨Rc, hc, cm, c0, c1, c2, c3, c4, co⟩ := S2b_eff hb
  obtain ⟨Rd, hd, dm, d0, d1, d2, d3, d4, d6, dO⟩ := S3a_eff hc
  obtain ⟨Re, he, em, e4, eo⟩ := S3b_eff hd
  obtain ⟨Rg, hg, gm, gz, g12, go⟩ := S3c_eff he
  rw [h13] at a4
  have hpA : Ra 4 = hp := by rw [a4, hH]
  have s13 : Ra 13 = sp := (ao 13 (by decide) (by decide)).trans h13
  have hp4 : Rb 4 = hp := (bo 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpA
  have t13 : Rb 13 = sp := (bo 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s13
  have u13 : Rc 13 = sp := (co 13 (by decide) (by decide)).trans t13
  have d4' : Rd 4 = hp + 16#32 := by rw [d4, c4, hp4]; bv_omega
  have s13' : Re 13 = sp := (eo 13 (by decide) (by decide)).trans
    ((dO 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans u13)
  have d13 : Rd 13 = sp := dO 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans u13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha 4 (by decide)).trans hpA
  · exact (ha 13 (by decide)).trans s13
  · exact (hb 4 (by decide)).trans hp4
  · exact (hc 13 (by decide)).trans u13
  · exact (hd 4 (by decide)).trans d4'
  · exact (hd 13 (by decide)).trans d13
  · exact (he 13 (by decide)).trans s13'
  · exact (hg 13 (by decide)).trans ((go 13 (by decide) (by decide) (by decide)).trans s13')

end M0Crypto.Release.Blake2sTail
