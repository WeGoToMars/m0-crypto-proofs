import M0Crypto.Release.Blake2sRound
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace M0Crypto.Release.Blake2sPro

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCode
open M0Crypto.Release.Blake2s (toReg_ne15 regs_movHi regs_eors regs_ldrSp mem_movHi mem_ldrSp mem_dp mem_strSp regs_strSp)

theorem regs_push (s : State) (l : BitVec 8) (lr : Bool) (r : Reg) (hr : r ≠ 15) :
    ((Instr.push l lr).next s).regs r =
      if r = 13 then s.regs 13 - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem mem_push (s : State) (l : BitVec 8) (lr : Bool) :
    ((Instr.push l lr).next s).mem =
      storeWords s.mem (s.regs 13 - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)))
        ((listRegs l).map (fun x => s.regs x.toReg) ++ (if lr then [s.regs 14] else [])) := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, State.reg]

theorem regs_subSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subSp i).next s).regs r =
      if r = 13 then s.regs 13 - BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem mem_subSp (s : State) (i : BitVec 7) : ((Instr.subSp i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_addRdSp (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addRdSp d i).next s).regs r =
      if r = d.toReg then s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem mem_addRdSp (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.addRdSp d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_ldrLit (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldrLit t i).next s).regs r =
      if r = t.toReg then read32 s.mem (((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (i.toNat * 4))
      else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_ldrLit (s : State) (t : LowReg) (i : BitVec 8) : ((Instr.ldrLit t i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem regs_stm (s : State) (n : LowReg) (l : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.stm n l).next s).regs r =
      if r = n.toReg then s.reg n + BitVec.ofNat 32 (4 * bitCount l) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg, hr]

theorem mem_stm (s : State) (n : LowReg) (l : BitVec 8) :
    ((Instr.stm n l).next s).mem = storeWords s.mem (s.regs n.toReg) ((listRegs l).map (fun x => s.regs x.toReg)) := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg]

theorem mem_ldm (s : State) (n : LowReg) (l : BitVec 8) :
    ((Instr.ldm n l).next s).mem = s.mem := by
  have key : ∀ (rs : List Reg) (a : Word) (t : State), (loadRegs t a rs).mem = t.mem := by
    intro rs; induction rs with
    | nil => intros; rfl
    | cons r rs ih => intro a t; simp [loadRegs, ih, State.setReg]
  simp only [Instr.next, Instr.exec]
  split
  · rename_i x s1 heq
    split at heq <;> (injection heq with heq; subst heq; simp [key, State.setReg])
  · rfl

theorem regs_ldm4d (s : State) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldm 1 0x4d).next s).regs r =
      if r = 0 then read32 s.mem (s.regs 1)
      else if r = 2 then read32 s.mem (s.regs 1 + 4#32)
      else if r = 3 then read32 s.mem (s.regs 1 + 8#32)
      else if r = 6 then read32 s.mem (s.regs 1 + 12#32)
      else if r = 1 then s.regs 1 + 16#32 else s.regs r := by
  have h : listRegs 77#8 = [0, 2, 3, 6] := by decide
  have hb : bitCount 77#8 = 4 := by decide
  simp [Instr.next, Instr.exec, h, hb, loadRegs, State.setReg, State.reg, hr, LowReg.toReg]
  have e12 : s.regs 1 + 8#32 + 4#32 = s.regs 1 + 12#32 := by bv_omega
  have e8 : s.regs 1 + 4#32 + 4#32 = s.regs 1 + 8#32 := by bv_omega
  have e12b : s.regs 1 + 4#32 + 4#32 + 4#32 = s.regs 1 + 12#32 := by bv_omega
  simp only [e8, e12, e12b]
  obtain ⟨rv, hrv⟩ := r
  simp only [Fin.ext_iff] at hr ⊢
  simp (config := {decide := true}) only [Fin.val_zero] at hr ⊢
  repeat' split
  all_goals first | rfl | (exfalso; omega)
  done


def copy4 : List Instr := [.ldm 1 0x4d, .stm 4 0x4d]

theorem copy4_eff (s : State) :
    let t := execAll copy4 s
    let w0 := read32 s.mem (s.regs 1)
    let w1 := read32 s.mem (s.regs 1 + 4#32)
    let w2 := read32 s.mem (s.regs 1 + 8#32)
    let w3 := read32 s.mem (s.regs 1 + 12#32)
    (∀ r : Reg, r ≠ 15 → t.regs r =
      if r = 0 then w0 else if r = 2 then w1 else if r = 3 then w2 else if r = 6 then w3
      else if r = 1 then s.regs 1 + 16#32 else if r = 4 then s.regs 4 + 16#32 else s.regs r) ∧
    t.mem = storeWords s.mem (s.regs 4) [w0, w1, w2, w3] := by
  intro t w0 w1 w2 w3
  have hl : listRegs 77#8 = [0, 2, 3, 6] := by decide
  have hb : bitCount 77#8 = 4 := by decide
  have hb' : bitCount 77 = 4 := by decide
  have hl' : listRegs 77 = [0, 2, 3, 6] := by decide
  have e4 : (LowReg.toReg 4 : Reg) = 4 := rfl
  have a0 := regs_ldm4d s 0 (by decide)
  have a2 := regs_ldm4d s 2 (by decide)
  have a3 := regs_ldm4d s 3 (by decide)
  have a6 := regs_ldm4d s 6 (by decide)
  have a4 := regs_ldm4d s 4 (by decide)
  simp (config := {decide := true}) only [ite_true, ite_false] at a0 a2 a3 a4 a6
  constructor
  · intro r hr
    simp only [t, copy4, execAll]
    rw [regs_stm _ _ _ r hr, regs_ldm4d _ r hr]
    simp only [State.reg, hl, hb, a4, e4, hb']
    by_cases h4 : r = 4
    · subst h4; simp (config := {decide := true}) [a4]
    · simp [h4, w0, w1, w2, w3]
  · simp only [t, copy4, execAll]
    rw [mem_stm, mem_ldm]
    simp only [e4, a4, hl, hl', List.map_cons, List.map_nil]
    show storeWords s.mem (s.regs 4) [((Instr.ldm 1 77).next s).regs 0, ((Instr.ldm 1 77).next s).regs 2,
      ((Instr.ldm 1 77).next s).regs 3, ((Instr.ldm 1 77).next s).regs 6] = _
    rw [a0, a2, a3, a6]


/-! ## Frame bookkeeping -/

open M0Crypto.Release.Frame (read32_write32_slot' read32_congr ne_of_disj Disj)

/-- Known word contents of the frame slots `0..34`. -/
def FS (fp : Word) (F : Nat → Option Word) (m : Mem) : Prop :=
  ∀ k, k < FRAME_SLOTS → ∀ w, F k = some w → read32 m (slot fp k) = w

/-- `m` agrees with `m0` outside the 136 frame bytes. -/
def Out (fp : Word) (m0 m : Mem) : Prop :=
  ∀ y, (∀ o, o < COMPRESS_FRAME → y ≠ fp + BitVec.ofNat 32 o) → m y = m0 y

theorem slot_succ (fp : Word) (k : Nat) : slot fp k + 4#32 = slot fp (k + 1) := by
  simp only [slot]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem FS_write {fp : Word} {F : Nat → Option Word} {m : Mem} (k : Nat) (v : Word) (hk : k < FRAME_SLOTS)
    (h : FS fp F m) : FS fp (fun j => if j = k then some v else F j) (write32 m (slot fp k) v) := by
  intro j hj w hw
  rw [read32_write32_slot' _ _ _ _ _ (by omega) (by omega)]
  by_cases hjk : j = k
  · subst hjk; simp at hw ⊢; exact hw
  · simp [hjk] at hw
    rw [if_neg (fun e => hjk e.symm)]
    exact h j hj w hw

theorem Out_write {fp : Word} {m0 m : Mem} (k : Nat) (v : Word) (hk : k < SLOTW_9) (h : Out fp m0 m) :
    Out fp m0 (write32 m (slot fp k) v) := by
  intro y hy
  rw [M0Crypto.Armv6M.write32_other]
  · exact h y hy
  · intro q hq e
    exact hy (4 * k + q) (by omega) (by rw [e]; simp only [slot]; rw [BitVec.add_assoc, ← BitVec.ofNat_add])

theorem FS_stw {fp : Word} : ∀ (vs : List Word) (k : Nat) (F : Nat → Option Word) (m : Mem),
    k + vs.length ≤ SLOTW_9 → FS fp F m →
    FS fp (fun j => if k ≤ j ∧ j < k + vs.length then some (vs.getD (j - k) 0) else F j)
      (storeWords m (slot fp k) vs)
  | [], k, F, m, _, h => by
    have e : (fun j => if k ≤ j ∧ j < k + ([] : List Word).length then some (([] : List Word).getD (j - k) 0)
        else F j) = F := by
      funext j; simp; intro h1 h2; omega
    rw [e]; exact h
  | v :: vs, k, F, m, hl, h => by
    simp only [storeWords, slot_succ]
    have h1 := FS_write (fp := fp) k v (by simp at hl; omega) h
    have h2 := FS_stw vs (k + 1) _ _ (by simp at hl; omega) h1
    have e : (fun j => if k ≤ j ∧ j < k + (v :: vs).length then some ((v :: vs).getD (j - k) 0) else F j) =
        (fun j => if k + 1 ≤ j ∧ j < k + 1 + vs.length then some (vs.getD (j - (k + 1)) 0)
          else if j = k then some v else F j) := by
      funext j
      simp only [List.length_cons]
      by_cases hjk : j = k
      · subst hjk; simp; intro h; omega
      · by_cases hj : j < k
        · have a1 : ¬ (k ≤ j) := by omega
          have a2 : ¬ (k + 1 ≤ j) := by omega
          simp [a1, a2, hjk]
        · by_cases hj2 : j < k + 1 + vs.length
          · have a3 : k + 1 ≤ j := by omega
            have e : j - k = (j - (k + 1)) + 1 := by omega
            simp [hjk, a3, hj2, e, List.getD_cons_succ]
            omega
          · have a4 : ¬ (j < k + 1 + vs.length) := hj2
            simp [hjk, a4]
            omega
    rw [e]; exact h2

theorem Out_stw {fp : Word} {m0 : Mem} : ∀ (vs : List Word) (k : Nat) (m : Mem),
    k + vs.length ≤ SLOTW_9 → Out fp m0 m → Out fp m0 (storeWords m (slot fp k) vs)
  | [], k, m, _, h => by simpa [storeWords] using h
  | v :: vs, k, m, hl, h => by
    simp only [storeWords, slot_succ]
    exact Out_stw vs (k + 1) _ (by simp at hl; omega) (Out_write k v (by simp at hl; omega) h)


/-! ## Stages of the prologue -/

def pA : List Instr := [ .push 0xF0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11, .push 0xF0 false,
    .subSp LOCALS_WORDS, .strSp 0 HPTR_WORDS ]

theorem regs_strSp' (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.strSp t i).next s).regs r = s.regs r := Release.Blake2s.regs_strSp s t i r hr

theorem mem_strSp' (s : State) (t : LowReg) (i : BitVec 8) :
    ((Instr.strSp t i).next s).mem = write32 s.mem (s.regs 13 + BitVec.ofNat 32 (i.toNat * 4)) (s.regs t.toReg) :=
  Release.Blake2s.mem_strSp s t i

theorem reg_cases (P : Reg → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13)
    (h14 : P 14) : ∀ r : Reg, r ≠ 15 → P r := by
  intro r hr
  obtain ⟨rv, hrv⟩ := r
  have hr' : rv ≠ 15 := fun h => hr (by subst h; rfl)
  rcases (by omega : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 ∨ rv = 8 ∨
    rv = 9 ∨ rv = 10 ∨ rv = 11 ∨ rv = 12 ∨ rv = 13 ∨ rv = 14) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> assumption

theorem pA_regs : ∀ (s : State) (r : Reg), r ≠ 15 →
    (execAll pA s).regs r =
      if r = 13 then s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME else if r = 4 then s.regs 8 else if r = 5 then s.regs 9
      else if r = 6 then s.regs 10 else if r = 7 then s.regs 11 else s.regs r := by
  intro s
  have hb : bitCount 0xF0 = 4 := by decide
  have n13 : (13 : Reg) ≠ 15 := by decide
  have n8 : (8 : Reg) ≠ 15 := by decide
  have n9 : (9 : Reg) ≠ 15 := by decide
  have n10 : (10 : Reg) ≠ 15 := by decide
  have n11 : (11 : Reg) ≠ 15 := by decide
  refine reg_cases _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp only [pA, execAll]
    simp (config := {decide := true}) only [regs_strSp', regs_subSp, regs_push, regs_movHi, hb, n13, n8, n9, n10, n11, ne_eq, not_false_eq_true, ite_true, ite_false]
    try (simp [Bool.toNat]; bv_omega)

theorem pA_mem (s : State) :
    (execAll pA s).mem = write32 (storeWords (storeWords s.mem (s.regs 13 - BitVec.ofNat 32 20)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]) (s.regs 13 - BitVec.ofNat 32 36)
      [s.regs 8, s.regs 9, s.regs 10, s.regs 11]) (s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME + BitVec.ofNat 32 HPTR_SLOT) (s.regs 0) := by
  have hl : listRegs 0xF0 = [4, 5, 6, 7] := by decide
  have hb : bitCount 0xF0 = 4 := by decide
  have n13 : (13 : Reg) ≠ 15 := by decide
  have n8 : (8 : Reg) ≠ 15 := by decide
  have n9 : (9 : Reg) ≠ 15 := by decide
  have n10 : (10 : Reg) ≠ 15 := by decide
  have n11 : (11 : Reg) ≠ 15 := by decide
  have n14 : (14 : Reg) ≠ 15 := by decide
  have n4 : (4 : Reg) ≠ 15 := by decide
  have n5 : (5 : Reg) ≠ 15 := by decide
  have n6 : (6 : Reg) ≠ 15 := by decide
  have n7 : (7 : Reg) ≠ 15 := by decide
  have n0 : (0 : Reg) ≠ 15 := by decide
  simp only [pA, execAll]
  simp (config := {decide := true}) only [mem_strSp', mem_subSp, mem_push, mem_movHi, regs_strSp', regs_subSp, regs_push, regs_movHi, hl, hb, n13, n8, n9, n10, n11, n14, n4, n5, n6, n7, n0, ne_eq, not_false_eq_true, ite_true, ite_false, List.map_cons, List.map_nil, List.cons_append, List.nil_append, LowReg.toReg]
  have A : s.regs 13 - BitVec.ofNat 32 (4 * (4 + true.toNat)) - BitVec.ofNat 32 (4 * (4 + false.toNat)) -
      BitVec.ofNat 32 ((LOCALS_WORDS : BitVec 7).toNat * 4) + BitVec.ofNat 32 ((HPTR_WORDS : BitVec 8).toNat * 4) =
      s.regs 13 - COMPRESS_FRAME_W + HPTR_SLOT_W := by simp [Bool.toNat]; bv_omega
  have B : s.regs 13 - BitVec.ofNat 32 (4 * (4 + true.toNat)) - BitVec.ofNat 32 (4 * (4 + false.toNat)) =
      s.regs 13 - 36#32 := by simp [Bool.toNat]; bv_omega
  have C : s.regs 13 - BitVec.ofNat 32 (4 * (4 + true.toNat)) = s.regs 13 - 20#32 := by
    simp [Bool.toNat] <;> bv_omega
  rw [A, B, C]
  rfl

/-! ## Register-map calculus -/

def upd (R : Reg → Word) (d : Reg) (v : Word) : Reg → Word := fun r => if r = d then v else R r

/-- The register file of `t` (away from the PC) is the map `R`. -/
def RA (t : State) (R : Reg → Word) : Prop := ∀ r : Reg, r ≠ 15 → t.regs r = R r

theorem RA_movHi {s : State} {R : Reg → Word} (h : RA s R) (d m : Reg) (hd : d ≠ 15) (hm : m ≠ 15) :
    RA ((Instr.movHi d m).next s) (upd R d (R m)) := by
  intro r hr
  rw [regs_movHi _ _ _ _ hr]
  by_cases e : r = d
  · subst e; simp [upd, h m hm]
  · simp [upd, e, h r hr]

theorem RA_eors {s : State} {R : Reg → Word} (h : RA s R) (d m : LowReg) :
    RA ((Instr.dp .eors d m).next s) (upd R d.toReg (R d.toReg ^^^ R m.toReg)) := by
  intro r hr
  rw [regs_eors _ _ _ _ hr]
  by_cases e : r = d.toReg
  · subst e; simp [upd, State.reg, h _ (toReg_ne15 d), h _ (toReg_ne15 m)]
  · simp [upd, e, h r hr]

theorem RA_ldrLit {s : State} {R : Reg → Word} (h : RA s R) (t : LowReg) (i : BitVec 8) (a : Word)
    (ha : ((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (i.toNat * 4) = a) :
    RA ((Instr.ldrLit t i).next s) (upd R t.toReg (read32 s.mem a)) := by
  intro r hr
  rw [regs_ldrLit _ _ _ _ hr, ha]
  by_cases e : r = t.toReg
  · subst e; simp [upd]
  · simp [upd, e, h r hr]

theorem RA_ldrSp {s : State} {R : Reg → Word} (h : RA s R) (t : LowReg) (i : BitVec 8) :
    RA ((Instr.ldrSp t i).next s)
      (upd R t.toReg (read32 s.mem (R 13 + BitVec.ofNat 32 (i.toNat * 4)))) := by
  intro r hr
  rw [regs_ldrSp _ _ _ _ hr]
  have h13 := h 13 (by decide)
  by_cases e : r = t.toReg
  · subst e; simp [upd, State.sp, h13]
  · simp [upd, e, h r hr, State.sp, h13]

theorem RA_addRdSp {s : State} {R : Reg → Word} (h : RA s R) (d : LowReg) (i : BitVec 8) :
    RA ((Instr.addRdSp d i).next s) (upd R d.toReg (R 13 + BitVec.ofNat 32 (i.toNat * 4))) := by
  intro r hr
  rw [regs_addRdSp _ _ _ _ hr]
  have h13 := h 13 (by decide)
  by_cases e : r = d.toReg
  · subst e; simp [upd, h13]
  · simp [upd, e, h r hr]

theorem RA_copy4 {s : State} {R : Reg → Word} (h : RA s R) :
    RA (execAll copy4 s)
      (upd (upd (upd (upd (upd (upd R 0
        (read32 s.mem (R 1))) 2 (read32 s.mem (R 1 + 4#32))) 3 (read32 s.mem (R 1 + 8#32)))
        6 (read32 s.mem (R 1 + 12#32))) 1 (R 1 + 16#32)) 4 (R 4 + 16#32)) := by
  intro r hr
  obtain ⟨hreg, _⟩ := copy4_eff s
  rw [hreg r hr]
  have h1 := h 1 (by decide)
  have h4 := h 4 (by decide)
  by_cases e0 : r = 0
  · subst e0; simp [upd, h1]
  · by_cases e2 : r = 2
    · subst e2; simp [upd, h1]
    · by_cases e3 : r = 3
      · subst e3; simp [upd, h1]
      · by_cases e6 : r = 6
        · subst e6; simp [upd, h1]
        · by_cases e1 : r = 1
          · subst e1; simp [upd, h1]
          · by_cases e4 : r = 4
            · subst e4; simp [upd, h4, e0]
            · simp [upd, e0, e2, e3, e6, e1, e4, h r hr]

theorem RA_ldm4d {s : State} {R : Reg → Word} (h : RA s R) :
    RA ((Instr.ldm 1 0x4d).next s)
      (upd (upd (upd (upd (upd R 0 (read32 s.mem (R 1))) 2 (read32 s.mem (R 1 + 4#32))) 3
        (read32 s.mem (R 1 + 8#32))) 6 (read32 s.mem (R 1 + 12#32))) 1 (R 1 + 16#32)) := by
  intro r hr
  rw [regs_ldm4d _ _ hr]
  have h1 := h 1 (by decide)
  by_cases e0 : r = 0
  · subst e0; simp [upd, h1]
  · by_cases e2 : r = 2
    · subst e2; simp [upd, h1]
    · by_cases e3 : r = 3
      · subst e3; simp [upd, h1]
      · by_cases e6 : r = 6
        · subst e6; simp [upd, h1]
        · by_cases e1 : r = 1
          · subst e1; simp [upd, h1]
          · simp [upd, e0, e2, e3, e6, e1, h r hr]

theorem regs_stm4c (s : State) (r : Reg) (hr : r ≠ 15) :
    ((Instr.stm 4 0x4c).next s).regs r = if r = 4 then s.regs 4 + 12#32 else s.regs r := by
  have hb : bitCount 76#8 = 3 := by decide
  rw [regs_stm _ _ _ r hr]
  simp [State.reg, hb, LowReg.toReg]
  <;> rfl

theorem RA_stm4c {s : State} {R : Reg → Word} (h : RA s R) :
    RA ((Instr.stm 4 0x4c).next s) (upd R 4 (R 4 + 12#32)) := by
  intro r hr
  rw [regs_stm4c _ _ hr]
  by_cases e : r = 4
  · subst e; simp [upd, h 4 (by decide)]
  · simp [upd, e, h r hr]

theorem out_read {fp : Word} {m0 m : Mem} (h : Out fp m0 m) (a : Word) (hd : Disj a 4 fp COMPRESS_FRAME) :
    read32 m a = read32 m0 a := by
  apply read32_congr
  intro k hk
  exact h _ (fun o ho => ne_of_disj hd.1 hd.2.1 hd.2.2 hk ho)

/-- Joint invariant: registers, known frame words, and memory outside the frame unchanged. -/
def JI (fp : Word) (s0 t : State) (R : Reg → Word) (F : Nat → Option Word) : Prop :=
  RA t R ∧ FS fp F t.mem ∧ Out fp s0.mem t.mem

theorem J_pure {fp : Word} {s0 t t' : State} {R R' : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (hm : t'.mem = t.mem) (hR : RA t' R') : JI fp s0 t' R' F := by
  refine ⟨hR, ?_, ?_⟩ <;> rw [hm]
  · exact h.2.1
  · exact h.2.2

theorem J_copy4 {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word} (k : Nat)
    (h : JI fp s0 t R F) (hk : k + 4 ≤ SLOTW_9) (h4 : R 4 = slot fp k)
    (d0 : Disj (R 1) 4 fp COMPRESS_FRAME) (d1 : Disj (R 1 + 4#32) 4 fp COMPRESS_FRAME) (d2 : Disj (R 1 + 8#32) 4 fp COMPRESS_FRAME)
    (d3 : Disj (R 1 + 12#32) 4 fp COMPRESS_FRAME) :
    JI fp s0 (execAll copy4 t)
      (upd (upd (upd (upd (upd (upd R 0 (read32 s0.mem (R 1))) 2 (read32 s0.mem (R 1 + 4#32))) 3
        (read32 s0.mem (R 1 + 8#32))) 6 (read32 s0.mem (R 1 + 12#32))) 1 (R 1 + 16#32)) 4 (R 4 + 16#32))
      (fun j => if k ≤ j ∧ j < k + 4 then
        some ([read32 s0.mem (R 1), read32 s0.mem (R 1 + 4#32), read32 s0.mem (R 1 + 8#32),
          read32 s0.mem (R 1 + 12#32)].getD (j - k) 0) else F j) := by
  obtain ⟨hRA, hFS, hOut⟩ := h
  have e0 := out_read hOut _ d0
  have e1 := out_read hOut _ d1
  have e2 := out_read hOut _ d2
  have e3 := out_read hOut _ d3
  have ra := RA_copy4 hRA
  rw [e0, e1, e2, e3] at ra
  refine ⟨ra, ?_, ?_⟩
  · obtain ⟨_, hm⟩ := copy4_eff t
    rw [hm, hRA 4 (by decide), hRA 1 (by decide), h4, e0, e1, e2, e3]
    exact FS_stw [read32 s0.mem (R 1), read32 s0.mem (R 1 + 4#32), read32 s0.mem (R 1 + 8#32),
      read32 s0.mem (R 1 + 12#32)] k F t.mem (by simpa using hk) hFS
  · obtain ⟨_, hm⟩ := copy4_eff t
    rw [hm, hRA 4 (by decide), h4]
    exact Out_stw _ k t.mem (by simpa using hk) hOut

theorem J_copy4' {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word} (k : Nat)
    (h : JI fp s0 t R F) (hk : k + 4 ≤ SLOTW_9) (h4 : R 4 = slot fp k) (a : Word) (ha : R 1 = a)
    (d0 : Disj a 4 fp COMPRESS_FRAME) (d1 : Disj (a + 4#32) 4 fp COMPRESS_FRAME) (d2 : Disj (a + 8#32) 4 fp COMPRESS_FRAME)
    (d3 : Disj (a + 12#32) 4 fp COMPRESS_FRAME) :
    JI fp s0 (execAll copy4 t)
      (upd (upd (upd (upd (upd (upd R 0 (read32 s0.mem a)) 2 (read32 s0.mem (a + 4#32))) 3
        (read32 s0.mem (a + 8#32))) 6 (read32 s0.mem (a + 12#32))) 1 (a + 16#32)) 4 (R 4 + 16#32))
      (fun j => if k ≤ j ∧ j < k + 4 then
        some ([read32 s0.mem a, read32 s0.mem (a + 4#32), read32 s0.mem (a + 8#32),
          read32 s0.mem (a + 12#32)].getD (j - k) 0) else F j) := by
  subst ha
  exact J_copy4 k h hk h4 d0 d1 d2 d3

/-- Frame words known after `pA`. -/
def FA (R0 : Reg → Word) (f0 : Word) : Nat → Option Word := fun j =>
  if j = HPTR_WORDS then some (R0 0)
  else if SLOTW_0 ≤ j ∧ j < SLOTW_4 then some ([R0 8, R0 9, R0 10, R0 11].getD (j - SLOTW_0) 0)
  else if SLOTW_4 ≤ j ∧ j < SLOTW_9 then some ([R0 4, R0 5, R0 6, R0 7, R0 14].getD (j - SLOTW_4) 0)
  else if j = SLOTW_9 then some f0 else none

def RpA (R0 : Reg → Word) : Reg → Word := fun r =>
  if r = 13 then R0 13 - BitVec.ofNat 32 COMPRESS_FRAME else if r = 4 then R0 8 else if r = 5 then R0 9
  else if r = 6 then R0 10 else if r = 7 then R0 11 else R0 r

theorem J_pA (s : State) (R0 : Reg → Word) (f0 : Word) (hs : RA s R0) (hf0 : read32 s.mem (R0 13) = f0) :
    JI (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) s (execAll pA s) (RpA R0) (FA R0 f0) := by
  have hra : RA (execAll pA s) (RpA R0) := by
    intro r hr
    rw [pA_regs s r hr]
    simp only [RpA]
    have h13 := hs 13 (by decide)
    have h8 := hs 8 (by decide); have h9 := hs 9 (by decide); have h10 := hs 10 (by decide)
    have h11 := hs 11 (by decide); have hr' := hs r hr
    simp only [h13, h8, h9, h10, h11, hr']
  refine ⟨hra, ?_, ?_⟩
  · generalize hfp : R0 13 - BitVec.ofNat 32 COMPRESS_FRAME = fp
    rw [pA_mem]
    have h13 := hs 13 (by decide)
    have a29 : s.regs 13 - BitVec.ofNat 32 20 = slot fp SLOTW_4 := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    have a25 : s.regs 13 - BitVec.ofNat 32 36 = slot fp SLOTW_0 := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    have a24 : s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME + BitVec.ofNat 32 HPTR_SLOT = slot fp HPTR_WORDS := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    rw [a29, a25, a24]
    have F0 : FS fp (fun j => if j = SLOTW_9 then some f0 else none) s.mem := by
      intro k hk w hw
      by_cases e : k = SLOTW_9
      · subst e; simp at hw; subst hw
        have : slot fp SLOTW_9 = R0 13 := by simp only [slot, ← hfp] <;> bv_omega
        rw [this]; exact hf0
      · simp [e] at hw
    have F1 := FS_stw [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] SLOTW_4 _ s.mem (by simp) F0
    have F2 := FS_stw [s.regs 8, s.regs 9, s.regs 10, s.regs 11] SLOTW_0 _ _ (by simp) F1
    have F3 := FS_write HPTR_WORDS (s.regs 0) (by omega) F2
    intro k hk w hw
    apply F3 k hk w
    rw [← hw]
    simp only [FA, hs 0 (by decide), hs 4 (by decide), hs 5 (by decide), hs 6 (by decide),
      hs 7 (by decide), hs 8 (by decide), hs 9 (by decide), hs 10 (by decide), hs 11 (by decide),
      hs 14 (by decide)]
    simp only [List.length_cons, List.length_nil]
  · generalize hfp : R0 13 - BitVec.ofNat 32 COMPRESS_FRAME = fp
    rw [pA_mem]
    have h13 := hs 13 (by decide)
    have a29 : s.regs 13 - BitVec.ofNat 32 20 = slot fp SLOTW_4 := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    have a25 : s.regs 13 - BitVec.ofNat 32 36 = slot fp SLOTW_0 := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    have a24 : s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME + BitVec.ofNat 32 HPTR_SLOT = slot fp HPTR_WORDS := by
      simp only [slot, ← hfp, h13] <;> bv_omega
    rw [a29, a25, a24]
    have O0 : Out fp s.mem s.mem := fun _ _ => rfl
    exact Out_write HPTR_WORDS _ (by omega) (Out_stw _ SLOTW_0 _ (by simp) (Out_stw _ SLOTW_4 _ (by simp) O0))

theorem J_movHi {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (d m : Reg) (hd : d ≠ 15) (hm : m ≠ 15) :
    JI fp s0 ((Instr.movHi d m).next t) (upd R d (R m)) F :=
  J_pure h (mem_movHi _ _ _) (RA_movHi h.1 d m hd hm)

theorem J_eors {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (d m : LowReg) :
    JI fp s0 ((Instr.dp .eors d m).next t) (upd R d.toReg (R d.toReg ^^^ R m.toReg)) F :=
  J_pure h (Release.Blake2s.mem_dp _ _ _ _ (Or.inl rfl)) (RA_eors h.1 d m)

theorem J_addRdSp {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (d : LowReg) (i : BitVec 8) :
    JI fp s0 ((Instr.addRdSp d i).next t) (upd R d.toReg (R 13 + BitVec.ofNat 32 (i.toNat * 4))) F :=
  J_pure h (mem_addRdSp _ _ _) (RA_addRdSp h.1 d i)

theorem J_ldrLit {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (d : LowReg) (i : BitVec 8) (a : Word)
    (ha : ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (i.toNat * 4) = a) (hd : Disj a 4 fp COMPRESS_FRAME) :
    JI fp s0 ((Instr.ldrLit d i).next t) (upd R d.toReg (read32 s0.mem a)) F := by
  have := RA_ldrLit h.1 d i a ha
  rw [out_read h.2.2 a hd] at this
  exact J_pure h (mem_ldrLit _ _ _) this

theorem J_ldrSp {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (d : LowReg) (i : BitVec 8) (k : Nat) (hk : k < FRAME_SLOTS) (w : Word)
    (hF : F k = some w) (hs : R 13 + BitVec.ofNat 32 (i.toNat * 4) = slot fp k) :
    JI fp s0 ((Instr.ldrSp d i).next t) (upd R d.toReg w) F := by
  have := RA_ldrSp h.1 d i
  rw [hs, h.2.1 k hk w hF] at this
  exact J_pure h (mem_ldrSp _ _ _) this

theorem J_ldm4d {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F)
    (d0 : Disj (R 1) 4 fp COMPRESS_FRAME) (d1 : Disj (R 1 + 4#32) 4 fp COMPRESS_FRAME) (d2 : Disj (R 1 + 8#32) 4 fp COMPRESS_FRAME)
    (d3 : Disj (R 1 + 12#32) 4 fp COMPRESS_FRAME) :
    JI fp s0 ((Instr.ldm 1 0x4d).next t)
      (upd (upd (upd (upd (upd R 0 (read32 s0.mem (R 1))) 2 (read32 s0.mem (R 1 + 4#32))) 3
        (read32 s0.mem (R 1 + 8#32))) 6 (read32 s0.mem (R 1 + 12#32))) 1 (R 1 + 16#32)) F := by
  have := RA_ldm4d h.1
  rw [out_read h.2.2 _ d0, out_read h.2.2 _ d1, out_read h.2.2 _ d2, out_read h.2.2 _ d3] at this
  exact J_pure h (mem_ldm _ _ _) this

theorem J_ldm4d' {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (a : Word) (ha : R 1 = a)
    (d0 : Disj a 4 fp COMPRESS_FRAME) (d1 : Disj (a + 4#32) 4 fp COMPRESS_FRAME) (d2 : Disj (a + 8#32) 4 fp COMPRESS_FRAME)
    (d3 : Disj (a + 12#32) 4 fp COMPRESS_FRAME) :
    JI fp s0 ((Instr.ldm 1 0x4d).next t)
      (upd (upd (upd (upd (upd R 0 (read32 s0.mem a)) 2 (read32 s0.mem (a + 4#32))) 3
        (read32 s0.mem (a + 8#32))) 6 (read32 s0.mem (a + 12#32))) 1 (a + 16#32)) F := by
  subst ha
  exact J_ldm4d h d0 d1 d2 d3

theorem mem_stm4c (s : State) :
    ((Instr.stm 4 0x4c).next s).mem = storeWords s.mem (s.regs 4) [s.regs 2, s.regs 3, s.regs 6] := by
  rw [mem_stm]
  have hl' : listRegs 76#8 = [2, 3, 6] := by decide
  simp [hl', LowReg.toReg]
  rfl

theorem J_stm4c {fp : Word} {s0 t : State} {R : Reg → Word} {F : Nat → Option Word} (k : Nat)
    (h : JI fp s0 t R F) (hk : k + 3 ≤ SLOTW_9) (h4 : R 4 = slot fp k) :
    JI fp s0 ((Instr.stm 4 0x4c).next t) (upd R 4 (R 4 + 12#32))
      (fun j => if k ≤ j ∧ j < k + 3 then some ([R 2, R 3, R 6].getD (j - k) 0) else F j) := by
  obtain ⟨hRA, hFS, hOut⟩ := h
  have e2 := hRA 2 (by decide); have e3 := hRA 3 (by decide); have e6 := hRA 6 (by decide)
  have e4 := hRA 4 (by decide)
  have key : ((Instr.stm 4 0x4c).next t).mem = storeWords t.mem (slot fp k) [R 2, R 3, R 6] := by
    rw [mem_stm4c, e4, e2, e3, e6, h4]
  refine ⟨RA_stm4c hRA, ?_, ?_⟩
  · rw [key]
    exact FS_stw [R 2, R 3, R 6] k F t.mem (by simpa using hk) hFS
  · rw [key]
    exact Out_stw _ k t.mem (by simpa using hk) hOut

abbrev preI : List Instr := Blake2sCode.pre

theorem preI_take_succ (s : State) (n : Nat) (i : Instr) (h : preI.take (n + 1) = preI.take n ++ [i]) :
    execAll (preI.take (n + 1)) s = i.next (execAll (preI.take n) s) := by
  rw [h, execAll_append]; rfl

theorem preI_take_copy (s : State) (n : Nat) (h : preI.take (n + 2) = preI.take n ++ copy4) :
    execAll (preI.take (n + 2)) s = execAll copy4 (execAll (preI.take n) s) := by
  rw [h, execAll_append]

theorem preI_pc (s : State) (n : Nat) (hf : (preI.take n).all Instr.falls = true) (hz : seqSize (preI.take n) = 2 * n) :
    (execAll (preI.take n) s).pc = s.pc + BitVec.ofNat 32 (2 * n) := by
  rw [execAll_pc _ _ hf, hz]

theorem JI_of_eq {fp : Word} {s0 t t' : State} {R : Reg → Word} {F : Nat → Option Word}
    (h : JI fp s0 t R F) (e : t = t') : JI fp s0 t' R F := e ▸ h

theorem disjAdd {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) (c : Nat) (hc : c + 4 ≤ n)
    (x : Word) (hx : x = a + BitVec.ofNat 32 c) : Disj x 4 b m := by
  obtain ⟨h1, h2, h3⟩ := h
  have : x.toNat = a.toNat + c := by
    rw [hx]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by omega, h2, ?_⟩
  omega

example (s : State) : execAll (preI.take 9) s = (Instr.ldrLit 0 20).next (execAll (preI.take 8) s) :=
  preI_take_succ s 8 _ (by decide)
example (s : State) : execAll (preI.take 23) s = execAll copy4 (execAll (preI.take 21) s) :=
  preI_take_copy s 21 (by decide)
example (s : State) : (execAll (preI.take 8) s).pc = s.pc + BitVec.ofNat 32 16 :=
  preI_pc s 8 (by decide) (by decide)
theorem pA_take : preI.take 8 = pA := by decide

macro "rsimp" : tactic => `(tactic| simp (config := {decide := true}) [upd, RpA, slot, LowReg.toReg])

/-- What the prologue leaves in the register file and frame map (named, so that the consumers
never see the run). -/
def PreRF (s : State) (R0 : Reg → Word) (f0 : Word) (A0 A1 A2 A3 A4 A5 A6 A7 : Word)
    (R : Reg → Word) (F : Nat → Option Word) : Prop :=
  R 13 = R0 13 - BitVec.ofNat 32 COMPRESS_FRAME ∧ R 8 = read32 s.mem (R0 0) ∧
  R 2 = read32 s.mem A0 ∧ R 5 = read32 s.mem A1 ∧ R 6 = read32 s.mem A2 ∧ R 7 = read32 s.mem A3 ∧
  R 9 = read32 s.mem A4 ^^^ R0 2 ∧ R 10 = read32 s.mem A5 ^^^ R0 3 ∧
  R 11 = read32 s.mem A6 ^^^ f0 ∧ R 12 = read32 s.mem A7 ∧
  (∀ i, 1 ≤ i → i < 8 → F i = some (read32 s.mem (R0 0 + BitVec.ofNat 32 (4 * i)))) ∧
  (∀ i, i < 16 → F (8 + i) = some (read32 s.mem (R0 1 + BitVec.ofNat 32 (4 * i)))) ∧
  F HPTR_WORDS = some (R0 0) ∧ F SLOTW_9 = some f0 ∧
  F SLOTW_0 = some (R0 8) ∧ F SLOTW_1 = some (R0 9) ∧ F SLOTW_2 = some (R0 10) ∧ F SLOTW_3 = some (R0 11) ∧
  F SLOTW_4 = some (R0 4) ∧ F SLOTW_5 = some (R0 5) ∧ F SLOTW_6 = some (R0 6) ∧ F SLOTW_7 = some (R0 7) ∧
  F SLOTW_8 = some (R0 14)

-- Reason: the 40-instruction prologue is one unrolled chain; the default 200000 times out
-- (measured 2026-11-11: whnf timeout at the final rewrite).
set_option maxHeartbeats 1000000 in
theorem J_pre (s : State) (R0 : Reg → Word) (f0 : Word) (hs : RA s R0)
    (hf0 : read32 s.mem (R0 13) = f0) (P : Word) (hpc : s.pc = P)
    (A0 A1 A2 A3 A4 A5 A6 A7 : Word)
    (l36 : ((P + BitVec.ofNat 32 72 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((2 : BitVec 8).toNat * 4) = A0)
    (l37 : ((P + BitVec.ofNat 32 74 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((3 : BitVec 8).toNat * 4) = A1)
    (l38 : ((P + BitVec.ofNat 32 76 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((3 : BitVec 8).toNat * 4) = A2)
    (l39 : ((P + BitVec.ofNat 32 78 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((4 : BitVec 8).toNat * 4) = A3)
    (l8 : ((P + BitVec.ofNat 32 16 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((20 : BitVec 8).toNat * 4) = A4)
    (l11 : ((P + BitVec.ofNat 32 22 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((20 : BitVec 8).toNat * 4) = A5)
    (l15 : ((P + BitVec.ofNat 32 30 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((19 : BitVec 8).toNat * 4) = A6)
    (l18 : ((P + BitVec.ofNat 32 36 + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((18 : BitVec 8).toNat * 4) = A7)
    (dA0 : Disj A0 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME) (dA1 : Disj A1 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME)
    (dA2 : Disj A2 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME) (dA3 : Disj A3 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME)
    (dA4 : Disj A4 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME) (dA5 : Disj A5 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME)
    (dA6 : Disj A6 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME) (dA7 : Disj A7 4 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME)
    (hbk : Disj (R0 1) 64 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME)
    (hhp : Disj (R0 0) 32 (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) COMPRESS_FRAME) :
    ∃ R F, JI (R0 13 - BitVec.ofNat 32 COMPRESS_FRAME) s (execAll preI s) R F ∧ PreRF s R0 f0 A0 A1 A2 A3 A4 A5 A6 A7 R F := by
  have j8 := J_pA s R0 f0 hs hf0
  rw [← pA_take] at j8
  have j9 := JI_of_eq (J_ldrLit j8 0 20 A4 (by rw [preI_pc s 8 (by decide) (by decide), hpc]; exact l8) dA4)
    (preI_take_succ s 8 _ (by decide)).symm
  have j10 := JI_of_eq (J_eors j9 0 2)
    (preI_take_succ s 9 _ (by decide)).symm
  have j11 := JI_of_eq (J_movHi j10 9 0 (by decide) (by decide))
    (preI_take_succ s 10 _ (by decide)).symm
  have j12 := JI_of_eq (J_ldrLit j11 5 20 A5 (by rw [preI_pc s 11 (by decide) (by decide), hpc]; exact l11) dA5)
    (preI_take_succ s 11 _ (by decide)).symm
  have j13 := JI_of_eq (J_eors j12 5 3)
    (preI_take_succ s 12 _ (by decide)).symm
  have j14 := JI_of_eq (J_movHi j13 10 5 (by decide) (by decide))
    (preI_take_succ s 13 _ (by decide)).symm
  have j15 := JI_of_eq (J_ldrSp j14 0 SLOTW_9 SLOTW_9 (by omega) f0 (by simp [FA]) (by rsimp <;> bv_omega))
    (preI_take_succ s 14 _ (by decide)).symm
  have j16 := JI_of_eq (J_ldrLit j15 6 19 A6 (by rw [preI_pc s 15 (by decide) (by decide), hpc]; exact l15) dA6)
    (preI_take_succ s 15 _ (by decide)).symm
  have j17 := JI_of_eq (J_eors j16 6 0)
    (preI_take_succ s 16 _ (by decide)).symm
  have j18 := JI_of_eq (J_movHi j17 11 6 (by decide) (by decide))
    (preI_take_succ s 17 _ (by decide)).symm
  have j19 := JI_of_eq (J_ldrLit j18 0 18 A7 (by rw [preI_pc s 18 (by decide) (by decide), hpc]; exact l18) dA7)
    (preI_take_succ s 18 _ (by decide)).symm
  have j20 := JI_of_eq (J_movHi j19 12 0 (by decide) (by decide))
    (preI_take_succ s 19 _ (by decide)).symm
  have j21 := JI_of_eq (J_addRdSp j20 4 8)
    (preI_take_succ s 20 _ (by decide)).symm
  have j23 := JI_of_eq (J_copy4' 8 j21 (by omega) (by rsimp <;> bv_omega) (R0 1 + BitVec.ofNat 32 0) (by rsimp <;> bv_omega)
    (disjAdd hbk 0 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 4 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 8 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 12 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_copy s 21 (by decide)).symm
  have j25 := JI_of_eq (J_copy4' 12 j23 (by omega) (by rsimp <;> bv_omega) (R0 1 + BitVec.ofNat 32 16) (by rsimp <;> bv_omega)
    (disjAdd hbk 16 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 20 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 24 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 28 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_copy s 23 (by decide)).symm
  have j27 := JI_of_eq (J_copy4' 16 j25 (by omega) (by rsimp <;> bv_omega) (R0 1 + BitVec.ofNat 32 32) (by rsimp <;> bv_omega)
    (disjAdd hbk 32 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 36 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 40 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 44 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_copy s 25 (by decide)).symm
  have j29 := JI_of_eq (J_copy4' 20 j27 (by omega) (by rsimp <;> bv_omega) (R0 1 + BitVec.ofNat 32 48) (by rsimp <;> bv_omega)
    (disjAdd hbk 48 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 52 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 56 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hbk 60 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_copy s 27 (by decide)).symm
  have j30 := JI_of_eq (J_ldrSp j29 1 HPTR_WORDS HPTR_WORDS (by omega) (R0 0) (by simp (config := {decide := true}) [FA]) (by rsimp <;> bv_omega))
    (preI_take_succ s 29 _ (by decide)).symm
  have j31 := JI_of_eq (J_ldm4d' j30 (R0 0) (by rsimp)
    (disjAdd hhp 0 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 4 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 8 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 12 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_succ s 30 _ (by decide)).symm
  have j32 := JI_of_eq (J_movHi j31 8 0 (by decide) (by decide))
    (preI_take_succ s 31 (.movHi 8 0) (by decide)).symm
  have j33 := JI_of_eq (J_addRdSp j32 4 1)
    (preI_take_succ s 32 _ (by decide)).symm
  have j34 := JI_of_eq (J_stm4c 1 j33 (by omega) (by rsimp <;> bv_omega))
    (preI_take_succ s 33 _ (by decide)).symm
  have j36 := JI_of_eq (J_copy4' 4 j34 (by omega) (by rsimp <;> bv_omega) (R0 0 + BitVec.ofNat 32 16) (by rsimp <;> bv_omega)
    (disjAdd hhp 16 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 20 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 24 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega)))
    (disjAdd hhp 28 (by omega) _ (by first | bv_omega | (rsimp <;> bv_omega))))
    (preI_take_copy s 34 (by decide)).symm
  have j37 := JI_of_eq (J_ldrLit j36 2 2 A0 (by rw [preI_pc s 36 (by decide) (by decide), hpc]; exact l36) dA0)
    (preI_take_succ s 36 _ (by decide)).symm
  have j38 := JI_of_eq (J_ldrLit j37 5 3 A1 (by rw [preI_pc s 37 (by decide) (by decide), hpc]; exact l37) dA1)
    (preI_take_succ s 37 _ (by decide)).symm
  have j39 := JI_of_eq (J_ldrLit j38 6 3 A2 (by rw [preI_pc s 38 (by decide) (by decide), hpc]; exact l38) dA2)
    (preI_take_succ s 38 _ (by decide)).symm
  have j40 := JI_of_eq (J_ldrLit j39 7 4 A3 (by rw [preI_pc s 39 (by decide) (by decide), hpc]; exact l39) dA3)
    (preI_take_succ s 39 _ (by decide)).symm
  have hall : preI.take 40 = preI := by decide
  rw [hall] at j40
  refine ⟨_, _, j40, ?_⟩
  unfold PreRF
  refine ⟨?r13, ?r8, ?r2, ?r5, ?r6, ?r7, ?r9, ?r10, ?r11, ?r12, ?f1, ?f2, ?f24, ?f34, ?f25, ?f26, ?f27, ?f28, ?f29, ?f30, ?f31, ?f32, ?f33⟩
  all_goals try rsimp
  case r10 => rfl
  case f1 =>
    intro i h1 h2
    have hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [FA] <;> (try (congr 1; bv_omega))
  case f2 =>
    intro i hi
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [FA] <;> (try (congr 1; bv_omega))
  all_goals simp (config := {decide := true}) [FA]

end M0Crypto.Release.Blake2sPro
