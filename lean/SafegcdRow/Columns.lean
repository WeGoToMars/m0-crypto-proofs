import SafegcdRow.Blocks

namespace SafegcdRow
open M0Crypto.Armv6M (State Reg Mem read32 write32 write32_other slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr slot_byte_ne' ne_of_disj)

/-- At each input/output pair the row permits exact aliasing or disjointness. -/
def Aliases (out src : Word) : Prop :=
  out = src ∨ out.toNat + 68 ≤ src.toNat ∨ src.toNat + 68 ≤ out.toNat

def InRange (addr : Word) : Prop := addr.toNat + 68 ≤ 2^32

structure Layout (p : Pins) : Prop where
  dst : InRange p.out
  srcX : InRange p.x
  srcY : InRange p.y
  aliasX : Aliases p.out p.x
  aliasY : Aliases p.out p.y

structure Input where
  pins : Pins
  mem : Mem

def Input.x (s : Input) (i : Nat) : Word := read32 s.mem (slot s.pins.x i)
def Input.y (s : Input) (i : Nat) : Word := read32 s.mem (slot s.pins.y i)

def correctionWord (t : Word) (i : Nat) : Word :=
  if i = 0 then -(t * 19#32) else if i = 15 then t <<< 15 else 0

def accumulateWord (s : Input) (i : Nat) (c : Word) : Word :=
  s.pins.a * s.x i + s.pins.b * s.y i + c + correctionWord s.pins.t i

def carryIn (s : Input) : Nat → Word
  | 0 => 0
  | i + 1 => carry (accumulateWord s i (carryIn s i))

def digit (s : Input) (i : Nat) : Word := low (accumulateWord s i (carryIn s i))

def outWord (s : Input) (i : Nat) : Word :=
  if i = 16 then emitTop (carryIn s 17) (remainder (digit s 16))
  else emit (digit s (i + 1)) (remainder (digit s i))

def outPrefix (s : Input) (n : Nat) : Mem :=
  storeWords s.mem s.pins.out ((List.range n).map (outWord s))

theorem store_append_one (mem : Mem) (addr : Word) (vs : List Word) (v : Word) :
    storeWords mem addr (vs ++ [v]) = write32 (storeWords mem addr vs) (slot addr vs.length) v := by
  induction vs generalizing mem addr with
  | nil => simp [storeWords, slot]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, storeWords]
    rw [ih]
    congr 1
    unfold slot
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
    congr 2
    omega

theorem outPrefix_succ (s : Input) (n : Nat) :
    outPrefix s (n + 1) = write32 (outPrefix s n) (slot s.pins.out n) (outWord s n) := by
  simp only [outPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    store_append_one, List.length_map, List.length_range]

theorem read_prefix (s : Input) (src : Word) (hD : InRange s.pins.out) (hS : InRange src)
    (ha : Aliases s.pins.out src) (n i : Nat) (hn : n ≤ i) (hi : i < 17) :
    read32 (outPrefix s n) (slot src i) = read32 s.mem (slot src i) := by
  apply read32_congr
  intro k hk
  unfold outPrefix
  apply storeWords_other
  intro j q hj hq
  simp only [List.length_map, List.length_range] at hj
  rcases ha with ha | ha
  · rw [ha]
    exact (slot_byte_ne' src j i q k (by omega) (by omega) hq hk (by omega)).symm
  · simp only [slot, ofNat_add_assoc]
    exact (ne_of_disj hD hS ha (by omega : 4*j+q < 68) (by omega : 4*i+k < 68)).symm

/-- State just before column i. The one-column store delay ensures every unread
limb still has its original value, even when its base address equals out. -/
structure Ready (s : Input) (i : Nat) (t : State) (modular : Bool := true) : Prop where
  held : s.pins.held t modular
  exact_zero : modular = false → s.pins.t = 0
  mem : t.mem = outPrefix s (i - 1)
  c : t.regs 5 = carryIn s i
  prev : 0 < i → t.regs 4 = remainder (digit s (i - 1))

private theorem column_keeps (i : Nat) (s : State) (r : Reg) (modular : Bool)
    (hr : r.val ∈ [2, 3, 7, 8, 10, 11, 12, 13, 14]) :
    (execAll (column i modular) s).regs r = s.regs r := by
  apply execAll_regs_other
  · simp at hr
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    have h : r.val ≠ 0 ∧ r.val ≠ 1 ∧ r.val ≠ 4 ∧ r.val ≠ 5 ∧ r.val ≠ 6 := by omega
    cases modular <;> by_cases h0 : BitVec.ofNat 5 i = 0#5 <;> by_cases h15 : BitVec.ofNat 5 i = 15#5 <;>
      by_cases hz : i = 0 <;>
      simp [column, correctionFor, correction, splitAccumulator, accumulate, emitShifted, h0, h15, hz,
        Instr.dsts, MemOp.isLoad, List.contains_eq_mem, h.1, h.2.1] <;> omega

private theorem column_held (i : Nat) {s : State} {p : Pins} {modular : Bool}
    (h : p.held s modular) : p.held (execAll (column i modular) s) modular := by
  simp only [Pins.held, State.sp] at h ⊢
  rw [column_keeps i s 7 modular (by decide), column_keeps i s 8 modular (by decide),
    column_keeps i s 10 modular (by decide), column_keeps i s 2 modular (by decide),
    column_keeps i s 3 modular (by decide), column_keeps i s 14 modular (by decide),
    column_keeps i s 11 modular (by decide), column_keeps i s 12 modular (by decide),
    column_keeps i s 13 modular (by decide)]
  exact h

private theorem column_facts (s : Input) (i : Nat) (t : State)
    (hi : i < 17) (lay : Layout s.pins) {modular : Bool} (h : Ready s i t modular) :
    let u := execAll (column i modular) t
    u.mem = outPrefix s i ∧ u.regs 5 = carryIn s (i+1) ∧
    u.regs 4 = remainder (digit s i) := by
  have hi' : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  rcases h with ⟨hP, ht0, hM, hC, hPrev⟩
  obtain ⟨hout,hx,hy,ha,hb,ht,ht19,hret,hsp⟩ := hP
  let o := BitVec.ofNat 5 i
  let v := execAll (accumulate o) t
  let w := execAll (correctionFor o modular) v
  let u := execAll splitAccumulator w
  have hvm : v.mem = t.mem := execAll_mem _ _ (by rfl)
  have ho0 : o = 0#5 ↔ i = 0 := by
    constructor
    · intro e; have hh := congrArg BitVec.toNat e; exact hi'.symm.trans hh
    · rintro rfl; rfl
  have ho15 : o = 15#5 ↔ i = 15 := by
    constructor
    · intro e; have hh := congrArg BitVec.toNat e; exact hi'.symm.trans hh
    · rintro rfl; rfl
  have hv : v.regs 0 = s.pins.a * s.x i + s.pins.b * s.y i + carryIn s i := by
    change (execAll (accumulate o) t).regs 0 = _
    rw [accumulate_word, hi', ha, hb, hx, hy, hM, hC,
      read_prefix s s.pins.x lay.dst lay.srcX lay.aliasX _ _ (by omega) hi,
      read_prefix s s.pins.y lay.dst lay.srcY lay.aliasY _ _ (by omega) hi]
    rfl
  have hv11 : v.regs 11 = t.regs 11 := execAll_regs_other _ _ _ (by decide) (by rfl)
  have hv14 : v.regs 14 = t.regs 14 := execAll_regs_other _ _ _ (by decide) (by rfl)
  have hw : w.regs 0 = accumulateWord s i (carryIn s i) := by
    change (execAll (correctionFor o modular) v).regs 0 = _
    cases hh : modular
    · have hz : correctionWord (0 : Word) i = 0 := by
        unfold correctionWord
        split
        · change -(0#32 * 19#32) = 0#32
          decide
        · split <;> rfl
      simp only [correctionFor, Bool.false_eq_true, ite_false, execAll, hv, accumulateWord,
        ht0 hh, hz]
      exact (BitVec.add_zero _).symm
    · simp only [correctionFor, ite_true]
      rw [correction_word, hv, hv11, hv14, ht19 hh, ht hh]
      simp only [ho0, ho15]
      rfl
  have hwm : w.mem = v.mem := by
    apply execAll_mem
    cases modular <;> by_cases h0 : o = 0#5 <;> by_cases h15 : o = 15#5 <;>
      simp [correctionFor, correction, h0, h15, Instr.writesMem]
  have hum : u.mem = t.mem := by
    have e : u.mem = w.mem := execAll_mem _ _ (by decide)
    rw [e, hwm, hvm]
  have huc : u.regs 5 = carryIn s (i + 1) := by
    rw [(split_effect w).1, hw]; rfl
  have hud : u.regs 0 = digit s i := by
    rw [(split_effect w).2, hw]; rfl
  change (execAll (column i modular) t).mem = outPrefix s i ∧
    (execAll (column i modular) t).regs 5 = carryIn s (i+1) ∧
    (execAll (column i modular) t).regs 4 = remainder (digit s i)
  simp only [column, execAll_append]
  change (execAll _ u).mem = _ ∧ (execAll _ u).regs 5 = _ ∧ (execAll _ u).regs 4 = _
  by_cases hz : i = 0
  · subst i
    refine ⟨(execAll_mem _ _ (by decide)).trans (hum.trans hM),
      (execAll_regs_other _ _ _ (by decide) (by decide)).trans huc, ?_⟩
    exact (head_remainder u).trans (congrArg remainder hud)
  · simp only [hz, ↓reduceIte]
    let j := BitVec.ofNat 5 (i - 1)
    have hj : j.toNat = i - 1 := by simp [j]; omega
    have huReg (r : Reg) (hr : r = 4 ∨ r = 7) : u.regs r = t.regs r := by
      have ha' : (accumulate o).all (fun z => !(z.dsts.contains r.val)) = true := by
        rcases hr with rfl | rfl <;> rfl
      have hc' : (correctionFor o modular).all (fun z => !(z.dsts.contains r.val)) = true := by
        cases modular <;> rcases hr with rfl | rfl <;> by_cases h0 : o = 0#5 <;> by_cases h15 : o = 15#5 <;>
          simp only [correctionFor, correction, h0, h15, ite_true, ite_false] <;> rfl
      have hs' : splitAccumulator.all (fun z => !(z.dsts.contains r.val)) = true := by
        rcases hr with rfl | rfl <;> rfl
      have hr' : r.val ≠ 15 := by rcases hr with rfl | rfl <;> decide
      unfold u w v
      rw [execAll_regs_other _ _ _ hr' hs', execAll_regs_other _ _ _ hr' hc',
        execAll_regs_other _ _ _ hr' ha']
    obtain ⟨hm, hr⟩ := shift_effect u j
    have hc : (execAll (emitShifted j) u).regs 5 = u.regs 5 :=
      execAll_regs_other _ _ _ (by decide) (by rfl)
    refine ⟨?_, hc.trans huc, hr.trans (congrArg remainder hud)⟩
    have e : i - 1 + 1 = i := by omega
    rw [hm, hum, hM, huReg 7 (.inr rfl), hout, huReg 4 (.inl rfl), hPrev (by omega),
      hud, hj, ← e, outPrefix_succ, outWord]
    rw [e]
    simp [show i - 1 ≠ 16 by omega]

theorem column_ready (s : Input) (i : Nat) (t : State) (hi : i < 17)
    (lay : Layout s.pins) {modular : Bool} (h : Ready s i t modular) :
    Ready s (i + 1) (execAll (column i modular) t) modular := by
  obtain ⟨hm, hc, hp⟩ := column_facts s i t hi lay h
  exact ⟨column_held _ h.held, h.exact_zero, by simpa using hm, hc, fun _ => by simpa using hp⟩

end SafegcdRow
