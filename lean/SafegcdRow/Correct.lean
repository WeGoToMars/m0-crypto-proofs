import SafegcdRow.Trace
import SafegcdRow.Arithmetic

namespace SafegcdRow

set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
open M0Crypto.Armv6M (State Reg Mem slot read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_storeWords_same)

private theorem exec_columns (s : Input) (lay : Layout s.pins)
    (n i : Nat) (t : State) (modular : Bool) (hn : i+n = 17) (h : Ready s i t modular) :
    let cols := List.range' i n
    let is := cols.flatMap (fun j => column j modular) ++ finish
    let u := execAll is t
    u.mem = outPrefix s 17 ∧ u.regs 12 = s.pins.ret ∧ u.sp = s.pins.sp ∧
      traceAll is t = predicted s.pins t.pc modular cols := by
  induction n generalizing i t with
  | zero =>
    have hi : i = 17 := by omega
    subst i
    simp only [List.range'_zero, List.flatMap_nil, List.nil_append]
    have hm := h.mem
    have hc := h.c
    have hp := h.prev (by decide)
    refine ⟨?_, ?_, ?_, finish_trace' _ _ modular h.held⟩
    · rw [finish_mem, h.held.1, hm, hc, hp]
      exact (outPrefix_succ s 16).symm
    · rw [execAll_regs_other _ _ 12 (by decide) (by decide)]
      exact h.held.2.2.2.2.2.2.2.1
    · unfold State.sp
      rw [execAll_regs_other _ _ 13 (by decide) (by decide)]
      exact h.held.2.2.2.2.2.2.2.2
  | succ n ih =>
    simp only [List.range'_succ, Nat.add_one, List.flatMap_cons, List.append_assoc,
      execAll_append, traceAll_append, predicted]
    have hi : i < 17 := by omega
    obtain ⟨hm, hr, hs, ht⟩ := ih (i+1) (execAll (column i modular) t) (by omega)
      (column_ready s i t hi lay h)
    rw [execAll_pc _ _ (column_falls i modular)] at ht
    simp only [execAll_append, traceAll_append] at hm hr hs ht
    exact ⟨hm, hr, hs, by rw [column_trace t s.pins i hi modular h.held, ht]; rfl⟩

private theorem body_effect (s : State) (modular : Bool) (h : Layout (Pins.load s modular)) :
    let p := Pins.load s modular
    let u := execAll (body modular) s
    u.mem = outPrefix ⟨p, s.mem⟩ 17 ∧ u.regs 12 = p.ret ∧ u.sp = p.sp ∧
      traceAll (body modular) s = predictedBody p s.pc modular := by
  obtain ⟨hP, hM, hC⟩ := prologue_effect s modular
  let q : Input := ⟨Pins.load s modular, s.mem⟩
  have ready : Ready q 0 (execAll (prologue modular) s) modular :=
    ⟨hP, by intro ht; cases ht; rfl, hM, hC, fun hz => absurd hz (by decide)⟩
  obtain ⟨hm, hr, hs, ht⟩ := exec_columns q h 17 0 _ modular (by decide) ready
  have hF : (prologue modular).all Instr.falls = true := by cases modular <;> decide
  rw [execAll_pc _ _ hF] at ht
  have er : List.range' 0 17 = List.range 17 := by decide +kernel
  have e : body modular = prologue modular ++
      ((List.range' 0 17).flatMap (fun j => column j modular) ++ finish) := by simp [body, er, List.append_assoc]
  dsimp only
  rw [e, execAll_append, traceAll_append, prologue_trace, ht, er]
  exact ⟨hm, hr, hs, rfl⟩

theorem trace_body (s : State) (modular : Bool) (h : Layout (Pins.load s modular)) :
    traceAll (body modular) s = predictedBody (Pins.load s modular) s.pc modular :=
  (body_effect s modular h).2.2.2

def Aligned (p : Pins) : Prop :=
  p.out.toNat % 4 = 0 ∧ p.x.toNat % 4 = 0 ∧ p.y.toNat % 4 = 0

theorem slot_aligned (addr : Word) (ha : addr.toNat % 4 = 0) (i : Nat) :
    (slot addr i).toNat % 4 = 0 := by
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem accesses_aligned (p : Pins) (h : Aligned p) (a : Access) (ha : AccessIn p a) :
    a.aligned = true := by
  obtain ⟨i, _, he | he | he⟩ := ha
  · subst a; simp [loadAt, Access.aligned, slot_aligned _ h.2.1]
  · subst a; simp [loadAt, Access.aligned, slot_aligned _ h.2.2]
  · subst a; simp [storeAt, Access.aligned, slot_aligned _ h.1]

theorem aligned_of_trace (is : List Instr) (s : State)
    (h : ∀ e ∈ traceAll is s, ∀ a ∈ e.accesses, a.aligned = true) : alignedAll is s = true := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [alignedAll, Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr (h _ (.head _)), ih _ ?_⟩
    exact fun e he => h e (.tail _ he)

def result (p : Pins) (m : Mem) : Int :=
  weighted (limb (fun i => read32 m (slot p.out i))) 17

theorem result_words (s : Input) :
    result s.pins (outPrefix s 17) = weighted (limb (outWord s)) 17 := by
  unfold result
  apply weighted_congr
  intro i hi
  have hget : i < ((List.range 17).map (outWord s)).length := by simpa using hi
  have e := read32_storeWords_same s.mem s.pins.out ((List.range 17).map (outWord s)) i hget
    (by simp)
  have eq : read32 (outPrefix s 17) (slot s.pins.out i) = outWord s i := by
    simpa only [outPrefix, slot, List.getElem_map, List.getElem_range] using e
  dsimp only [limb]
  rw [eq]

/-- The proof contract reads the complete inputs from the initial state.
The output may coincide with either or both input buffers. -/
structure Entry (base : Word) (s : State) (modular : Bool := true) : Prop where
  pc : s.pc = base
  baseEven : base.toNat % 2 = 0
  thumbReturn : (s.regs 14).getLsbD 0 = true
  layout : Layout (Pins.load s modular)
  align : Aligned (Pins.load s modular)
  args : Args ⟨Pins.load s modular, s.mem⟩

def returnTrace (base ret : Word) (modular : Bool := true) : Word × Word :=
  (base + BitVec.ofNat 32 (returnOffset modular), ret &&& ~~~1#32)

theorem row_correct (base : Word) (s : State) {modular : Bool} (h : Entry base s modular) :
    let q : Input := ⟨Pins.load s modular, s.mem⟩
    ∃ t, runRow (rowBytes modular) base s modular =
      .ok (t, predictedBody q.pins base modular, returnTrace base q.pins.ret modular) ∧
      t.pc = q.pins.ret &&& ~~~1#32 ∧ t.sp = s.sp ∧
      t.mem = outPrefix q 17 ∧
      divisor * result q.pins t.mem = numerator q + (q.pins.t.toNat : Int) * prime ∧
      TraceIn q.pins (predictedBody q.pins base modular) := by
  obtain ⟨hm, hr, hsp, ht⟩ := body_effect s modular h.layout
  let q : Input := ⟨Pins.load s modular, s.mem⟩
  let u := execAll (body modular) s
  have ht' := body_trace_in q.pins s.pc modular
  have hal : alignedAll (body modular) s = true := by
    apply aligned_of_trace
    rw [ht]
    exact fun e he a ha => accesses_aligned q.pins h.align a (ht' e he a ha)
  have hlen : (rowBytes modular).length < 2^32 := by cases modular <;> decide
  have hfalls := body_falls_for modular
  have hrn := runH_seq h.baseEven hlen (body modular) 0 s
    (by simpa using h.pc) (by decide) (body_matches_for modular) hfalls
  rw [runSeq_eq _ _ hfalls hal, ht, h.pc] at hrn
  have hUPC : u.pc = base + BitVec.ofNat 32 (returnOffset modular) := by
    rw [execAll_pc _ _ hfalls, h.pc]
    rfl
  have hoff : (u.pc - base).toNat = (returnOffset modular) := by
    rw [hUPC]
    exact sub_base base _ (by cases modular <;> decide +kernel)
  have he : u.pc.getLsbD 0 = false := by
    rw [hUPC]
    exact pc_even base _ h.baseEven (by cases modular <;> decide +kernel)
  let t := u.setReg 15 (q.pins.ret &&& ~~~1#32)
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, body_trace_in _ _ modular⟩
  · unfold runRow
    rw [hrn]
    change (match returnStep (rowBytes modular) base u with
      | .error e => Except.error e
      | .ok (u, ret) => Except.ok (u, _, ret)) = _
    have ret : returnStep (rowBytes modular) base u = .ok (t, returnTrace base q.pins.ret modular) := by
      unfold returnStep executeReturn returnTrace
      have hRet : q.pins.ret.getLsbD 0 = true := h.thumbReturn
      have hr' : u.regs 12 = q.pins.ret := hr
      rw [he, hoff, return_matches_for modular]
      simp only [Bool.false_eq_true, ite_false, ite_true, hr', hRet, hUPC]
      rfl
    rw [ret]
  · simp [t, q, State.pc, State.setReg]
  · simpa [t, u, Pins.load, State.sp, State.setReg] using hsp
  · exact hm
  · rw [show t.mem = outPrefix q 17 from hm, result_words]
    exact exact_value q h.args

set_option maxHeartbeats 4000000 in
/-- The row body and its BX run as one sequence at the linked code offset. -/
theorem row_at {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State} {modular : Bool}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt code off (body modular ++ [.bx 12]) = true) (h : Entry s.pc s modular) :
    let q : Input := ⟨Pins.load s modular, s.mem⟩
    ∃ t, runH code base ((body modular).length + 1) s =
      .ok (t, predictedBody q.pins s.pc modular ++ [⟨nextPC s.pc (body modular), .bx 12, []⟩]) ∧
      t.pc = q.pins.ret &&& ~~~1#32 ∧ t.sp = s.sp ∧ t.mem = outPrefix q 17 ∧
      divisor * result q.pins t.mem = numerator q + (q.pins.t.toNat : Int) * prime ∧
      TraceIn q.pins (predictedBody q.pins s.pc modular) := by
  obtain ⟨hm, hr, hsp, ht⟩ := body_effect s modular h.layout
  let q : Input := ⟨Pins.load s modular, s.mem⟩
  let u := execAll (body modular) s
  have ht' := body_trace_in q.pins s.pc modular
  have hal : alignedAll (body modular) s = true := by
    apply aligned_of_trace
    rw [ht]
    exact fun e he a ha => accesses_aligned q.pins h.align a (ht' e he a ha)
  have hf := body_falls_for modular
  have he : (off + seqSize (body modular)) % 2 = 0 := by
    have hz : seqSize (body modular) % 2 = 0 := by cases modular <;> decide +kernel
    omega
  have hret : (u.regs 12).getLsbD 0 = true := by
    change ((execAll (body modular) s).regs 12).getLsbD 0 = true
    rw [hr]
    exact h.thumbReturn
  have hrun := runH_leaf hb hlen hpc ho hat hf hal he hret
  dsimp only at hrun
  rw [ht, execAll_pc _ _ hf] at hrun
  refine ⟨_, hrun, ?_, ?_, hm, ?_, ht'⟩
  · change (u.regs 12 &&& ~~~1#32) = _
    rw [hr]
  · change u.sp = s.sp
    exact hsp
  · have hvalue : divisor * result q.pins (outPrefix q 17) =
        numerator q + (q.pins.t.toNat : Int) * prime := by
      rw [result_words]
      exact exact_value q h.args
    have hMem : (u.setReg 15 (u.regs 12 &&& ~~~1#32)).mem = outPrefix q 17 := hm
    rw [hMem]
    exact hvalue

theorem row_bytes_at (modular : Bool) :
    seqAt (rowBytes modular) 0 (body modular ++ [.bx 12]) = true := by
  cases modular <;> decide +kernel

theorem result_read_word (q : Input) (i : Nat) (hi : i < 17) :
    read32 (outPrefix q 17) (slot q.pins.out i) = outWord q i := by
  have hget : i < ((List.range 17).map (outWord q)).length := by simpa using hi
  simpa only [outPrefix, slot, List.getElem_map, List.getElem_range] using
    read32_storeWords_same q.mem q.pins.out ((List.range 17).map (outWord q)) i hget (by simp)

theorem result_low_limbs (q : Input) (i : Nat) (hi : i < 16) :
    (read32 (outPrefix q 17) (slot q.pins.out i)).toNat < 65536 := by
  rw [result_read_word _ _ (by omega)]
  simp only [outWord, show i ≠ 16 by omega, ite_false, emit]
  exact low_bound _

def SamePublic (s t : State) : Prop :=
  s.regs 0 = t.regs 0 ∧ s.regs 1 = t.regs 1 ∧ s.regs 2 = t.regs 2 ∧ s.regs 14 = t.regs 14

theorem row_secret_independent (base : Word) (s t : State) {modular : Bool}
    (hs : Entry base s modular) (ht : Entry base t modular) (pub : SamePublic s t) :
    ∃ s' t' trace, runRow (rowBytes modular) base s modular = .ok (s', trace) ∧
      runRow (rowBytes modular) base t modular = .ok (t', trace) := by
  obtain ⟨s', hS, _⟩ := row_correct base s hs
  obtain ⟨t', hT, _⟩ := row_correct base t ht
  obtain ⟨ho,hx,hy,hr⟩ := pub
  have ep (pc : Word) (is : List Nat) :
      predicted (Pins.load s modular) pc modular is = predicted (Pins.load t modular) pc modular is := by
    induction is generalizing pc with
    | nil => simp [predicted, Pins.load, ho]
    | cons i is ih =>
      have ec : predictedColumn (Pins.load s modular) pc i modular = predictedColumn (Pins.load t modular) pc i modular := by
        simp [predictedColumn, Pins.load, ho, hx, hy]
      simp only [predicted, ec, ih]
  refine ⟨s', t', _, hS, ?_⟩
  rw [hT]
  apply congrArg Except.ok
  change (t', predictedBody (Pins.load t modular) base modular, returnTrace base (Pins.load t modular).ret modular) =
    (t', predictedBody (Pins.load s modular) base modular, returnTrace base (Pins.load s modular).ret modular)
  rw [predictedBody, predictedBody, ep]
  simp [returnTrace, Pins.load, hr]

theorem row_frame (q : Input) (addr : Word)
    (h : ∀ i < 68, addr ≠ q.pins.out + BitVec.ofNat 32 i) :
    outPrefix q 17 addr = q.mem addr := by
  unfold outPrefix
  apply storeWords_other
  intro i j hi hj
  simp only [List.length_map, List.length_range] at hi
  rw [ofNat_add_assoc]
  exact h _ (by omega)

end SafegcdRow
