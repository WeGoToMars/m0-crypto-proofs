import SafegcdRow.Columns

namespace SafegcdRow

set_option linter.unusedSimpArgs false

open M0Crypto.Armv6M (State slot)
open M0Crypto.Thumb

/-- Annotate the instruction sequence with its public accesses. Offsets come
from instruction sizes and the access lists select registers and word slots. -/
def annotate (pc : Word) : List Instr → List (List Access) → List Event
  | [], _ => []
  | i :: is, acc =>
    ⟨pc, i, acc.headD []⟩ ::
      annotate (pc + BitVec.ofNat 32 i.size) is acc.tail

def loadAt (base : Word) (i : Nat) : Access := ⟨.read, slot base i, 4⟩
def storeAt (base : Word) (i : Nat) : Access := ⟨.write, slot base i, 4⟩

private def loadPlan (x y : Word) (i : Nat) : List (List Access) :=
  [[], [loadAt x i], [], [loadAt y i]]

private def storePlan (out : Word) (i : Nat) : List (List Access) :=
  [[], [], [], [storeAt out i]]

private def finishPlan (out : Word) : List (List Access) :=
  [[], [], [storeAt out 16]]

private theorem accumulate_trace (s : State) (i : BitVec 5) :
    traceAll (accumulate i) s =
      annotate s.pc (accumulate i) (loadPlan (s.regs 8) (s.regs 10) i.toNat) := by
  unfold accumulate loadPlan loadAt
  simp only [traceAll, annotate, List.headD, List.tail]
  row_simps
  rw [Nat.mul_comm]

private theorem emit_trace (s : State) (i : BitVec 5) :
    traceAll (emitShifted i) s =
      annotate s.pc (emitShifted i) (storePlan (s.regs 7) i.toNat) := by
  unfold emitShifted storePlan storeAt
  simp only [traceAll, annotate, List.headD, List.tail]
  row_simps
  rw [Nat.mul_comm]
  rfl

private theorem finish_trace (s : State) :
    traceAll finish s = annotate s.pc finish (finishPlan (s.regs 7)) := by
  unfold finish finishPlan storeAt
  simp only [traceAll, annotate, List.headD, List.tail]
  row_simps
  rfl

def quiet : Instr → Bool
  | .ldrLit .. | .memReg .. | .memImm .. | .strSp .. | .ldrSp .. | .push .. | .pop ..
  | .stm .. | .ldm .. => false
  | _ => true

theorem quiet_trace (is : List Instr) (s : State) (hf : is.all Instr.falls = true)
    (hq : is.all quiet = true) :
    traceAll is s = annotate s.pc is [] := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hf hq
    have ha : i.accesses s = [] := by cases i <;> simp_all [quiet, Instr.accesses]
    rw [traceAll, annotate, ha, ih _ hf.2 hq.2, exec_pc hf.1 (exec_ok_of_falls hf.1 s)]
    rfl

private theorem correction_quiet (i : BitVec 5) (modular : Bool) :
    (correctionFor i modular).all quiet = true ∧ (correctionFor i modular).all Instr.falls = true := by
  cases modular <;> by_cases h0 : i = 0#5 <;> by_cases h15 : i = 15#5 <;>
    simp only [correctionFor, correction, h0, h15, ite_true, ite_false] <;> decide

def nextPC (pc : Word) (is : List Instr) : Word := pc + BitVec.ofNat 32 (seqSize is)

theorem next_append (pc : Word) (a b : List Instr) :
    nextPC pc (a ++ b) = nextPC (nextPC pc a) b := by
  simp only [nextPC, seqSize, List.map_append, List.sum_append, ofNat_add_assoc]

def columnTail (i : Nat) : List Instr :=
  if i = 0 then [.lsrImm 4 0 14] else emitShifted (BitVec.ofNat 5 (i - 1))

theorem column_parts (i : Nat) (modular : Bool) : column i modular =
    accumulate (BitVec.ofNat 5 i) ++ correctionFor (BitVec.ofNat 5 i) modular ++ splitAccumulator ++ columnTail i := rfl

def predictedColumn (p : Pins) (pc : Word) (i : Nat) (modular : Bool := true) : List Event :=
  let acc := accumulate (BitVec.ofNat 5 i)
  let cor := correctionFor (BitVec.ofNat 5 i) modular
  let sp := splitAccumulator
  let pc₁ := nextPC pc acc
  let pc₂ := nextPC pc₁ cor
  let pc₃ := nextPC pc₂ sp
  annotate pc acc (loadPlan p.x p.y i) ++ annotate pc₁ cor [] ++ annotate pc₂ sp [] ++
    annotate pc₃ (columnTail i) (if i = 0 then [] else storePlan p.out (i - 1))

private theorem prep_keeps_out (i : BitVec 5) (s : State) (modular : Bool) :
    (execAll splitAccumulator (execAll (correctionFor i modular) (execAll (accumulate i) s))).regs 7 = s.regs 7 := by
  have hc : (correctionFor i modular).all (fun z => !z.dsts.contains 7) = true := by
    cases modular <;> by_cases h0 : i = 0#5 <;> by_cases h15 : i = 15#5 <;>
      simp only [correctionFor, correction, h0, h15, ite_true, ite_false] <;> decide
  rw [execAll_regs_other _ _ 7 (by decide) (by decide),
    execAll_regs_other _ _ 7 (by decide) hc, execAll_regs_other _ _ 7 (by decide) (by rfl)]

theorem column_falls (i : Nat) (modular : Bool) : (column i modular).all Instr.falls = true := by
  rw [column_parts]
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨rfl, (correction_quiet _ modular).2⟩, by decide⟩, ?_⟩
  by_cases h : i = 0 <;> simp only [columnTail, h, ite_true, ite_false] <;> rfl

theorem column_trace (s : State) (p : Pins) (i : Nat) (hi : i < 17) (modular : Bool) (hh : p.held s modular) :
    traceAll (column i modular) s = predictedColumn p s.pc i modular := by
  obtain ⟨ho,hx,hy,_⟩ := hh
  have o : (BitVec.ofNat 5 i).toNat = i := by simp; omega
  have o' : (BitVec.ofNat 5 (i - 1)).toNat = i - 1 := by simp; omega
  rw [column_parts]
  simp only [execAll_append, traceAll_append]
  rw [accumulate_trace, hx, hy, o, quiet_trace _ _ (correction_quiet _ modular).2 (correction_quiet _ modular).1,
    quiet_trace splitAccumulator _ (by decide) (by decide)]
  by_cases h : i = 0
  · simp only [columnTail, h, ite_true]
    rw [quiet_trace _ _ (by decide) (by decide)]
    simp only [predictedColumn, columnTail, h, ite_true, nextPC, execAll_pc _ _ (correction_quiet _ modular).2,
      execAll_pc splitAccumulator _ (by decide),
      execAll_pc (accumulate _) _ (by rfl)]
  · simp only [columnTail, h, ite_false]
    rw [emit_trace, prep_keeps_out, ho, o']
    simp only [predictedColumn, columnTail, h, ite_false, nextPC, execAll_pc _ _ (correction_quiet _ modular).2,
      execAll_pc splitAccumulator _ (by decide),
      execAll_pc (accumulate _) _ (by rfl)]

def AccessIn (p : Pins) (a : Access) : Prop :=
  ∃ i < 17, a = loadAt p.x i ∨ a = loadAt p.y i ∨ a = storeAt p.out i

def TraceIn (p : Pins) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ a ∈ e.accesses, AccessIn p a

private theorem annotate_in (p : Pins) (pc : Word) (is : List Instr) (acc : List (List Access))
    (h : ∀ as ∈ acc, ∀ a ∈ as, AccessIn p a) :
    TraceIn p (annotate pc is acc) := by
  induction is generalizing pc acc with
  | nil => simp [TraceIn, annotate]
  | cons ins is ih =>
    intro e he a ha
    simp only [annotate, List.mem_cons] at he
    rcases he with rfl | he
    · cases acc with
      | nil => simp [List.headD] at ha
      | cons as rest => exact h as (by simp) a ha
    · apply ih _ _ (fun as has => h as (List.mem_of_mem_tail has)) _ he _ ha

theorem in_append {p : Pins} {x y : List Event} (hx : TraceIn p x) (hy : TraceIn p y) :
    TraceIn p (x ++ y) := by
  intro e he
  exact (List.mem_append.mp he).elim (hx e) (hy e)

private theorem load_in (p : Pins) (i : Nat) (hi : i < 17) (pc : Word) (is : List Instr) :
    TraceIn p (annotate pc is (loadPlan p.x p.y i)) := by
  apply annotate_in
  intro t ht a ha
  simp only [loadPlan, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact False.elim ((List.not_mem_nil) ha)
  · exact ⟨i, hi, .inl (List.mem_singleton.mp ha)⟩
  · exact False.elim ((List.not_mem_nil) ha)
  · exact ⟨i, hi, .inr (.inl (List.mem_singleton.mp ha))⟩

private theorem empty_in (p : Pins) (pc : Word) (is : List Instr) : TraceIn p (annotate pc is []) :=
  annotate_in _ _ _ _ (by simp)

private theorem store_in (p : Pins) (i : Nat) (hi : i < 17) (pc : Word)
    (is : List Instr) : TraceIn p (annotate pc is (storePlan p.out i)) := by
  apply annotate_in
  intro t ht a ha
  simp only [storePlan, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals first | exact False.elim ((List.not_mem_nil) ha) |
    exact ⟨i, hi, .inr (.inr (List.mem_singleton.mp ha))⟩

theorem predictedColumn_in (p : Pins) (pc : Word) (i : Nat) (hi : i < 17) (modular : Bool) :
    TraceIn p (predictedColumn p pc i modular) := by
  unfold predictedColumn
  apply in_append (in_append (in_append (load_in _ _ hi _ _) (empty_in _ _ _)) (empty_in _ _ _))
  by_cases h : i = 0
  · simp only [h, ite_true]; exact empty_in _ _ _
  · simp only [h, ite_false]; exact store_in _ _ (by omega) _ _

def predicted (p : Pins) (pc : Word) (modular : Bool) : List Nat → List Event
  | [] => annotate pc finish (finishPlan p.out)
  | i :: is => predictedColumn p pc i modular ++ predicted p (nextPC pc (column i modular)) modular is

def predictedBody (p : Pins) (pc : Word) (modular : Bool := true) : List Event :=
  annotate pc (prologue modular) [] ++ predicted p (nextPC pc (prologue modular)) modular (List.range 17)

theorem prologue_trace (s : State) (modular : Bool) :
    traceAll (prologue modular) s = annotate s.pc (prologue modular) [] := by
  cases modular <;> exact quiet_trace _ _ (by decide) (by decide)

theorem finish_trace' (s : State) (p : Pins) (modular : Bool) (h : p.held s modular) :
    traceAll finish s = predicted p s.pc modular [] := by
  rw [finish_trace, h.1]
  rfl

theorem predicted_in (p : Pins) (pc : Word) (is : List Nat) (modular : Bool) (hi : ∀ i ∈ is, i < 17) :
    TraceIn p (predicted p pc modular is) := by
  induction is generalizing pc with
  | nil =>
    apply annotate_in
    intro t ht a ha
    simp only [finishPlan, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    all_goals first | exact False.elim ((List.not_mem_nil) ha) |
      exact ⟨16, by decide, .inr (.inr (List.mem_singleton.mp ha))⟩
  | cons i is ih =>
    exact in_append (predictedColumn_in p pc i (hi _ (by simp)) modular)
      (ih _ (fun i hm => hi i (by simp [hm])))

theorem body_trace_in (p : Pins) (pc : Word) (modular : Bool := true) :
    TraceIn p (predictedBody p pc modular) :=
  in_append (empty_in _ _ _) (predicted_in _ _ _ _ (fun _ h => List.mem_range.mp h))

end SafegcdRow
