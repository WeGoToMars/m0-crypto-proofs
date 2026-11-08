import M0Crypto.Thumb.Program
import Std.Data.HashMap

/-!
A fast evaluator for the whole-function model, proved equal to `runUntil`.

The model's memory and registers are functions; every write wraps another closure
around them, so evaluating long runs directly is quadratic. `runFast` keeps the
bytes written so far in a hash map, and after every step replaces the state's
memory by "the map, else the initial memory" and its registers by an array lookup.

`runFast_eq` proves `runFast = runUntil`. The invariant is that the state's memory
equals the map over the initial memory; `step_mem_other` (from `exec_mem_other`)
shows each step changes memory only at the addresses it writes, which are exactly
the ones the runner records. So this file adds speed, not trust.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

/-! ## Frame for one step -/

/-- Byte addresses an access list writes. -/
def writtenAddrs (acc : List Access) : List Word :=
  acc.flatMap fun a =>
    if a.kind = .write then (List.range a.width).map fun k => a.addr + BitVec.ofNat 32 k else []

theorem mem_writtenAddrs (acc : List Access) (y : Word) : y ∈ writtenAddrs acc ↔ Writes acc y := by
  simp only [writtenAddrs, List.mem_flatMap, Writes]
  constructor
  · rintro ⟨a, ha, hy⟩
    split at hy
    · simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact ⟨a, ha, by assumption, k, hk, rfl⟩
    · simp at hy
  · rintro ⟨a, ha, hw, k, hk, rfl⟩
    refine ⟨a, ha, ?_⟩
    simp only [hw, ite_true, List.mem_map, List.mem_range]
    exact ⟨k, hk, rfl⟩

theorem step_mem_other {s s' : State} {e : Event} (h : step s = .ok (s', e)) (y : Word)
    (hy : y ∉ writtenAddrs e.accesses) : s'.mem y = s.mem y := by
  simp only [step] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i i _
      split at h
      · split at h
        · rename_i s1 hex
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact exec_mem_other i s s1 hex y (by rwa [mem_writtenAddrs] at hy)
        · cases h
      · cases h

/-! ## Recording written bytes -/

abbrev Tbl := Std.HashMap Nat (BitVec 8)

/-- Record the current value of `m` at each address of `as`. -/
def record (m : Mem) (as : List Word) (t : Tbl) : Tbl :=
  as.foldl (fun t a => t.insert a.toNat (m a)) t

theorem record_get (m : Mem) (as : List Word) (t : Tbl) (y : Word) :
    (record m as t)[y.toNat]? = if y ∈ as then some (m y) else t[y.toNat]? := by
  induction as generalizing t with
  | nil => simp [record]
  | cons a as ih =>
    simp only [record, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hy : y ∈ as
    · simp [hy]
    · simp only [hy, ite_false, List.mem_cons, Std.HashMap.getElem?_insert]
      by_cases ha : y = a
      · subst ha; simp
      · have : (a.toNat == y.toNat) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h; exact ha (BitVec.eq_of_toNat_eq h).symm
        simp [ha, this]

/-- Memory seen through the table: recorded bytes, else the initial memory. -/
def view (base : Mem) (t : Tbl) : Mem := fun a => (t[a.toNat]?).getD (base a)

/-- Register lookup in an array. -/
def regsOfArray (arr : Array Word) : Reg → Word := fun i => arr.getD i.val 0

/-- The sixteen register values as an array.

Evaluation note: the compiler eta-expands any definition whose result is a
function, so a `flatRegs r : Reg → Word` would become `flatRegs r i` and rebuild
the array on every register read (about 16x more work per step, compounding).
Building the array in this `Array`-valued function, called from `flatten` (whose
result is a `State`), evaluates it once per step. -/
def regArray (r : Reg → Word) : Array Word := (List.finRange 16).toArray.map r

theorem regsOfArray_regArray (r : Reg → Word) : regsOfArray (regArray r) = r := by
  funext i
  simp [regsOfArray, regArray, Array.getD_eq_getD_getElem?]

/-- The state with memory and registers replaced by their flat forms. -/
def flatten (base : Mem) (t : Tbl) (s : State) : State :=
  ⟨regsOfArray (regArray s.regs), s.n, s.z, s.c, s.v, view base t⟩

def Inv (base : Mem) (t : Tbl) (s : State) : Prop := s.mem = view base t

theorem flatten_eq {base : Mem} {t : Tbl} {s : State} (h : Inv base t s) : flatten base t s = s := by
  simp only [flatten, regsOfArray_regArray]
  rw [show view base t = s.mem from h.symm]

theorem inv_step {base : Mem} {t : Tbl} {s s' : State} {e : Event} (hi : Inv base t s)
    (h : step s = .ok (s', e)) : Inv base (record s'.mem (writtenAddrs e.accesses) t) s' := by
  funext y
  simp only [view, record_get]
  split
  · rfl
  · rename_i hy
    rw [step_mem_other h y hy, hi]
    rfl

/-! ## The runner -/

def runFastAux (stop : Word) (base : Mem) : Nat → Tbl → State → Except Fault (State × List Event)
  | fuel, t, s =>
    if s.pc = stop then .ok (s, [])
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step s with
        | .error e => .error e
        | .ok (s1, e) =>
          let t1 := record s1.mem (writtenAddrs e.accesses) t
          match runFastAux stop base n t1 (flatten base t1 s1) with
          | .error e' => .error e'
          | .ok (s2, es) => .ok (s2, e :: es)

theorem runFastAux_eq (stop : Word) (base : Mem) (fuel : Nat) (t : Tbl) (s : State)
    (hi : Inv base t s) : runFastAux stop base fuel t s = runUntil stop fuel s := by
  induction fuel generalizing t s with
  | zero => simp [runFastAux, runUntil]
  | succ n ih =>
    rw [runFastAux, runUntil]
    split
    · rfl
    · simp only
      split
      · rename_i e h; simp [h]
      · rename_i s1 e h
        have hi1 := inv_step hi h
        rw [flatten_eq hi1, ih _ _ hi1, h]
        rfl

/-- Run from `s` whose memory is `base`: equal to `runUntil` (`runFast_eq`). -/
def runFast (stop : Word) (fuel : Nat) (s : State) : Except Fault (State × List Event) :=
  runFastAux stop s.mem fuel {} (flatten s.mem {} s)

theorem runFast_eq (stop : Word) (fuel : Nat) (s : State) : runFast stop fuel s = runUntil stop fuel s := by
  have hi : Inv s.mem {} s := by funext y; simp [view]
  unfold runFast
  rw [flatten_eq hi, runFastAux_eq stop s.mem fuel {} s hi]

end M0Crypto.Thumb
