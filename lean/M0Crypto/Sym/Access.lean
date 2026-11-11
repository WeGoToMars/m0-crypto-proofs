import M0Crypto.Sym.SoundMem

/-!
# Symbolic executor, layer 2: accesses and traces

`symAccesses i ss` mirrors `Instr.accesses` constructor for constructor, with the
addresses as syntax over the symbolic state. `symAccesses_sound` holds for every
instruction, with no `Sound` hypothesis: it only unfolds both sides.

For a list of instructions whose members are all `Sound`, `symTrace` steps the
symbolic state with `symStep` and records, per instruction, the symbolic pc, the
instruction and its symbolic accesses. `symTrace_sound` says that its denotation is
exactly `traceAll`, and `alignedAll_sym` decides alignment from it.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb

/-- One data access with a symbolic address. -/
structure SAccess where
  kind : Kind
  addr : SExpr
  width : Nat

def SAccess.denote (s0 : State) (a : SAccess) : Access := ⟨a.kind, a.addr.denote s0, a.width⟩

/-- Symbolic `wordAccesses`: `n` word accesses at ascending addresses from `a`. -/
def symWords (k : Kind) (a : SExpr) (n : Nat) : List SAccess :=
  (List.range n).map fun i => ⟨k, .add a (.const (BitVec.ofNat 32 (4 * i))), 4⟩

theorem symWords_denote (s0 : State) (k : Kind) (a : SExpr) (n : Nat) :
    (symWords k a n).map (SAccess.denote s0) = wordAccesses k (a.denote s0) n := by
  unfold symWords wordAccesses
  rw [List.map_map]
  rfl

/-- Symbolic `Instr.accesses`: the same accesses, with addresses as syntax over `ss`. -/
def symAccesses (i : Instr) (ss : SState) : List SAccess :=
  let k := fun (n : Nat) => SExpr.const (BitVec.ofNat 32 n)
  match i with
  | .ldrLit _ imm8 =>
    [⟨.read, .add (.and (.add (ss.regs 15) (k 4)) (.not (k 3))) (k (imm8.toNat * 4)), 4⟩]
  | .memReg op _ n m =>
    [⟨if op.isLoad then .read else .write, .add (ss.reg n) (ss.reg m), op.width⟩]
  | .memImm op _ n imm5 =>
    [⟨if op.isLoad then .read else .write, .add (ss.reg n) (k (imm5.toNat * op.width)), op.width⟩]
  | .strSp _ imm8 => [⟨.write, .add ss.sp (k (imm8.toNat * 4)), 4⟩]
  | .ldrSp _ imm8 => [⟨.read, .add ss.sp (k (imm8.toNat * 4)), 4⟩]
  | .push l lr =>
    let n := bitCount l + lr.toNat
    symWords .write (.sub ss.sp (k (4 * n))) n
  | .pop l pc => symWords .read ss.sp (bitCount l + pc.toNat)
  | .stm n l => symWords .write (ss.reg n) (bitCount l)
  | .ldm n l => symWords .read (ss.reg n) (bitCount l)
  | _ => []

theorem symAccesses_sound (i : Instr) (s0 : State) (ss : SState) :
    (symAccesses i ss).map (SAccess.denote s0) = i.accesses (ss.denote s0) := by
  cases i <;> simp only [symAccesses, Instr.accesses, SAccess.denote, symWords_denote,
    SExpr.denote, List.map_cons, List.map_nil, denote_reg, denote_regs, SState.sp, State.sp,
    State.pc]

/-- Symbolic trace: per instruction, its symbolic pc, the instruction and its symbolic
accesses; the state advances by `symStep`. -/
def symTrace : List Instr → SState → List (SExpr × Instr × List SAccess)
  | [], _ => []
  | i :: is, ss => (ss.regs 15, i, symAccesses i ss) :: symTrace is (symStep i ss)

/-- Denotation of one symbolic trace entry. -/
def SEvent.denote (s0 : State) : SExpr × Instr × List SAccess → Event
  | (pc, i, acc) => ⟨pc.denote s0, i, acc.map (SAccess.denote s0)⟩

theorem symTrace_sound : ∀ (is : List Instr), (∀ i ∈ is, Sound i) → ∀ (s0 : State) (ss : SState),
    (symTrace is ss).map (SEvent.denote s0) = traceAll is (ss.denote s0)
  | [], _, _, _ => rfl
  | i :: is, h, s0, ss => by
    have ih := symTrace_sound is (fun j hj => h j (List.mem_cons_of_mem _ hj)) s0 (symStep i ss)
    have hi : (symStep i ss).denote s0 = i.next (ss.denote s0) := h i List.mem_cons_self s0 ss
    have hacc := symAccesses_sound i s0 ss
    have hhead : SEvent.denote s0 (ss.regs 15, i, symAccesses i ss) =
        ⟨(ss.denote s0).pc, i, i.accesses (ss.denote s0)⟩ := by
      rw [← hacc]; rfl
    simp only [symTrace, List.map_cons, ih, hi, traceAll, hhead]

theorem alignedAll_eq_traceAll : ∀ (is : List Instr) (s : State),
    alignedAll is s = (traceAll is s).all (fun e => e.accesses.all Access.aligned)
  | [], _ => rfl
  | i :: is, s => by
    simp only [alignedAll, traceAll, List.all_cons, alignedAll_eq_traceAll is (i.next s)]

theorem alignedAll_sym (is : List Instr) (h : ∀ i ∈ is, Sound i) (s0 : State) (ss : SState) :
    alignedAll is (ss.denote s0) =
      (symTrace is ss).all (fun e => e.2.2.all (fun a => (a.denote s0).aligned)) := by
  rw [alignedAll_eq_traceAll, ← symTrace_sound is h s0 ss, List.all_map]
  congr 1
  funext e
  rcases e with ⟨pc, i, acc⟩
  simp only [Function.comp_def, SEvent.denote, List.all_map]

end M0Crypto.Sym
