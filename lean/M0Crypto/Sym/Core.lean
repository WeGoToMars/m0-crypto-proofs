import M0Crypto.Thumb.Seq
import M0Crypto.Spec.ChaCha20

/-!
# Symbolic executor, layer 1: mirror semantics

A symbolic machine state (`SState`) whose registers, flags and memory are *syntax*
(`SExpr`, `SBool`, `SMem`) over one unknown initial state. `symStep i` builds the
syntax of `Instr.next i` by mirroring `Instr.exec` constructor for constructor, so its
soundness is definitional unfolding: no algebra, no memory reasoning.

All simplification (read-over-write, ring normalisation, comparing against the RFC
specification) belongs to later layers, which rewrite `SExpr` with their own soundness
proofs. This file depends only on the machine model, never on the release bytes.

Interface used by everything above:
* `SState.denote s0 ss : State` — meaning of `ss` when the unknowns are the state `s0`;
* `SState.init` with `init.denote s0 = s0`;
* `symExec is ss` and `symExec_sound : (symExec is ss).denote s0 = execAll is (ss.denote s0)`
  for instruction lists with `is.all Instr.falls`;
* `symAccesses` with `symAccesses_sound`, giving `traceAll` / `alignedAll` / write sets.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry)
open M0Crypto.Thumb

mutual
/-- Word-valued syntax over an unknown initial state. -/
inductive SExpr where
  | reg0 (r : Reg)
  | const (w : Word)
  | add (a b : SExpr)
  | sub (a b : SExpr)
  | and (a b : SExpr)
  | or (a b : SExpr)
  | xor (a b : SExpr)
  | not (a : SExpr)
  | mul (a b : SExpr)
  | uxth (a : SExpr)
  /-- `(addWithCarry a b c).1` -/
  | awc (a b : SExpr) (c : SBool)
  /-- `(lslC a n c).1`, `(lsrC a n).1`, `(rorC a (b.toNat % 256) c).1` -/
  | lsl (a : SExpr) (n : Nat)
  | lsr (a : SExpr) (n : Nat)
  | ror (a b : SExpr) (c : SBool)
  | ld32 (m : SMem) (a : SExpr)
  | ld16 (m : SMem) (a : SExpr)
  | ld8 (m : SMem) (a : SExpr)
  /-- `rotl a n` is the RFC 8439 left rotation. It is never produced by `symStep`;
  only the normaliser introduces it (`Sym.Norm`, rule `rorK`). -/
  | rotl (a : SExpr) (n : Nat)

/-- Flag-valued syntax. -/
inductive SBool where
  | n0 | z0 | c0 | v0
  | const (b : Bool)
  | msb (a : SExpr)
  | isZero (a : SExpr)
  /-- `(addWithCarry a b c).2.1`, `.2.2` -/
  | awcC (a b : SExpr) (c : SBool)
  | awcV (a b : SExpr) (c : SBool)
  /-- carries of `lslC a n c`, `lsrC a n`, `rorC a (b.toNat % 256) c` -/
  | lslC (a : SExpr) (n : Nat) (c : SBool)
  | lsrC (a : SExpr) (n : Nat)
  | rorC (a b : SExpr) (c : SBool)

/-- Memory syntax: the initial memory and a stack of stores. -/
inductive SMem where
  | mem0
  | w32 (m : SMem) (a v : SExpr)
  | w16 (m : SMem) (a v : SExpr)
  | w8 (m : SMem) (a v : SExpr)
end

mutual
def SExpr.denote (s0 : State) : SExpr → Word
  | .reg0 r => s0.regs r
  | .const w => w
  | .add a b => a.denote s0 + b.denote s0
  | .sub a b => a.denote s0 - b.denote s0
  | .and a b => a.denote s0 &&& b.denote s0
  | .or a b => a.denote s0 ||| b.denote s0
  | .xor a b => a.denote s0 ^^^ b.denote s0
  | .not a => ~~~(a.denote s0)
  | .mul a b => a.denote s0 * b.denote s0
  | .uxth a => (a.denote s0).setWidth 16 |>.setWidth 32
  | .awc a b c => (addWithCarry (a.denote s0) (b.denote s0) (c.denote s0)).1
  | .lsl a n => a.denote s0 <<< n
  | .lsr a n => a.denote s0 >>> n
  | .ror a b c => (Armv6M.rorC (a.denote s0) ((b.denote s0).toNat % 256) (c.denote s0)).1
  | .ld32 m a => read32 (m.denote s0) (a.denote s0)
  | .ld16 m a => read16 (m.denote s0) (a.denote s0)
  | .ld8 m a => read8 (m.denote s0) (a.denote s0)
  | .rotl a n => M0Crypto.Spec.ChaCha20.rotl (a.denote s0) n

def SBool.denote (s0 : State) : SBool → Bool
  | .n0 => s0.n
  | .z0 => s0.z
  | .c0 => s0.c
  | .v0 => s0.v
  | .const b => b
  | .msb a => (a.denote s0).msb
  | .isZero a => a.denote s0 == 0
  | .awcC a b c => (addWithCarry (a.denote s0) (b.denote s0) (c.denote s0)).2.1
  | .awcV a b c => (addWithCarry (a.denote s0) (b.denote s0) (c.denote s0)).2.2
  | .lslC a n c => (Thumb.lslC (a.denote s0) n (c.denote s0)).2
  | .lsrC a n => (Thumb.lsrC (a.denote s0) n).2
  | .rorC a b c => (Armv6M.rorC (a.denote s0) ((b.denote s0).toNat % 256) (c.denote s0)).2

def SMem.denote (s0 : State) : SMem → Mem
  | .mem0 => s0.mem
  | .w32 m a v => write32 (m.denote s0) (a.denote s0) (v.denote s0)
  | .w16 m a v => write16 (m.denote s0) (a.denote s0) (v.denote s0)
  | .w8 m a v => write8 (m.denote s0) (a.denote s0) (v.denote s0)
end

/-- Symbolic machine state. -/
structure SState where
  regs : Reg → SExpr
  n : SBool
  z : SBool
  c : SBool
  v : SBool
  mem : SMem

namespace SState

def denote (s0 : State) (ss : SState) : State where
  regs := fun r => (ss.regs r).denote s0
  n := ss.n.denote s0
  z := ss.z.denote s0
  c := ss.c.denote s0
  v := ss.v.denote s0
  mem := ss.mem.denote s0

def init : SState := ⟨.reg0, .n0, .z0, .c0, .v0, .mem0⟩

theorem init_denote (s0 : State) : init.denote s0 = s0 := rfl

def setReg (ss : SState) (r : Reg) (x : SExpr) : SState :=
  { ss with regs := fun i => if i = r then x else ss.regs i }

def setNZ (ss : SState) (x : SExpr) : SState := { ss with n := .msb x, z := .isZero x }

def reg (ss : SState) (r : LowReg) : SExpr := ss.regs r.toReg

def sp (ss : SState) : SExpr := ss.regs 13

theorem denote_setReg (s0 : State) (ss : SState) (r : Reg) (x : SExpr) :
    (ss.setReg r x).denote s0 = (ss.denote s0).setReg r (x.denote s0) := by
  simp only [denote, setReg, State.setReg]; congr 1; funext i; split <;> rfl

theorem denote_setNZ (s0 : State) (ss : SState) (x : SExpr) :
    (ss.setNZ x).denote s0 = (ss.denote s0).setNZ (x.denote s0) := rfl

end SState

/-- `addFlags`, symbolically. -/
def sAddFlags (ss : SState) (d : Reg) (a b : SExpr) (c : SBool) (write : Bool := true) : SState :=
  let r := SExpr.awc a b c
  let ss := if write then ss.setReg d r else ss
  { ss with n := .msb r, z := .isZero r, c := .awcC a b c, v := .awcV a b c }

theorem denote_sAddFlags (s0 : State) (ss : SState) (d : Reg) (a b : SExpr) (c : SBool) (w : Bool) :
    (sAddFlags ss d a b c w).denote s0 =
      addFlags (ss.denote s0) d (a.denote s0) (b.denote s0) (c.denote s0) w := by
  cases w
  · rfl
  · simp only [sAddFlags, addFlags, ite_true, SState.denote, SState.setReg, State.setNZCV,
      State.setNZ, State.setReg]
    congr 1; funext i; split <;> rfl

/-- Stores of `storeWords`, symbolically. -/
def sStoreWords : SMem → SExpr → List SExpr → SMem
  | m, _, [] => m
  | m, a, v :: vs => sStoreWords (.w32 m a v) (.add a (.const 4#32)) vs

theorem denote_sStoreWords (s0 : State) : ∀ (m : SMem) (a : SExpr) (vs : List SExpr),
    (sStoreWords m a vs).denote s0 = storeWords (m.denote s0) (a.denote s0) (vs.map (·.denote s0))
  | _, _, [] => rfl
  | m, a, v :: vs => by
    simp only [sStoreWords, List.map_cons, storeWords]
    rw [denote_sStoreWords s0 _ _ vs]; rfl

/-- `loadRegs`, symbolically (reads the memory of `ss`). -/
def sLoadRegs (ss : SState) : SExpr → List Reg → SState
  | _, [] => ss
  | a, r :: rs => sLoadRegs (ss.setReg r (.ld32 ss.mem a)) (.add a (.const 4#32)) rs

theorem denote_sLoadRegs (s0 : State) : ∀ (ss : SState) (a : SExpr) (rs : List Reg),
    (sLoadRegs ss a rs).denote s0 = loadRegs (ss.denote s0) (a.denote s0) rs
  | _, _, [] => rfl
  | ss, a, r :: rs => by
    simp only [sLoadRegs, loadRegs]
    rw [denote_sLoadRegs s0 _ _ rs, SState.denote_setReg]; rfl

/-- One instruction, symbolically. Defined for every instruction; it agrees with
`Instr.next` whenever `i.falls` (`symStep_sound`). -/
def symStep (i : Instr) (ss : SState) : SState :=
  let next := ss.setReg 15 (.add (ss.regs 15) (.const (BitVec.ofNat 32 i.size)))
  let r := fun (x : LowReg) => ss.reg x
  let k := fun (n : Nat) => SExpr.const (BitVec.ofNat 32 n)
  match i with
  | .lslImm d m imm5 =>
    let x := SExpr.lsl (r m) imm5.toNat
    let x' := if imm5.toNat = 0 then r m else x
    { (next.setReg d.toReg x').setNZ x' with c := .lslC (r m) imm5.toNat ss.c }
  | .lsrImm d m imm5 =>
    let n := if imm5.toNat = 0 then 32 else imm5.toNat
    let x := SExpr.lsr (r m) n
    { (next.setReg d.toReg x).setNZ x with c := .lsrC (r m) n }
  | .addReg d n m => sAddFlags next d.toReg (r n) (r m) (.const false)
  | .subReg d n m => sAddFlags next d.toReg (r n) (.not (r m)) (.const true)
  | .addImm3 d n imm3 => sAddFlags next d.toReg (r n) (.const (imm3.setWidth 32)) (.const false)
  | .subImm3 d n imm3 => sAddFlags next d.toReg (r n) (.const (~~~(imm3.setWidth 32))) (.const true)
  | .movImm d imm8 =>
    let x := SExpr.const (imm8.setWidth 32)
    (next.setReg d.toReg x).setNZ x
  | .cmpImm n imm8 => sAddFlags next 0 (r n) (.const (~~~(imm8.setWidth 32))) (.const true) false
  | .addImm8 dn imm8 => sAddFlags next dn.toReg (r dn) (.const (imm8.setWidth 32)) (.const false)
  | .subImm8 dn imm8 => sAddFlags next dn.toReg (r dn) (.const (~~~(imm8.setWidth 32))) (.const true)
  | .dp op dn m =>
    match op with
    | .ands => let x := SExpr.and (r dn) (r m); (next.setReg dn.toReg x).setNZ x
    | .eors => let x := SExpr.xor (r dn) (r m); (next.setReg dn.toReg x).setNZ x
    | .orrs => let x := SExpr.or (r dn) (r m); (next.setReg dn.toReg x).setNZ x
    | .mvns => let x := SExpr.not (r m); (next.setReg dn.toReg x).setNZ x
    | .muls => let x := SExpr.mul (r m) (r dn); (next.setReg dn.toReg x).setNZ x
    | .tst => next.setNZ (.and (r dn) (r m))
    | .adcs => sAddFlags next dn.toReg (r dn) (r m) ss.c
    | .sbcs => sAddFlags next dn.toReg (r dn) (.not (r m)) ss.c
    | .rsbs => sAddFlags next dn.toReg (.not (r m)) (.const 0#32) (.const true)
    | .cmp => sAddFlags next 0 (r dn) (.not (r m)) (.const true) false
    | .rors =>
      let x := SExpr.ror (r dn) (r m) ss.c
      { (next.setReg dn.toReg x).setNZ x with c := .rorC (r dn) (r m) ss.c }
  | .movHi d m => next.setReg d (ss.regs m)
  | .ldrLit t imm8 =>
    let a := SExpr.add (.and (.add (ss.regs 15) (k 4)) (.not (k 3))) (k (imm8.toNat * 4))
    next.setReg t.toReg (.ld32 ss.mem a)
  | .memReg op t n m => sMemOp next op t (.add (r n) (r m))
  | .memImm op t n imm5 => sMemOp next op t (.add (r n) (k (imm5.toNat * op.width)))
  | .strSp t imm8 => { next with mem := .w32 ss.mem (.add ss.sp (k (imm8.toNat * 4))) (r t) }
  | .ldrSp t imm8 => next.setReg t.toReg (.ld32 ss.mem (.add ss.sp (k (imm8.toNat * 4))))
  | .addRdSp d imm8 => next.setReg d.toReg (.add ss.sp (k (imm8.toNat * 4)))
  | .addSp imm7 => next.setReg 13 (.add ss.sp (k (imm7.toNat * 4)))
  | .subSp imm7 => next.setReg 13 (.sub ss.sp (k (imm7.toNat * 4)))
  | .uxth d m => next.setReg d.toReg (.uxth (r m))
  | .push l lr =>
    let n := bitCount l + lr.toNat
    let a := SExpr.sub ss.sp (k (4 * n))
    let vals := (listRegs l).map r ++ (if lr then [ss.regs 14] else [])
    { next with mem := sStoreWords ss.mem a vals }.setReg 13 a
  | .pop l _ =>
    (sLoadRegs next ss.sp ((listRegs l).map LowReg.toReg)).setReg 13
      (.add ss.sp (k (4 * bitCount l)))
  | .stm n l =>
    { next with mem := sStoreWords ss.mem (r n) ((listRegs l).map r) }.setReg n.toReg
      (.add (r n) (k (4 * bitCount l)))
  | .ldm n l =>
    let s1 := sLoadRegs next (r n) ((listRegs l).map LowReg.toReg)
    if l.getLsbD n.val then s1 else s1.setReg n.toReg (.add (r n) (k (4 * bitCount l)))
  | _ => next
where
  sMemOp (next : SState) (op : MemOp) (t : LowReg) (a : SExpr) : SState :=
    let v := next.reg t
    match op with
    | .str => { next with mem := .w32 next.mem a v }
    | .strh => { next with mem := .w16 next.mem a v }
    | .strb => { next with mem := .w8 next.mem a v }
    | .ldr => next.setReg t.toReg (.ld32 next.mem a)
    | .ldrh => next.setReg t.toReg (.ld16 next.mem a)
    | .ldrb => next.setReg t.toReg (.ld8 next.mem a)

def symExec : List Instr → SState → SState
  | [], ss => ss
  | i :: is, ss => symExec is (symStep i ss)

theorem denote_regs (s0 : State) (ss : SState) (r : Reg) : (ss.denote s0).regs r = (ss.regs r).denote s0 := rfl

theorem denote_reg (s0 : State) (ss : SState) (r : LowReg) : (ss.denote s0).reg r = (ss.reg r).denote s0 := rfl

/-- `symStep i` agrees with `Instr.next i` on every state. -/
def Sound (i : Instr) : Prop := ∀ (s0 : State) (ss : SState), (symStep i ss).denote s0 = i.next (ss.denote s0)

theorem symExec_sound : ∀ (is : List Instr), (∀ i ∈ is, Sound i) → ∀ (s0 : State) (ss : SState),
    (symExec is ss).denote s0 = execAll is (ss.denote s0)
  | [], _, _, _ => rfl
  | i :: is, h, s0, ss => by
    simp only [symExec, execAll]
    rw [symExec_sound is (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i List.mem_cons_self]

/-- Instruction forms whose soundness is closed below by unfolding alone. The remaining
`falls` forms (`dp`, shifts, loads, stores, push/pop, stm/ldm) are covered in
`SoundAlu.lean` and `SoundMem.lean`, which extend this to
`sound_of_falls : i.falls = true → Sound i`. -/
def symBasic : Instr → Bool
  | .addReg .. | .subReg .. | .addImm3 .. | .subImm3 .. | .movImm .. | .cmpImm ..
  | .addImm8 .. | .subImm8 .. | .addRdSp .. | .addSp .. | .subSp .. | .uxth .. => true
  | .movHi d _ => d.val != 15
  | _ => false

theorem sound_basic (i : Instr) (h : symBasic i = true) : Sound i := by
  intro s0 ss
  cases i <;> simp only [symBasic, Bool.false_eq_true] at h
  all_goals
    simp only [symStep, Instr.next, Instr.exec, SState.denote_setReg, SState.denote_setNZ,
      denote_sAddFlags, SExpr.denote, SBool.denote, denote_regs, denote_reg, SState.reg, SState.sp,
      State.reg, State.sp, State.pc]

end M0Crypto.Sym
