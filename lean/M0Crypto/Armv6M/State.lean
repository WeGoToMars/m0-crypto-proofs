/-!
Minimal ARMv6-M architectural state for the pilot.

Scope and assumptions:
* Thumb state only, privileged/unprivileged mode and exceptions are not modelled.
* Core registers r0-r15 and APSR N/Z/C/V. EPSR, IPSR, PRIMASK and CONTROL are not
  modelled; the subset of instructions supported cannot read or write them.
* Data memory is a total byte map. Code is held separately in an immutable
  `Code` region (see `Step.lean`): the model assumes fetched bytes are not
  modified during execution and are not aliased by data writes.
-/

namespace M0Crypto.Armv6M

abbrev Word := BitVec 32

/-- Core register index. 13 = SP, 14 = LR, 15 = PC. -/
abbrev Reg := Fin 16

/-- Low register index r0-r7, as encoded in 3-bit Thumb fields. -/
abbrev LowReg := Fin 8

def LowReg.toReg (r : LowReg) : Reg := ⟨r.val, by omega⟩

structure State where
  regs : Reg → Word
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  mem : Word → BitVec 8

namespace State

/-- Program counter value, i.e. the address of the current instruction. -/
def pc (s : State) : Word := s.regs 15

def reg (s : State) (r : LowReg) : Word := s.regs r.toReg

def setReg (s : State) (r : Reg) (x : Word) : State :=
  { s with regs := fun i => if i = r then x else s.regs i }

/-- Set APSR.N and APSR.Z from a result; C and V are left unchanged. -/
def setNZ (s : State) (x : Word) : State :=
  { s with n := x.msb, z := x == 0 }

end State

end M0Crypto.Armv6M
