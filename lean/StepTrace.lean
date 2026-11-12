import M0Crypto.Thumb.FastRun

/-!
Run the machine model from recorded machine states and print every state it passes through
(`tools/qemu_steps.py`, which compares them with QEMU's, instruction by instruction).

Input lines:

* `flash ADDR HEX`: read-only bytes, shared by all cases;
* `case NAME`, then `ram ADDR HEX`, `regs R0 … R15 NZCV` (hex words, flags as four binary
  digits) and `stop ADDR`: one call, entered in that state, run until PC = `stop`.

Output per case: `case NAME`, one `R0 … R15 NZCV` line per executed instruction (the state
after it), then `ram HEX` (the final RAM) or `fault …`.

The states come from `Thumb.step`, the function the theorems are about. `record` and `flatten`
(`FastRun.lean`) only keep the state's memory and registers in flat form between steps, which
`flatten_eq` and `inv_step` prove changes nothing.
-/

open M0Crypto.Armv6M M0Crypto.Thumb

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0

def hexBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (hexNat (String.ofList [cs[2 * i]!, cs[2 * i + 1]!])).toUInt8
  return out

def hex (width n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d

/-- Memory holding `flash` and `ram` at their addresses, zero elsewhere. -/
def memOf (flash ram : Nat × ByteArray) : Mem := fun a =>
  let x := a.toNat
  if ram.1 ≤ x ∧ x < ram.1 + ram.2.size then BitVec.ofNat 8 ram.2[x - ram.1]!.toNat
  else if flash.1 ≤ x ∧ x < flash.1 + flash.2.size then BitVec.ofNat 8 flash.2[x - flash.1]!.toNat
  else 0

def stateLine (s : State) : String :=
  let bit (b : Bool) := if b then "1" else "0"
  " ".intercalate ((List.finRange 16).map fun r => hex 8 (s.regs r).toNat) ++
    " " ++ bit s.n ++ bit s.z ++ bit s.c ++ bit s.v

def runCase (flash ram : Nat × ByteArray) (regs : Array Word) (flags : String) (stop : Word) :
    IO Unit := do
  let flag (i : Nat) := flags.toList.getD i '0' == '1'
  let base := memOf flash ram
  let mut s : State := ⟨regsOfArray regs, flag 0, flag 1, flag 2, flag 3, base⟩
  let mut t : Tbl := {}
  for _ in [0:4000000] do
    if s.pc = stop then
      let bytes := (List.range ram.2.size).map fun i => hex 2 (s.mem (BitVec.ofNat 32 (ram.1 + i))).toNat
      IO.println ("ram " ++ String.join bytes)
      return
    match step s with
    | .error e => IO.println s!"fault {repr e} at pc {hex 8 s.pc.toNat}"; return
    | .ok (s1, ev) =>
      t := record s1.mem (writtenAddrs ev.accesses) t
      s := flatten base t s1
      IO.println (stateLine s)
  IO.println "fault: no return within the step limit"

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: StepTrace FILE"; return 2
  let mut flash : Nat × ByteArray := (0, .empty)
  let mut ram : Nat × ByteArray := (0, .empty)
  let mut regs : Array Word := #[]
  let mut flags := ""
  for line in ← IO.FS.lines path do
    match line.splitOn " " with
    | ["flash", a, h] => flash := (hexNat a, hexBytes h)
    | ["case", name] => IO.println s!"case {name}"
    | ["ram", a, h] => ram := (hexNat a, hexBytes h)
    | "regs" :: ws =>
      regs := (ws.take 16).toArray.map fun w => BitVec.ofNat 32 (hexNat w)
      flags := ws.getD 16 ""
    | ["stop", a] => runCase flash ram regs flags (BitVec.ofNat 32 (hexNat a))
    | _ => IO.eprintln s!"malformed line: {line.take 40}"; return 2
  return 0
