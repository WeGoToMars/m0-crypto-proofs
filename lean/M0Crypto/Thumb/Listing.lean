import M0Crypto.Thumb.Decode
import M0Crypto.Artifacts.Release

/-!
Decoder coverage of the release artifact.

`sweepOf` walks each Thumb code range of an artifact (from the assembler's
mapping symbols) from its start, decoding one instruction at a time and advancing
by its size. The `#guard` below requires that every step decodes, and that each
range is tiled exactly (no instruction runs into a literal pool or past the end).

`render` prints a decoded instruction in llvm-objdump's syntax. `tools/check_listing.py`
compares that listing, offset by offset, with `llvm-objdump -d` on the release
object: an independent decoder agreeing on every instruction, including register
fields, immediates, branch targets and literal addresses. The targets are computed
with the same formulas `Exec.lean` uses.
-/

namespace M0Crypto.Thumb.Listing

open M0Crypto.Artifacts

/-- The halfword at byte offset `off` of `code`. -/
def hwAtOff (code : Array (BitVec 8)) (off : Nat) : BitVec 16 :=
  (code.getD (off + 1) 0) ++ (code.getD off 0)

/-- Decode the instructions of `[lo, hi)` of `code`, or report the first offset that fails. -/
def sweepRange (code : Array (BitVec 8)) (lo hi : Nat) : Except String (List (Nat × Instr)) :=
  go (hi - lo + 1) lo []
where
  go : Nat → Nat → List (Nat × Instr) → Except String (List (Nat × Instr))
    | 0, off, _ => .error s!"no progress at 0x{Nat.toDigits 16 off |> String.ofList}"
    | fuel + 1, off, acc =>
      if off = hi then .ok acc.reverse
      else if off > hi then .error s!"instruction crosses the range end 0x{Nat.toDigits 16 hi |> String.ofList}"
      else match decode (hwAtOff code off) (hwAtOff code (off + 2)) with
        | none => .error s!"undecodable at 0x{Nat.toDigits 16 off |> String.ofList}"
        | some i => go fuel (off + i.size) ((off, i) :: acc)

/-- Decode every code range of an artifact. -/
def sweepOf (bytes : List (BitVec 8)) (codeRanges : List (Nat × Nat)) :
    Except String (List (Nat × Instr)) :=
  let code := bytes.toArray
  codeRanges.foldlM (fun acc (lo, hi) => (acc ++ ·) <$> sweepRange code lo hi) []

/-- Code and data ranges cover the artifact contiguously from 0. -/
def rangesCoverOf (bytes : List (BitVec 8)) (codeRanges dataRanges : List (Nat × Nat)) : Bool :=
  let rs := (codeRanges ++ dataRanges).mergeSort (fun a b => a.1 ≤ b.1)
  (rs.foldl (fun (ok, pos) (lo, hi) => (ok && lo = pos && lo < hi, hi)) (true, 0)) ==
    (true, bytes.length)

/-- The workspace's artifact `Artifacts.Release`. An asset with several builds names each
build's artifact module instead (`lean/DumpListingEd25519.lean`). -/
def sweep : Except String (List (Nat × Instr)) := sweepOf Release.bytes Release.codeRanges

def sweepOk : Bool := match sweep with | .ok _ => true | .error _ => false

def rangesCover : Bool := rangesCoverOf Release.bytes Release.codeRanges Release.dataRanges

#guard rangesCover
#guard sweepOk

/-! ## llvm-objdump syntax -/

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def regName (r : Nat) : String :=
  match r with
  | 13 => "sp" | 14 => "lr" | 15 => "pc" | _ => s!"r{r}"

def lo (r : M0Crypto.Armv6M.LowReg) : String := regName r.val

def regList (l : BitVec 8) (extra : Option String) : String :=
  let rs := ((List.range 8).filter fun i => l.getLsbD i).map regName
  "{" ++ ", ".intercalate (rs ++ extra.toList) ++ "}"

def condName (c : Nat) : String :=
  match c with
  | 0 => "eq" | 1 => "ne" | 2 => "hs" | 3 => "lo" | 4 => "mi" | 5 => "pl" | 6 => "vs"
  | 7 => "vc" | 8 => "hi" | 9 => "ls" | 10 => "ge" | 11 => "lt" | 12 => "gt" | 13 => "le"
  | 14 => "al" | _ => "<und>"

def memName : MemOp → String
  | .str => "str" | .strh => "strh" | .strb => "strb"
  | .ldr => "ldr" | .ldrh => "ldrh" | .ldrb => "ldrb"

def dpName : DpOp → String
  | .ands => "ands" | .eors => "eors" | .lsls => "lsls" | .lsrs => "lsrs" | .adcs => "adcs" | .sbcs => "sbcs" | .rors => "rors" | .tst => "tst"
  | .rsbs => "rsbs" | .cmp => "cmp" | .orrs => "orrs" | .muls => "muls" | .mvns => "mvns"

def addr (base : String) (off : Nat) : String :=
  if off = 0 then s!"[{base}]" else s!"[{base}, #{hex off}]"

/-- Branch target at offset `pc` (same arithmetic as `Exec.lean`, mod 2^32). -/
def target {w : Nat} (pc : Nat) (imm : BitVec w) : String :=
  hex ((BitVec.ofNat 32 (pc + 4) + imm.signExtend 32).toNat)

/-- The instruction at offset `pc` in llvm-objdump syntax (comments dropped, except
the literal address of a PC-relative load). -/
def render (pc : Nat) : Instr → String
  | .lslImm d m 0 => s!"movs {lo d}, {lo m}"
  | .lslImm d m k => s!"lsls {lo d}, {lo m}, #{hex k.toNat}"
  | .lsrImm d m k => s!"lsrs {lo d}, {lo m}, #{hex (if k.toNat = 0 then 32 else k.toNat)}"
  | .asrImm d m k => s!"asrs {lo d}, {lo m}, #{hex (if k.toNat = 0 then 32 else k.toNat)}"
  | .addReg d n m => s!"adds {lo d}, {lo n}, {lo m}"
  | .subReg d n m => s!"subs {lo d}, {lo n}, {lo m}"
  | .addImm3 d n k => s!"adds {lo d}, {lo n}, #{hex k.toNat}"
  | .subImm3 d n k => s!"subs {lo d}, {lo n}, #{hex k.toNat}"
  | .movImm d k => s!"movs {lo d}, #{hex k.toNat}"
  | .cmpImm n k => s!"cmp {lo n}, #{hex k.toNat}"
  | .addImm8 d k => s!"adds {lo d}, #{hex k.toNat}"
  | .subImm8 d k => s!"subs {lo d}, #{hex k.toNat}"
  | .dp .rsbs d m => s!"rsbs {lo d}, {lo m}, #0"
  | .dp .muls d m => s!"muls {lo d}, {lo m}, {lo d}"
  | .dp op d m => s!"{dpName op} {lo d}, {lo m}"
  | .movHi d m => s!"mov {regName d.val}, {regName m.val}"
  | .addPc d => s!"add {lo d}, pc"
  | .ldrLit t k => s!"ldr {lo t}, [pc, #{hex (k.toNat * 4)}] @ {hex ((pc + 4) / 4 * 4 + k.toNat * 4)}"
  | .memReg op t n m => s!"{memName op} {lo t}, [{lo n}, {lo m}]"
  | .memImm op t n k => s!"{memName op} {lo t}, {addr (lo n) (k.toNat * op.width)}"
  | .strSp t k => s!"str {lo t}, {addr "sp" (k.toNat * 4)}"
  | .ldrSp t k => s!"ldr {lo t}, {addr "sp" (k.toNat * 4)}"
  | .addRdSp d k => s!"add {lo d}, sp, #{hex (k.toNat * 4)}"
  | .addSp k => s!"add sp, #{hex (k.toNat * 4)}"
  | .subSp k => s!"sub sp, #{hex (k.toNat * 4)}"
  | .uxth d m => s!"uxth {lo d}, {lo m}"
  | .rev d m => s!"rev {lo d}, {lo m}"
  | .push l lr => s!"push {regList l (if lr then some "lr" else none)}"
  | .pop l pc' => s!"pop {regList l (if pc' then some "pc" else none)}"
  | .stm n l => s!"stm {lo n}!, {regList l none}"
  | .ldm n l => s!"ldm {lo n}{if l.getLsbD n.val then "" else "!"}, {regList l none}"
  | .bcond c k => s!"b{condName c.toNat} {target pc (k ++ 0#1)}"
  | .b k => s!"b {target pc (k ++ 0#1)}"
  | .bl k => s!"bl {target pc k}"

/-- One line per instruction: offset, tab, text. -/
def listingOf (bytes : List (BitVec 8)) (codeRanges : List (Nat × Nat)) : String :=
  match sweepOf bytes codeRanges with
  | .error e => s!"error: {e}\n"
  | .ok is => String.join (is.map fun (off, i) => s!"{hex off}\t{render off i}\n")

def listing : String := listingOf Release.bytes Release.codeRanges

end M0Crypto.Thumb.Listing
