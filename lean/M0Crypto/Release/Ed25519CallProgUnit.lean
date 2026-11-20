import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.RoutinePieces

/-!
# Call programs: the unit's call graph

The generator's call graph as data: each function of the unit with its own stack bytes (`push`
and `sub sp` before its first `add sp`) and its direct callees, as `asm.py`'s `stack_depths`
computes them, checked against the decoded final bytes of both builds (`unit_ok`). From it, every routine's **transitive code footprint** (its body and its callees'
bodies) and **stack depth** are derived, so no contract names the unit's whole code range and
no stack bound is a literal. A body runs from the function's offset to the next label of
`Build.compactOffsets`; both builds have the same offsets and the same table (`offsets_same`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Release.Ed25519
open M0Crypto.Artifacts.Ed25519Compact
open M0Crypto.Thumb

/-- A function of the unit: offset, own stack bytes, direct callees (offsets). -/
structure Fn where
  off : Nat
  own : Nat
  calls : List Nat

/-- The unit's functions (`stack_depths` of the generated unit; the same in both builds). -/
def unitFns : List Fn :=
  [⟨fe_mul, 148, []⟩, ⟨fe_sqr, 148, []⟩, ⟨fe_add, 4, []⟩, ⟨fe_sub, 4, []⟩, ⟨fe_canon, 4, []⟩,
   ⟨fe_eq, 4, []⟩, ⟨cmov, 4, []⟩, ⟨copy, 4, []⟩, ⟨zero, 4, []⟩,
   ⟨fe_pow, 204, [copy, fe_mul, fe_sqr]⟩, ⟨fe_inv, 384, [fe_inv_shared]⟩,
   ⟨inv_canon, 0, []⟩, ⟨inv_sub, 0, []⟩, ⟨inv_select, 0, []⟩,
   ⟨fe_inv_shared, 0, [inv_canon, inv_matrix, inv_row_exact, inv_row_mod, inv_fold, inv_sub, inv_select]⟩,
   ⟨inv_matrix, 0, []⟩, ⟨inv_row_exact, 0, []⟩, ⟨inv_row_mod, 0, []⟩, ⟨inv_fold, 0, []⟩,
   ⟨sha512_block, 208, []⟩, ⟨sha512_init, 4, []⟩,
   ⟨sha512_update, 16, [sha512_block]⟩, ⟨sha512_final, 12, [sha512_block]⟩, ⟨mp_mul, 24, []⟩,
   ⟨sc_reduce, 228, [cmov, copy, mp_mul]⟩, ⟨sc_muladd, 76, [mp_mul, sc_reduce]⟩,
   ⟨ge_compress, 108, [fe_canon, fe_mul, fe_inv]⟩,
   ⟨ge_decompress, 300, [copy, fe_add, fe_canon, fe_eq, fe_mul, fe_pow, fe_sqr, fe_sub]⟩,
   ⟨sc_recode_comb, 44, []⟩, ⟨ge_lookup, 60, [cmov, fe_sub]⟩,
   ⟨ge_mul_base, 604, [cmov, copy, fe_add, fe_mul, fe_sqr, fe_sub, ge_lookup, sc_recode_comb, zero]⟩,
   ⟨sbit, 4, []⟩, ⟨sc_wnaf, 36, [sbit, zero]⟩,
   ⟨ge_dsm, 692, [copy, fe_add, fe_mul, fe_sqr, fe_sub, zero]⟩,
   ⟨ed25519_pubkey, 308, [ge_compress, ge_mul_base, sha512_final, sha512_init, sha512_update]⟩,
   ⟨ed25519_sign, 508, [ge_compress, ge_mul_base, sc_muladd, sc_reduce, sha512_final, sha512_init,
     sha512_update]⟩,
   ⟨ed25519_verify, 924, [ge_decompress, ge_dsm, ge_compress, bytes_diff32, r_encoding_check, sc_reduce, sc_wnaf,
     sha512_final, sha512_init, sha512_update]⟩,
   ⟨bytes_diff32, 0, []⟩,
   ⟨r_encoding_check, 0, []⟩]

def fnAt (o : Nat) : Option Fn := unitFns.find? (·.off == o)

/-- The end of the body at `o`: the next label. -/
def fnEnd (o : Nat) : Nat := ((compactOffsets.filter (o < ·)).min?).getD size

/-- Functions reachable from `o` (fuel `n`), `o` first. -/
def reach : Nat → Nat → List Nat
  | 0, o => [o]
  | n + 1, o => o :: ((fnAt o).map fun f => f.calls.flatMap (reach n)).getD []

/-- **The transitive code footprint** of the function at `o`: its body and its callees'. -/
def footprint (o : Nat) : List (Nat × Nat) :=
  ((reach unitFns.length o).eraseDups).map fun x => (x, fnEnd x)

/-- **The stack depth** of the function at `o`: own bytes plus its deepest callee's. -/
def depth : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, o => match fnAt o with
    | some f => f.own + (f.calls.map (depth n)).foldl max 0
    | none => 0

def stackOf (o : Nat) : Nat := depth unitFns.length o

/-! ## The table from the bytes -/

/-- Why a function's bytes disagree with its `unitFns` row: an undecodable halfword, a body
longer than its fuel, or the own stack bytes or callees the bytes give. -/
inductive UnitErr where
  | noDecode
  | fuel
  | own (bytes : Nat)
  | calls (bytes : List Nat)
  deriving Repr

/-- A body's facts from its bytes `bs` at `o` up to `e`, data ranges `D` skipped: the bytes of
the prologue's `push`, `sub sp` and high-register copies, and the `bl` targets. -/
def walk (D : List (Nat × Nat)) (e : Nat) : Nat → List (BitVec 8) → Nat → Bool → Nat → List Nat →
    Except (Nat × UnitErr) (Nat × List Nat)
  | 0, _, o, _, _, _ => .error (o, .fuel)
  | n + 1, bs, o, pro, own, cs =>
    if e ≤ o then .ok (own, cs) else
    match D.find? (·.1 == o) with
    | some (_, d) => walk D e n (bs.drop (d - o)) d false own cs
    | none =>
      match decode (hwAt bs 0) (hwAt bs 2) with
      | none => .error (o, .noDecode)
      | some i =>
        let (pro', own') : Bool × Nat := match i with
          | .push l lr => (pro, if pro then own + 4 * (bitCount l + lr.toNat) else own)
          | .subSp k => (pro, if pro then own + 4 * k.toNat else own)
          | .movHi _ _ => (pro, own)
          | _ => (false, own)
        let cs' := match i with
          | .bl imm => if cs.contains (blTarget o imm).toNat then cs else cs ++ [(blTarget o imm).toNat]
          | _ => cs
        walk D e n (bs.drop i.size) (o + i.size) pro' own' cs'

/-- **The first function whose bytes disagree with its row**, with the offset and the reason. -/
def unitErr (b : Build) : Option (Nat × UnitErr) :=
  unitFns.findSome? fun f =>
    match walk b.dataRanges (fnEnd f.off) (fnEnd f.off - f.off) (b.bytes.drop f.off) f.off true 0 [] with
    | .error e => some e
    | .ok (own, cs) =>
      if own != f.own then some (f.off, .own own)
      else if !(cs.all f.calls.contains && f.calls.all cs.contains) then some (f.off, .calls cs)
      else none

/-- **The table is the bytes'**: own stack bytes and callees, both builds. -/
theorem unit_ok (b : Build) : (unitErr b).isNone = true := by cases b <;> decide +kernel

end M0Crypto.Release.Ed25519CallProg
