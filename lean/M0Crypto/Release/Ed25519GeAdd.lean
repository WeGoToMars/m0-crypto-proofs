import M0Crypto.Release.Ed25519FieldSeq

set_option linter.unusedSimpArgs false

/-!
# The `ge_add` macro on frame slots

`ge_add(g, f, r, e, t, cached=False, neg)` of the generator: `t = r ± e` for a point `r`
(`X, Y, Z, T`) and a niels entry `e` (`y+x`, `y−x`, `2dxy`), ten field calls on frame slots
through `A`-`D` (`geAdd`). `ge_add_run` is its rule for any slots, callees, `neg` and offset, by
`fops_run`: the continuation receives the four result slots congruent to the formulas of
`AddPost`, and the memory equal outside the written slots and the callees' window below `sp`.
-/

namespace M0Crypto.Release.Ed25519GeAdd

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Ed25519FieldSeq
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- The slots of one `ge_add`: inputs `r`, `e`, results `t`, temporaries `A`-`D`. -/
inductive Sl where
  | rx | ry | rz | rt | ep | em | e2 | tx | ty | tz | tt | A | B | C | D
  deriving DecidableEq

def Sl.all : List Sl := [.rx, .ry, .rz, .rt, .ep, .em, .e2, .tx, .ty, .tz, .tt, .A, .B, .C, .D]

/-- `fe_sub` if `b`, else `fe_add`. -/
def zop (b : Bool) : FOp := if b then .sub else .add

/-- The ten calls of `ge_add`. -/
def geAdd (neg : Bool) : List (FCall Sl) :=
  [⟨.add, .A, .ry, .rx⟩, ⟨.sub, .B, .ry, .rx⟩, ⟨.mul, .A, .A, if neg then .em else .ep⟩,
   ⟨.mul, .B, .B, if neg then .ep else .em⟩, ⟨.mul, .C, .rt, .e2⟩, ⟨.add, .D, .rz, .rz⟩,
   ⟨.sub, .tx, .A, .B⟩, ⟨.add, .ty, .A, .B⟩, ⟨zop neg, .tz, .D, .C⟩, ⟨zop !neg, .tt, .D, .C⟩]

/-- The results of `ge_add` from the slot values `v` before and `w` after. -/
def AddPost (neg : Bool) (v w : Sl → Int) : Prop :=
  let a := (v .ry + v .rx) * v (if neg then .em else .ep)
  let b := (v .ry - v .rx) * v (if neg then .ep else .em)
  let c := v .rt * v .e2
  let d := v .rz + v .rz
  ModP (w .tx) (a - b) ∧ ModP (w .ty) (a + b) ∧ ModP (w .tz) (if neg then d - c else d + c) ∧
    ModP (w .tt) (if neg then d + c else d - c)

/-- **`ge_add` on frame slots**, for any slots `s`, callees, `neg` and offset `o`. -/
theorem ge_add_run {c : Callees} {s : Sl → Nat} {neg : Bool}
    (hT : ∀ op, Routine.TSpec (fun _ : Unit => c.R op) (fieldPub true))
    {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {t : State} {Q : State → Prop} {Ψ : TrP} {o top stW : Nat} {rest : List Piece}
    (F : Caller base sp0 N Wc) (hWc : Sub [⟨sp0 - BitVec.ofNat 32 N, N⟩] Wc)
    (hRc : Sub [codeR base, ⟨sp0 - BitVec.ofNat 32 N, N⟩] Rc) (hN : top + stW ≤ N)
    (hp : piecesAt B o (fopsP c s (geAdd neg) ++ rest) = true)
    (hok : fopsOk cs c Sl.all s top N stW o (geAdd neg) = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 top) (hcode : CodeAt t.mem base B)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + piecesSize (fopsP c s (geAdd neg))) → u.regs 13 = sp0 - BitVec.ofNat 32 top →
      CodeAt u.mem base B → MemEq (fopsW (sp0 - BitVec.ofNat 32 top) stW s (geAdd neg)) t.mem u.mem →
      AddPost neg (fun x => feVal t.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 (s x)))
        (fun x => feVal u.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 (s x))) →
      piecesAt B (o + piecesSize (fopsP c s (geAdd neg))) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (fopsTr (fun op => (hT op).T) c s base (sp0 - BitVec.ofNat 32 top) o (geAdd neg) Ψ) := by
  simp only [fopsOk, Bool.and_eq_true] at hok
  refine fops_run hT F hWc hRc hN hok.1 _ o t _ hp hok.2 hpc h13 hcode (fun _ _ => ModP.refl _)
    fun u hu h13u hcu hm hv hpu => k u hu h13u hcu hm ?_ hpu
  cases neg <;> simp only [geAdd, zop, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv <;>
    exact ⟨fops_val hv .tx, fops_val hv .ty, fops_val hv .tz, fops_val hv .tt⟩

/-! ## The instance in `m0c_ge_mul_base` -/

namespace MulBase

open M0Crypto.Artifacts
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519FeAddSub (wrap)
open M0Crypto.Release.Field25519AddSub (feAddBody feSubBody)
open M0Crypto.Release.Field25519Macros (feMulList)

/-- The frame of `m0c_ge_mul_base` as the generator allocates it: `OUT SC Q CC ROW PAD E H T N
A B C D`, in bytes. -/
def frame : List Nat := [4, 4, 4, 4, 4, 4, 64, 128, 128, 128, 32, 32, 32, 32]

/-- The offset of slot `i` of `frame`. -/
def slot (i : Nat) : Nat := (frame.take i).sum

/-- `sp` lies `push {lr}` and the frame below the entry `sp`. -/
def top : Nat := 4 + frame.sum

/-- The slots of `ge_add(g, f, H, N, T, cached=False)`. -/
def slots : Sl → Nat
  | .rx => slot 7 | .ry => slot 7 + 32 | .rz => slot 7 + 64 | .rt => slot 7 + 96
  | .ep => slot 9 | .em => slot 9 + 32 | .e2 => slot 9 + 64
  | .tx => slot 8 | .ty => slot 8 + 32 | .tz => slot 8 + 64 | .tt => slot 8 + 96
  | .A => slot 10 | .B => slot 11 | .C => slot 12 | .D => slot 13

/-- `fe_add`, `fe_sub`, `fe_mul` (`fe_mul` pushes `lr` and takes 144 bytes). -/
def callees : Callees :=
  ⟨Ed25519Compact.fe_add, seqSize (wrap feAddBody), 4, Ed25519Compact.fe_sub,
   seqSize (wrap feSubBody), 4, Ed25519Compact.fe_mul, seqSize feMulList, 148⟩

/-- The stack the instance's calls need below the entry `sp`. -/
def stack : Nat := top + 148

/-- The first offset from `o`, in 2-byte steps, `n` steps at most, where `ps` lie. -/
def findScan (ps : List Piece) : List (BitVec 8) → Nat → Nat → Option Nat
  | _, _, 0 => none
  | bs, o, n + 1 => if piecesScan bs o ps then some o else findScan ps (bs.drop 2) (o + 2) n

/-- The offset of the instance: the first match inside `m0c_ge_mul_base`. -/
def at_ : Nat :=
  (findScan (fopsP callees slots (geAdd false)) (Build.compact.bytes.drop Ed25519Compact.ge_mul_base)
    Ed25519Compact.ge_mul_base 312).getD 0

/-- The instance's pieces and call checks, in each build. -/
theorem facts (b : Build) : letI := b.codeBytes
    piecesAt b.bytes at_ (fopsP callees slots (geAdd false) ++ []) = true ∧
    fopsOk Ed25519Compact.codeRanges callees Sl.all slots top stack 148 at_ (geAdd false) = true := by
  cases b <;> exact ⟨by rw [List.append_nil, piecesAt_eq_scan]; decide +kernel, by decide +kernel⟩

end MulBase

end M0Crypto.Release.Ed25519GeAdd
