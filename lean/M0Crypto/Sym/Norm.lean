import M0Crypto.Sym.Access

/-!
# Symbolic executor, layer 3: the normaliser

`norm : SExpr → SExpr` rewrites the mirror syntax produced by `symExec` towards a
canonical form, with `norm_sound : (norm e).denote s0 = e.denote s0`. Every rule is a
separate function with its own soundness lemma; `norm` only composes them bottom-up.
All functions are structurally recursive, so the kernel evaluates them (`decide`, `rfl`).

Rules:
* `addK` — constant folding and re-association of `x + k` chains (`k` constant);
* `rdW` — read-over-write for 32-bit loads through 32-bit stores whose addresses have the
  same symbolic base and constant offsets (`sp + k` style): equal offsets return the
  stored value; offsets at least 4 apart (mod 2^32, both directions) skip the store.

* `awcK` — carry chains with a constant carry: carry `0` is `addK`; `a + ~b + 1` is `a - b`;
  `a + k + 1` folds into the constant chain;
* `rorK` — rotate-right by a constant amount not a multiple of 32 becomes `rotl` (left
  rotation by `32 - k % 32`).

Addresses are compared through `split e = (x, k)` with `e = x + k`. This decides the
stack slots and buffer offsets the release code uses; anything else is left unresolved
(sound, just less simplified).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 write32_other read32_write32_same)
open M0Crypto.Thumb

deriving instance DecidableEq for SExpr, SBool, SMem

/-! ## Base + constant offset -/

/-- `split e = (x, k)` with `x + k = e`, peeling constant addends. -/
def split : SExpr → SExpr × Word
  | .add x (.const k) => ((split x).1, (split x).2 + k)
  | .const k => (.const 0#32, k)
  | e => (e, 0#32)

theorem split_sound (s0 : State) : ∀ e : SExpr, (split e).1.denote s0 + (split e).2 = e.denote s0
  | .add x (.const k) => by
    simp only [split, SExpr.denote]
    rw [← BitVec.add_assoc, split_sound s0 x]
  | .const k => by simp [split, SExpr.denote]
  | .reg0 _ | .add _ (.reg0 _) | .add _ (.add _ _) | .add _ (.sub _ _) | .add _ (.and _ _)
  | .add _ (.or _ _) | .add _ (.xor _ _) | .add _ (.not _) | .add _ (.mul _ _)
  | .add _ (.uxth _) | .add _ (.awc _ _ _) | .add _ (.lsl _ _) | .add _ (.lsr _ _)
  | .add _ (.ror _ _ _) | .add _ (.ld32 _ _) | .add _ (.ld16 _ _) | .add _ (.ld8 _ _)
  | .add _ (.rotl _ _)
  | .sub _ _ | .and _ _ | .or _ _ | .xor _ _ | .not _ | .mul _ _ | .uxth _ | .awc _ _ _
  | .lsl _ _ | .lsr _ _ | .ror _ _ _ | .ld32 _ _ | .ld16 _ _ | .ld8 _ _ | .rotl _ _ => by
    simp [split]

/-- Rebuild `x + k`, dropping `+ 0` and folding constants. -/
def mkAdd (x : SExpr) (k : Word) : SExpr :=
  match x with
  | .const j => .const (j + k)
  | _ => if k = 0#32 then x else .add x (.const k)

theorem mkAdd_sound (s0 : State) (x : SExpr) (k : Word) :
    (mkAdd x k).denote s0 = x.denote s0 + k := by
  unfold mkAdd
  split
  · rfl
  · split
    · rename_i h; subst h; simp
    · rfl

/-- `a + b` with `b` constant: fold into the constant chain of `a`. -/
def addK (a b : SExpr) : SExpr :=
  match b with
  | .const k => mkAdd (split a).1 ((split a).2 + k)
  | _ => .add a b

theorem addK_sound (s0 : State) (a b : SExpr) : (addK a b).denote s0 = a.denote s0 + b.denote s0 := by
  unfold addK
  split
  · rw [mkAdd_sound, ← BitVec.add_assoc, split_sound]; rfl
  · rfl

/-! ## Read over write -/

/-- Two 4-byte ranges at `b` and `a` with `a - b` in `[4, 2^32 - 4]` do not overlap. -/
theorem read32_write32_far (m : Mem) (a b v : Word)
    (h : 4 ≤ (a - b).toNat ∧ (a - b).toNat ≤ 2 ^ 32 - 4) : read32 (write32 m b v) a = read32 m a := by
  have ne : ∀ j < 4, ∀ k < 4, a + BitVec.ofNat 32 j ≠ b + BitVec.ofNat 32 k := by
    intro j hj k hk he
    have : a - b = BitVec.ofNat 32 k - BitVec.ofNat 32 j := by bv_omega
    rw [this, BitVec.toNat_sub] at h
    simp only [BitVec.toNat_ofNat] at h
    omega
  have w : ∀ j < 4, write32 m b v (a + BitVec.ofNat 32 j) = m (a + BitVec.ofNat 32 j) :=
    fun j hj => write32_other m b v _ (ne j hj)
  have w0 := w 0 (by decide); have w1 := w 1 (by decide)
  have w2 := w 2 (by decide); have w3 := w 3 (by decide)
  simp only [BitVec.add_zero] at w0 w1 w2 w3
  simp only [read32]
  rw [w0, w1, w2, w3]

/-! ## Carry chains and rotations -/

theorem awc_false (x y : Word) : (Armv6M.addWithCarry x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq; simp [Armv6M.addWithCarry, BitVec.toNat_add]

theorem awc_true (x y : Word) : (Armv6M.addWithCarry x y true).1 = x + y + 1 := by
  apply BitVec.eq_of_toNat_eq; simp [Armv6M.addWithCarry, BitVec.toNat_add, Nat.mod_add_mod]

theorem awc_not_true (x y : Word) : (Armv6M.addWithCarry x (~~~y) true).1 = x - y := by
  rw [awc_true]; bv_omega

/-- Carry-chain rule. A constant carry `false` is a plain sum (`addK`); carry `true` with
`b = ~~~b'` is `a - b'` (`a + ~b' + 1`); carry `true` with `b = k` folds into the constant
chain as `a + (k + 1)`. Anything else stays `awc`. -/
def awcK (a b : SExpr) (c : SBool) : SExpr :=
  match c with
  | .const false => addK a b
  | .const true =>
    match b with
    | .not b' => .sub a b'
    | .const k => addK a (.const (k + 1))
    | _ => .awc a b (.const true)
  | _ => .awc a b c

theorem awcK_sound (s0 : State) (a b : SExpr) (c : SBool) :
    (awcK a b c).denote s0 = (Armv6M.addWithCarry (a.denote s0) (b.denote s0) (c.denote s0)).1 := by
  unfold awcK
  split
  · simp only [addK_sound, SBool.denote, awc_false]
  · split
    · simp only [SExpr.denote, SBool.denote, awc_not_true]
    · simp only [addK_sound, SExpr.denote, SBool.denote]
      rw [awc_true, BitVec.add_assoc]
    · rfl
  · rfl

/-- Rotate-right by `k` with `k % 32 ≠ 0` is the left rotation by `32 - k % 32`; the carry-in
is unused. -/
theorem rorC_rotl (x k : Word) (c : Bool) (h : k.toNat % 32 ≠ 0) :
    (Armv6M.rorC x (k.toNat % 256) c).1 = M0Crypto.Spec.ChaCha20.rotl x (32 - k.toNat % 32) := by
  have h1 : k.toNat % 256 ≠ 0 := by omega
  have hm : k.toNat % 256 % 32 = k.toNat % 32 := by omega
  have e : 32 - (32 - k.toNat % 32) = k.toNat % 32 := by omega
  simp only [Armv6M.rorC, h1, ↓reduceIte, hm, M0Crypto.Spec.ChaCha20.rotl, e]
  exact BitVec.or_comm _ _

/-- Rotation rule. A constant rotation whose amount is a multiple of 32 is kept; any other
constant amount becomes the left rotation `rotl a (32 - k % 32)`. -/
def rorK (a b : SExpr) (c : SBool) : SExpr :=
  match b with
  | .const k => if k.toNat % 32 = 0 then .ror a b c else .rotl a (32 - k.toNat % 32)
  | _ => .ror a b c

theorem rorK_sound (s0 : State) (a b : SExpr) (c : SBool) :
    (rorK a b c).denote s0 = (Armv6M.rorC (a.denote s0) ((b.denote s0).toNat % 256) (c.denote s0)).1 := by
  unfold rorK
  split
  · split
    · rfl
    · rename_i hk
      simp only [SExpr.denote]
      exact (rorC_rotl _ _ _ hk).symm
  · rfl

/-! ## The normaliser -/

-- `norm` and `rdW` are mutual: loads are resolved through `rdW` against the stores in their
-- memory, and a load that hits an equal store returns the normalised stored value.
mutual

/-- Bottom-up normalisation of word syntax. -/
def norm : SExpr → SExpr
  | .add a b => addK (norm a) (norm b)
  | .sub a b => .sub (norm a) (norm b)
  | .and a b => .and (norm a) (norm b)
  | .or a b => .or (norm a) (norm b)
  | .xor a b => .xor (norm a) (norm b)
  | .not a => .not (norm a)
  | .mul a b => .mul (norm a) (norm b)
  | .uxth a => .uxth (norm a)
  | .awc a b c => awcK (norm a) (norm b) c
  | .lsl a n => .lsl (norm a) n
  | .lsr a n => .lsr (norm a) n
  | .ror a b c => rorK (norm a) (norm b) c
  | .rotl a n => .rotl (norm a) n
  | .ld32 m a => rdW m (norm a)
  | .ld16 m a => .ld16 m (norm a)
  | .ld8 m a => .ld8 m (norm a)
  | e => e

/-- `ld32 m a`, looking through stores to provably equal or disjoint addresses. An equal
store gives its value, normalised; a disjoint store is skipped. -/
def rdW : SMem → SExpr → SExpr
  | .w32 m b v, a =>
    if (split a).1 = (split b).1 then
      if (split a).2 - (split b).2 = 0#32 then norm v
      else if 4 ≤ ((split a).2 - (split b).2).toNat ∧ ((split a).2 - (split b).2).toNat ≤ 2 ^ 32 - 4
      then rdW m a
      else .ld32 (.w32 m b v) a
    else .ld32 (.w32 m b v) a
  | m, a => .ld32 m a

end

mutual

theorem norm_sound (s0 : State) : ∀ e : SExpr, (norm e).denote s0 = e.denote s0
  | .add a b => by simp only [norm, addK_sound, norm_sound s0 a, norm_sound s0 b, SExpr.denote]
  | .ld32 m a => by
    simp only [norm, SExpr.denote, rdW_sound s0 m (norm a), norm_sound s0 a]
  | .sub a b | .and a b | .or a b | .xor a b | .mul a b => by
    simp only [norm, SExpr.denote, norm_sound s0 a, norm_sound s0 b]
  | .awc a b c => by simp only [norm, awcK_sound, SExpr.denote, norm_sound s0 a, norm_sound s0 b]
  | .ror a b c => by simp only [norm, rorK_sound, SExpr.denote, norm_sound s0 a, norm_sound s0 b]
  | .not a | .uxth a | .lsl a _ | .lsr a _ | .ld16 _ a | .ld8 _ a | .rotl a _ => by
    simp only [norm, SExpr.denote, norm_sound s0 a]
  | .reg0 _ | .const _ => rfl

theorem rdW_sound (s0 : State) : ∀ (m : SMem) (a : SExpr),
    (rdW m a).denote s0 = read32 (m.denote s0) (a.denote s0)
  | .w32 m b v, a => by
    have ha := split_sound s0 a
    have hb := split_sound s0 b
    unfold rdW
    split
    · rename_i hx
      split
      · rename_i hk
        simp only [SMem.denote]
        have : a.denote s0 = b.denote s0 := by
          rw [← ha, ← hb, hx, BitVec.sub_eq_iff_eq_add.mp hk, BitVec.zero_add]
        rw [norm_sound s0 v, this, read32_write32_same]
      · split
        · rename_i _ hd
          rw [rdW_sound s0 m a]
          simp only [SMem.denote]
          rw [read32_write32_far]
          rw [← ha, ← hb, hx]
          have : (split b).1.denote s0 + (split a).2 - ((split b).1.denote s0 + (split b).2) =
              (split a).2 - (split b).2 := by
            bv_omega
          rw [this]; exact hd
        · rfl
    · rfl
  | .mem0, _ | .w16 _ _ _, _ | .w8 _ _ _, _ => rfl

end

/-! ## Bridge: registers after a straight-line block -/

theorem sound_all {is : List Instr} (hf : is.all Instr.falls = true) : ∀ i ∈ is, Sound i :=
  fun i hi => sound_of_falls i (List.all_eq_true.mp hf i hi)

/-- The value of register `r` after the straight-line block `is` is the normalised
symbolic value, read in the initial state. Typical use: `rw [execAll_regs_norm _ hf]`,
then evaluate `norm (...)` by `decide`/`rfl` to a small closed syntax tree. -/
theorem execAll_regs_norm (is : List Instr) (hf : is.all Instr.falls = true) (s : State) (r : Reg) :
    (execAll is s).regs r = (norm ((symExec is SState.init).regs r)).denote s := by
  rw [norm_sound, ← denote_regs, symExec_sound is (sound_all hf), SState.init_denote]

/-! ## Worked example: a store/store/load sequence on the stack

`str r0, [sp, #12]; str r1, [sp, #20]; ldr r2, [sp, #12]` leaves `r0` in `r2`. The
normaliser resolves the load through both stores (skip the one 8 bytes away, hit the
equal one); the kernel computes this by `decide`. -/

def demoBlock : List Instr := [.strSp 0 3, .strSp 1 5, .ldrSp 2 3]

theorem demo_norm : norm ((symExec demoBlock SState.init).regs 2) = .reg0 0 := by decide

theorem demo (s : State) : (execAll demoBlock s).regs 2 = s.regs 0 := by
  rw [execAll_regs_norm _ (by decide), demo_norm]; rfl

end M0Crypto.Sym
