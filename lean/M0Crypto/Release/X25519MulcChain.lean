import M0Crypto.Release.X25519MulcEnds
import M0Crypto.Release.X25519Frame

set_option linter.unusedSimpArgs false

/-!
The carry chain of `m0c_fe_mulc_add` over words 0 to 6 (plan `x25519-proofs.md`, phase 8).

`Inv c q j k x`: before chain step `j`, the words `0..j-1` of `dst` hold the low words of the
chain so far, the words from `j` still read as at entry (after `push`), the carry-in is in
register `k`, and the partial sums satisfy

  `psum lo j + 2^(32 j) * k = 121666 * psum A j + psum B j + q`

where `A`, `B` are the input words and `q` the chain's carry-in (`19 * q` of the routine).
`chain_step_w` is the one generic lemma for `mulcStep`: it keeps `Inv` from `j` to `j + 1`.

Aliasing: the step reads `a[j]` and `b[j]` before it stores word `j` of `dst`, and words `≥ j`
of `dst` are untouched, so `dst = a` or `dst = b` (`Ok.dstA`, `Ok.dstB`) reads the entry
values (`read_src`); otherwise the inputs are disjoint from `dst` and the frame lemma
`FrameOk.read_disj` applies.
-/

namespace M0Crypto.Release.X25519MulcChain
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Frame (FrameOk upd)
open M0Crypto.Release.X25519MulcWord (wAddr)
open M0Crypto.Release.X25519MulcStep (sAddr SDist mulcStep_run_w)
open M0Crypto.Release.X25519Macros (mulcStep)

/-- Little-endian partial sum of `j` words. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => psum f j + 2 ^ (32 * j) * f j

theorem psum_congr {f g : Nat → Nat} : ∀ {j : Nat}, (∀ i < j, f i = g i) → psum f j = psum g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [psum]
    rw [psum_congr (fun i hi => h i (by omega)), h j (by omega)]

theorem psum_lt {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ 32) : ∀ j, psum f j < 2 ^ (32 * j)
  | 0 => by simp [psum]
  | j + 1 => by
    simp only [psum]
    have ih := psum_lt hf j
    have hj := hf j
    have : 2 ^ (32 * j) * f j + 2 ^ (32 * j) ≤ 2 ^ (32 * j) * 2 ^ 32 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    rw [show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
    omega

/-- One chain step on the partial sums. -/
theorem chain_nat (P S K L H Aj Bj SA SB q : Nat) (hinv : S + P * K = 121666 * SA + SB + q)
    (hw : L + 2 ^ 32 * H = 121666 * Aj + Bj + K) :
    S + P * L + P * 2 ^ 32 * H = 121666 * (SA + P * Aj) + (SB + P * Bj) + q := by
  grind

theorem disj_symm {a : Word} {n : Nat} {b : Word} {m : Nat} (h : Disj a n b m) : Disj b m a n :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- The fixed data of the chain: the pointers, the memory after `push`, and the values of
the registers the chain does not touch. -/
structure Ctx where
  dst : Word
  a : Word
  b : Word
  m0 : Mem
  m1 : Mem
  r8 : Word
  sp : Word

namespace Ctx
variable (c : Ctx)
/-- Input word `i` of `a`, as at entry. -/
def A (i : Nat) : Nat := (read32 c.m0 (slot c.a i)).toNat
/-- Input word `i` of `b`, as at entry. -/
def B (i : Nat) : Nat := (read32 c.m0 (slot c.b i)).toNat
end Ctx

/-- The hypotheses on the chain's data. -/
structure Ok (c : Ctx) : Prop where
  a4 : c.a.toNat % 4 = 0
  b4 : c.b.toNat % 4 = 0
  dst4 : c.dst.toNat % 4 = 0
  fits : c.dst.toNat + 32 ≤ 2 ^ 32
  dstA : c.dst = c.a ∨ Disj c.dst 32 c.a 32
  dstB : c.dst = c.b ∨ Disj c.dst 32 c.b 32
  /-- `push` did not change the inputs. -/
  ra : ∀ i < 8, read32 c.m1 (slot c.a i) = read32 c.m0 (slot c.a i)
  rb : ∀ i < 8, read32 c.m1 (slot c.b i) = read32 c.m0 (slot c.b i)

/-- The state before chain step `j`, with carry-in `q` and the carry in register `k`. -/
structure Inv (c : Ctx) (q j : Nat) (k : LowReg) (x : State) : Prop where
  r1 : x.reg 1 = c.a
  r2 : x.reg 2 = c.b
  r6 : x.reg 6 = 0#32
  r7 : x.reg 7 = 60833#32
  r8 : x.regs 8 = c.r8
  r12 : x.regs 12 = c.dst
  r13 : x.regs 13 = c.sp
  frame : ∃ F, FrameOk c.dst 8 c.m1 F x.mem ∧
    (∀ i, j ≤ i → i < 8 → F i = read32 c.m1 (slot c.dst i)) ∧
    psum (fun i => (F i).toNat) j + 2 ^ (32 * j) * (x.reg k).toNat =
      121666 * psum c.A j + psum c.B j + q

/-- A word of an input not yet overwritten reads as at entry. -/
theorem read_src {dst p : Word} {m1 m : Mem} {F : Nat → Word} {j i : Nat}
    (h : FrameOk dst 8 m1 F m) (hF : ∀ i, j ≤ i → i < 8 → F i = read32 m1 (slot dst i))
    (hp : dst = p ∨ Disj dst 32 p 32) (hji : j ≤ i) (hi : i < 8) :
    read32 m (slot p i) = read32 m1 (slot p i) := by
  rcases hp with rfl | hd
  · rw [h.slots i hi, hF i hji hi]
  · exact h.read_disj (disj_symm hd) (by omega)

theorem wAddr_slot (x : State) (n : LowReg) (i : Nat) (hi : i < 32) :
    wAddr x n i = slot (x.reg n) i := by
  simp only [wAddr, slot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mul_comm i 4]

theorem sAddr_slot (x : State) (i : Nat) (hi : i < 32) : sAddr x i = slot (x.regs 12) i := by
  simp only [sAddr, slot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mul_comm i 4]

theorem lo_ne (r : Reg) (hr : 8 ≤ r.val) (x : LowReg) : r ≠ x.toReg := fun e => by
  have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega

/-- Chain step `j` (`mulcStep j k a`) keeps the invariant: from `Inv … j k` to
`Inv … (j + 1) a`. -/
theorem chain_step_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off j q : Nat} {k a : LowReg} {c : Ctx} (hc : Ok c) (hd : SDist k a) (hj : j < 7)
    (hseq : seqAt B off (mulcStep j k a) = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (mulcStep j k a)))
    (hW : ∀ i < 8, ∀ q < 4, Wr (slot c.dst i + BitVec.ofNat 32 q))
    (hi : Inv c q j k x) {Q : State → Prop}
    (cont : ∀ y : State, y.pc = base + BitVec.ofNat 32 (off + seqSize (mulcStep j k a)) →
      Inv c q (j + 1) a y → ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  obtain ⟨r1, r2, r6, r7, r8, r12, r13, F, hF, hFs, hv⟩ := hi
  have sa := sAddr_slot x j (by omega)
  rw [r12] at sa
  refine mulcStep_run_w hb hd hseq ho hpc hr (by rw [r1]; exact hc.a4) (by rw [r2]; exact hc.b4)
    (by rw [r12]; exact hc.dst4) r6 r7 (fun q hq => by rw [sa]; exact hW j (by omega) q hq) ?_
  intro y L hpy hL hm ho'
  have hd' := hd
  simp only [SDist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd'
  obtain ⟨-, ⟨-, -, a1, a2, a6, a7⟩, -⟩ := hd'
  have keep : ∀ x' : LowReg, x' ≠ a → x' ≠ 4 → x' ≠ 5 → y.reg x' = x.reg x' := fun x' h1 h2 h3 =>
    ho' x'.toReg (toReg_ne_15 x') (by rw [ne_eq, X25519Mul.toReg_inj]; exact h1)
      (by rw [ne_eq, show (4 : Reg) = LowReg.toReg 4 from rfl, X25519Mul.toReg_inj]; exact h2)
      (by rw [ne_eq, show (5 : Reg) = LowReg.toReg 5 from rfl, X25519Mul.toReg_inj]; exact h3)
  have keepH : ∀ r : Reg, 8 ≤ r.val → r ≠ 15 → y.regs r = x.regs r := fun r h8 h15 =>
    ho' r h15 (lo_ne r h8 a) (lo_ne r h8 4) (lo_ne r h8 5)
  -- the two inputs read as at entry
  have rA : read32 x.mem (wAddr x 1 j) = read32 c.m0 (slot c.a j) := by
    rw [wAddr_slot x 1 j (by omega), r1, read_src hF hFs hc.dstA (Nat.le_refl j) (by omega),
      hc.ra j (by omega)]
  have rB : read32 x.mem (wAddr x 2 j) = read32 c.m0 (slot c.b j) := by
    rw [wAddr_slot x 2 j (by omega), r2, read_src hF hFs hc.dstB (Nat.le_refl j) (by omega),
      hc.rb j (by omega)]
  rw [rA, rB] at hL
  refine cont y hpy ⟨by rw [keep 1 (Ne.symm a1) (by decide) (by decide), r1],
    by rw [keep 2 (Ne.symm a2) (by decide) (by decide), r2],
    by rw [keep 6 (Ne.symm a6) (by decide) (by decide), r6],
    by rw [keep 7 (Ne.symm a7) (by decide) (by decide), r7],
    by rw [keepH 8 (by decide) (by decide), r8], by rw [keepH 12 (by decide) (by decide), r12],
    by rw [keepH 13 (by decide) (by decide), r13], upd F j [L], ?_, ?_, ?_⟩
  · rw [hm, sa]; exact hF.write (by omega) L
  · intro i hji hi8
    simp only [upd, List.length_singleton]
    rw [ite_eq_right_iff.mpr (fun h => by omega)]
    exact hFs i (by omega) hi8
  · have e1 : psum (fun i => (upd F j [L] i).toNat) j = psum (fun i => (F i).toNat) j :=
      psum_congr fun i hi => by simp only [upd, List.length_singleton]; rw [ite_eq_right_iff.mpr (fun h => by omega)]
    have e2 : (upd F j [L] j).toNat = L.toNat := by simp [upd]
    simp only [psum, e1, e2]
    rw [show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
    exact chain_nat _ _ _ _ _ _ _ _ _ _ hv hL

end M0Crypto.Release.X25519MulcChain
