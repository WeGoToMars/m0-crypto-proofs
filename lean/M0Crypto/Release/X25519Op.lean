import M0Crypto.Release.X25519Call
import M0Crypto.Release.X25519Layout

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
Field operations on frame slots of `m0c_x25519`.

An operation `op fn d a b` of the generator is `add r0, sp, #d; add r1, sp, #a;
[add r2, sp, #b;]` followed by an inline body or a `bl` to a routine. `opCall o tgt d a b`
is the call form at code offset `o`, with the `bl` offset computed from `o` (`blTo`).

`Body c m1 t` is the state of the entry body between operations: SP is `E c`, and memory
outside the scratch bytes `[c.fp, c.fp + wipeBytes)` equals `m1`, the memory after the
prologue. `op_call_w` runs one call operation: the destination slot gets `f a b` modulo p,
the rest of the frame is unchanged, and `Body` is kept.
-/

namespace M0Crypto.Release.X25519Op
open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Block (Runs Runs.reg)
open M0Crypto.Release.X25519Routines (Call Pre Post feVal)
open M0Crypto.Release.X25519Call
open M0Crypto.Release.X25519Layout

/-! ## Branch offsets -/

theorem bl_target (q t : Nat) (hq : q + 4 < 2 ^ 23) (ht : t < 2 ^ 23) :
    BitVec.ofNat 32 q + 4#32 + (BitVec.ofInt 25 ((t : Int) - (q + 4))).signExtend 32 =
      BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt,
    BitVec.toInt_ofNat', BitVec.toInt_ofNat', BitVec.toInt_ofNat']
  have e1 : ((q : Int)).bmod (2 ^ 32) = q := Int.bmod_eq_of_le (by omega) (by omega)
  have e2 : ((t : Int) - (q + 4)).bmod (2 ^ 25) = (t : Int) - (q + 4) :=
    Int.bmod_eq_of_le (by omega) (by omega)
  have e3 : ((t : Int)).bmod (2 ^ 32) = t := Int.bmod_eq_of_le (by omega) (by omega)
  have e4 : ((q : Int) + 4).bmod (2 ^ 32) = q + 4 := Int.bmod_eq_of_le (by omega) (by omega)
  have e5 : (((4 : Nat) : Int)).bmod (2 ^ 32) = 4 := by decide
  rw [e1, e5, e4, e2, show (q : Int) + 4 + ((t : Int) - (q + 4)) = t by omega, e3]

/-- `bl` at offset `q` to offset `t`. -/
def blTo (q t : Nat) : Instr := .bl (BitVec.ofInt 25 ((t : Int) - (q + 4)))

/-! ## Operation lists -/

/-- `add r0, sp, #d; add r1, sp, #a; [add r2, sp, #b]`. -/
def opPre (d a : Nat) (b : Option Nat) : List Instr :=
  .addRdSp 0 (BitVec.ofNat 8 (d / 4)) :: .addRdSp 1 (BitVec.ofNat 8 (a / 4)) ::
    match b with
    | some b => [.addRdSp 2 (BitVec.ofNat 8 (b / 4))]
    | none => []

/-- A call operation at code offset `o` to the routine at offset `tgt`. -/
def opCall (o tgt d a : Nat) (b : Option Nat) : List Instr :=
  opPre d a b ++ [blTo (o + seqSize (opPre d a b)) tgt]

theorem opPre_size (d a : Nat) (b : Option Nat) : seqSize (opPre d a b) ≤ 6 := by
  cases b <;> simp [opPre, seqSize, Instr.size]

theorem opPre_falls (d a : Nat) (b : Option Nat) : (opPre d a b).all Instr.falls = true := by
  cases b <;> rfl

theorem opPre_reg (d a : Nat) (b : Option Nat) :
    (opPre d a b).all X25519Mul.regOnly = true ∧ (opPre d a b).all (!·.writesMem) = true := by
  cases b <;> exact ⟨rfl, rfl⟩

/-- Second operand address after the prefix: a slot, or `r2` unchanged. -/
def bAddr (sp : Word) (r2 : Word) : Option Nat → Word
  | some b => sp + BitVec.ofNat 32 b
  | none => r2

theorem opPre_exec (s : State) (d a : Nat) (b : Option Nat) (hd : d % 4 = 0 ∧ d < 1024)
    (ha : a % 4 = 0 ∧ a < 1024) (hb : ∀ x, b = some x → x % 4 = 0 ∧ x < 1024) :
    let t := execAll (opPre d a b) s
    t.regs 0 = s.sp + BitVec.ofNat 32 d ∧ t.regs 1 = s.sp + BitVec.ofNat 32 a ∧
      t.regs 2 = bAddr s.sp (s.regs 2) b ∧ t.mem = s.mem ∧
      ∀ r : Reg, 3 ≤ r.val → r ≠ 15 → t.regs r = s.regs r := by
  have k4 : ∀ x, x % 4 = 0 → x < 1024 → x / 4 % 256 * 4 = x := fun x h1 h2 => by omega
  cases b with
  | none =>
    refine ⟨?_, ?_, ?_, rfl, fun r h3 h15 => ?_⟩
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, k4 d hd.1 hd.2]
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, k4 a ha.1 ha.2]
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, bAddr]
    · have h0 : r ≠ LowReg.toReg 0 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
      have h1 : r ≠ LowReg.toReg 1 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
      simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, h0, h1, h15]
  | some x =>
    have hx := hb x rfl
    refine ⟨?_, ?_, ?_, rfl, fun r h3 h15 => ?_⟩
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, k4 d hd.1 hd.2]
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, k4 a ha.1 ha.2]
    · simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
        X25519Mem.toReg1, X25519Mem.toReg2, bAddr, k4 x hx.1 hx.2]
    · have h0 : r ≠ LowReg.toReg 0 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
      have h1 : r ≠ LowReg.toReg 1 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
      have h2 : r ≠ LowReg.toReg 2 := fun e => by rw [e] at h3; exact absurd h3 (by decide)
      simp [opPre, execAll, Instr.next, Instr.exec, State.setReg, h0, h1, h2, h15]


theorem region_iff {a y : Word} {n : Nat} (h : a.toNat + n ≤ 2 ^ 32) :
    Region a n y ↔ a.toNat ≤ y.toNat ∧ y.toNat < a.toNat + n := by
  show (y - a).toNat < n ↔ _
  rw [BitVec.toNat_sub]
  have := y.isLt; have := a.isLt
  constructor
  · intro h1
    by_cases hy : a.toNat ≤ y.toNat
    · omega
    · exfalso
      have : (2 ^ 32 - a.toNat + y.toNat) % 2 ^ 32 = 2 ^ 32 - a.toNat + y.toNat := Nat.mod_eq_of_lt (by omega)
      omega
  · intro ⟨h1, h2⟩
    have : (2 ^ 32 - a.toNat + y.toNat) % 2 ^ 32 = y.toNat - a.toNat := by
      rw [show 2 ^ 32 - a.toNat + y.toNat = (y.toNat - a.toNat) + 2 ^ 32 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    omega

theorem region_sub {a b y : Word} {n m : Nat} (hb : b.toNat + m ≤ 2 ^ 32) (h1 : b.toNat ≤ a.toNat)
    (h2 : a.toNat + n ≤ b.toNat + m) (h : Region a n y) : Region b m y := by
  have ha : a.toNat + n ≤ 2 ^ 32 := by omega
  rw [region_iff ha] at h; rw [region_iff hb]; omega

theorem opPre_even (d a : Nat) (b : Option Nat) : seqSize (opPre d a b) % 2 = 0 := by
  cases b <;> simp [opPre, seqSize, Instr.size]

theorem opCall_size (o tgt d a : Nat) (b : Option Nat) :
    seqSize (opCall o tgt d a b) = seqSize (opPre d a b) + 4 := by
  simp [opCall, seqSize_append, seqSize, blTo, Instr.size]

theorem bl_at {q t : Nat} (h : seqAt B q [blTo q t] = true) :
    instrAt B q = some (blTo q t) ∧ q + 4 ≤ B.length := by
  simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1, by simpa [blTo, Instr.size] using h.2⟩

theorem size_lt : Artifacts.Release.size < 2 ^ 22 := by decide

/-! ## Program counters of a code part

`PcOk base lo hi Pc`: `Pc` covers the field routines (the code below the entry) and the entry
code at offsets `[lo, hi)`. The functional proof runs each part of the entry under its own `Pc`,
so that a part's events are known to lie outside the other parts (the constant-time proof uses this
to place the byte loads and stores of the entry). -/
structure PcOk (base : Word) (lo hi : Nat) (Pc : Word → Prop) : Prop where
  rout : ∀ y, Region base Artifacts.Release.x25519 y → Pc y
  ent : InRegion Pc base lo (hi - lo)
  xlo : Artifacts.Release.x25519 ≤ lo
  hile : hi ≤ Artifacts.Release.size

theorem PcOk.inE {base : Word} {lo hi : Nat} {Pc : Word → Prop} (h : PcOk base lo hi Pc)
    {o n : Nat} (h1 : lo ≤ o) (h2 : o + n ≤ hi) : InRegion Pc base o n := by
  have := h.ent.sub (a := o - lo) (n := n) (by omega)
  rwa [show lo + (o - lo) = o by omega] at this

theorem PcOk.atE {base : Word} {lo hi : Nat} {Pc : Word → Prop} (h : PcOk base lo hi Pc)
    {o : Nat} (h1 : lo ≤ o) (h2 : o < hi) : Pc (base + BitVec.ofNat 32 o) := by
  simpa using h.inE (n := 1) h1 (by omega) 0 (by omega)

/-- `inE` for a part `[L, H)` inside `[lo, hi)`: the offsets are checked against `L` and `H`. -/
theorem PcOk.inE' {base : Word} {lo hi L H : Nat} {Pc : Word → Prop} (h : PcOk base lo hi Pc)
    (hl : lo ≤ L) (hh : H ≤ hi) {o n : Nat} (hb : L ≤ o ∧ o + n ≤ H) : InRegion Pc base o n :=
  h.inE (by omega) (by omega)

theorem PcOk.atE' {base : Word} {lo hi L H : Nat} {Pc : Word → Prop} (h : PcOk base lo hi Pc)
    (hl : lo ≤ L) (hh : H ≤ hi) {o : Nat} (hb : L ≤ o ∧ o < H) : Pc (base + BitVec.ofNat 32 o) :=
  h.atE (by omega) (by omega)

/-- A routine's bytes lie below the entry, so in `Pc`. -/
theorem PcOk.routine {base : Word} {lo hi : Nat} {Pc : Word → Prop} (h : PcOk base lo hi Pc)
    (hw : base.toNat + Artifacts.Release.size ≤ 2 ^ 32) {off size : Nat}
    (hr : off + size ≤ Artifacts.Release.x25519) :
    ∀ y, Region (base + BitVec.ofNat 32 off) size y → Pc y := fun y hy => by
  have hx : Artifacts.Release.x25519 ≤ Artifacts.Release.size := by decide
  have e : (base + BitVec.ofNat 32 off).toNat = base.toNat + off :=
    Frame.toNat_add_ofNat _ _ (by omega)
  exact h.rout y (region_sub (by omega) (by omega) (by omega) hy)


section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

theorem sp0_lt : c.sp0.toNat < 2 ^ 32 := c.sp0.isLt

theorem E_toNat : (E c).toNat = c.sp0.toNat - (SAVED + LFRAME) := by
  have := hv.spLo
  unfold E; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [X25519.stackBytes, SAVED, LFRAME] at this ⊢
  have := c.sp0.isLt
  rw [show 2 ^ 32 - 368 % 2 ^ 32 + c.sp0.toNat = (c.sp0.toNat - 368) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem fp_toNat : c.fp.toNat = c.sp0.toNat - X25519.stackBytes := by
  have := hv.spLo
  unfold X25519.Ctx.fp; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [X25519.stackBytes] at this ⊢
  have := c.sp0.isLt
  rw [show 2 ^ 32 - 516 % 2 ^ 32 + c.sp0.toNat = (c.sp0.toNat - 516) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem E_add {d : Nat} (hd : d ≤ LFRAME + SAVED) : (E c + BitVec.ofNat 32 d).toNat = (E c).toNat + d := by
  have := E_toNat hv; have := hv.spLo; have := c.sp0.isLt
  simp only [X25519.stackBytes, SAVED, LFRAME] at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem E_sub {k : Nat} (hk : k ≤ CALLEE) : (E c - BitVec.ofNat 32 k).toNat = (E c).toNat - k := by
  have := E_toNat hv; have := hv.spLo; have := c.sp0.isLt
  simp only [X25519.stackBytes, SAVED, LFRAME, CALLEE] at *
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 32 - k + (E c).toNat = ((E c).toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

end

/-! ## The state between operations -/

/-- SP at `E c`; memory outside the scratch bytes as after the prologue (`m1`). -/
structure Body (c : X25519.Ctx) (m1 : Mem) (t : State) : Prop where
  sp : t.regs 13 = E c
  keep : ∀ y, ¬ Region c.fp X25519.wipeBytes y → t.mem y = m1 y

theorem Body.code {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hc : CodeAt m1 c.base B)
    {t : State} (h : Body c m1 t) : CodeAt t.mem c.base B := by
  intro i hi
  rw [h.keep _ fun hy => ?_]
  · exact hc i hi
  · have hs := hv.codeS
    have hl : B.length = Artifacts.Release.size := B_len
    exact X25519MulcFacts.region_ne hs (show Region c.fp X25519.stackBytes _ from
      Nat.lt_of_lt_of_le hy (by decide)) i (by omega) rfl

/-- A slot offset: word aligned, inside the frame. -/
def SlotOk (d : Nat) : Prop := d % 32 = 0 ∧ d + 32 ≤ LFRAME

instance (d : Nat) : Decidable (SlotOk d) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## One call operation -/

theorem op_call_w {off size frame : Nat} {useB : Bool} {f : Int → Int → Int}
    (hrun : RoutineRun off size frame useB f) (hfr : frame ≤ CALLEE)
    (hrt : off + size ≤ Artifacts.Release.x25519)
    {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
    {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : PcOk c.base lo hi Pc)
    {s : State} {Q : State → Prop} {o d a : Nat} {b : Option Nat}
    (hseq : seqAt B o (opCall o off d a b) = true) (ho : o % 2 = 0)
    (hlo : lo ≤ o) (hend0 : o + seqSize (opCall o off d a b) ≤ hi)
    (hpc : s.pc = c.base + BitVec.ofNat 32 o) (hs : Body c m1 s)
    (hd : SlotOk d) (ha : SlotOk a) (hb : ∀ x, b = some x → SlotOk x)
    (hbB : useB = true → b.isSome = true)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (opCall o off d a b)) → Body c m1 t →
      X25519Congr.ModP (feVal t.mem (E c + BitVec.ofNat 32 d))
        (f (feVal s.mem (E c + BitVec.ofNat 32 a)) (feVal s.mem (bAddr (E c) (s.regs 2) b))) →
      (∀ y, Region (E c) LFRAME y → ¬ Region (E c + BitVec.ofNat 32 d) 32 y → t.mem y = s.mem y) →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hend : o + seqSize (opCall o off d a b) ≤ Artifacts.Release.size := Nat.le_trans hend0 hPO.hile
  have hafter : off + size ≤ o := Nat.le_trans hrt (Nat.le_trans hPO.xlo hlo)
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hR := hv.codeS
  have hE := E_toNat hv
  have hF := fp_toNat hv
  have hsp := hv.spLo
  have hs4 := hv.sp4
  have hsl := size_lt
  have hsz := opCall_size o off d a b
  have hev := opPre_even d a b
  have hps := opPre_size d a b
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨ha1, ha2⟩ := ha
  simp only [X25519.stackBytes, X25519.wipeBytes, SAVED, LFRAME, CALLEE, Disj] at *
  rw [opCall, seqAt_append, Bool.and_eq_true] at hseq
  obtain ⟨hP, hbl⟩ := hseq
  obtain ⟨hi, hil⟩ := bl_at hbl
  rw [B_len] at hil
  have hdd : d % 4 = 0 ∧ d < 1024 := ⟨by omega, by omega⟩
  have haa : a % 4 = 0 ∧ a < 1024 := ⟨by omega, by omega⟩
  have hbb : ∀ x, b = some x → x % 4 = 0 ∧ x < 1024 := fun x hx => by
    obtain ⟨h1, h2⟩ := hb x hx; simp only [LFRAME] at h2; omega
  have hreg := opPre_reg d a b
  refine X25519Block.ReachW.blockRuns hb0 (opPre d a b) o hpc ho hP (opPre_falls d a b)
    (Runs.reg (Q := fun u => u = execAll (opPre d a b) s) hreg.1 hreg.2 rfl)
    (hPO.inE hlo (by omega)) ?_
  rintro u upc rfl
  obtain ⟨u0, u1, u2, um, ur⟩ := opPre_exec s d a b hdd haa hbb
  have hsp' : s.sp = E c := hs.sp
  rw [hsp'] at u0 u1 u2
  have u13 : (execAll (opPre d a b) s).regs 13 = E c := by rw [ur 13 (by decide) (by decide)]; exact hs.sp
  generalize execAll (opPre d a b) s = u at u0 u1 u2 um ur u13 upc
  have eD : (E c + BitVec.ofNat 32 d).toNat = (E c).toNat + d := E_add hv (by simp only [SAVED, LFRAME]; omega)
  have eA : (E c + BitVec.ofNat 32 a).toNat = (E c).toNat + a := E_add hv (by simp only [SAVED, LFRAME]; omega)
  have eF : (E c - BitVec.ofNat 32 frame).toNat = (E c).toNat - frame := E_sub hv hfr
  have eBb : ∀ x, b = some x → (E c + BitVec.ofNat 32 x).toNat = (E c).toNat + x ∧ x % 32 = 0 ∧ x + 32 ≤ 332 :=
    fun x hx => by
      obtain ⟨h1, h2⟩ := hb x hx
      exact ⟨E_add hv (by simp only [SAVED, LFRAME] at h2 ⊢; omega), h1, h2⟩
  have eOff : (c.base + BitVec.ofNat 32 off).toNat = c.base.toNat + off :=
    Frame.toNat_add_ofNat _ _ (by omega)
  have eQ : ∀ n, n < Artifacts.Release.size → (c.base + BitVec.ofNat 32 n).toNat = c.base.toNat + n :=
    fun n hn => Frame.toNat_add_ofNat _ _ (by omega)
  have hW1 : ∀ y, Region (E c - BitVec.ofNat 32 frame) frame y → Region c.fp 480 y := fun y h =>
    region_sub (by omega) (by omega) (by omega) h
  have hD : ∀ y, Region (E c + BitVec.ofNat 32 d) 32 y → Region c.fp 480 y := fun y h =>
    region_sub (by omega) (by omega) (by omega) h
  have hRw : ∀ y, Region c.fp 480 y → Region c.fp 516 y := fun y h =>
    region_sub (by omega) (Nat.le_refl _) (by omega) h
  have hdisjS : ∀ x, x % 32 = 0 → x + 32 ≤ 332 →
      Disj (E c + BitVec.ofNat 32 x) 32 (E c - BitVec.ofNat 32 frame) frame := fun x h1 h2 => by
    have := E_add hv (d := x) (by simp only [SAVED, LFRAME]; omega)
    simp only [Disj]; omega
  have hdisjC : ∀ x, x % 32 = 0 → x + 32 ≤ 332 →
      Disj c.base Artifacts.Release.size (E c + BitVec.ofNat 32 x) 32 := fun x h1 h2 => by
    have := E_add hv (d := x) (by simp only [SAVED, LFRAME]; omega)
    simp only [Disj]; omega
  have hdisjX : ∀ x, x % 32 = 0 → x + 32 ≤ 332 →
      E c + BitVec.ofNat 32 d = E c + BitVec.ofNat 32 x ∨
        Disj (E c + BitVec.ofNat 32 d) 32 (E c + BitVec.ofNat 32 x) 32 := fun x h1 h2 => by
    by_cases e : d = x
    · exact Or.inl (by rw [e])
    · have := E_add hv (d := x) (by simp only [SAVED, LFRAME]; omega)
      right; simp only [Disj]; omega
  have hq4 : (o + seqSize (opPre d a b)) % 2 = 0 := by omega
  refine call_w hrun upc hq4 hi (by omega)
    (bl_target _ _ (by omega) (by omega))
    (hPO.atE (by omega) (by omega))
    (hPO.routine hR.1 hrt)
    (by
      show ¬ (BitVec.toNat (_ - _ : Word) < _)
      rw [show o + seqSize (opPre d a b) + 4 = off + (o + seqSize (opPre d a b) + 4 - off) by omega,
        ← ofNat_add_assoc, Frame.sub_ofNat_toNat _ _ (by omega)]
      omega)
    { base4 := hv.base4
      sp4 := by rw [u13]; omega
      spLo := by rw [u13]; omega
      al := ⟨by rw [u0, eD]; omega, by rw [u1, eA]; omega, fun hu => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hbB hu)
        obtain ⟨e1, e2, _⟩ := eBb x hx
        rw [u2, hx]; show (E c + BitVec.ofNat 32 x).toNat % 4 = 0; rw [e1]; omega⟩
      code := by rw [um]; exact Body.code hv hcode hs
      codeS := by simp only [Disj]; (try rw [u13]); rw [eF]; omega
      codeD := by rw [u0]; exact hdisjC d hd1 hd2
      dstS := by rw [u0, u13]; exact hdisjS d hd1 hd2
      aS := by rw [u1, u13]; exact hdisjS a ha1 ha2
      bS := fun hu => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hbB hu)
        obtain ⟨_, e2, e3⟩ := eBb x hx
        rw [u2, hx, u13]; exact hdisjS x e2 e3
      dstA := by rw [u0, u1]; exact hdisjX a ha1 ha2
      dstB := fun hu => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hbB hu)
        obtain ⟨_, e2, e3⟩ := eBb x hx
        rw [u0, u2, hx]; exact hdisjX x e2 e3 }
    (fun y h => hWr y (hRw y (by
      rcases h with h | h
      · rw [u13] at h; exact hW1 y h
      · rw [u0] at h; exact hD y h))) ?_
  intro t tpc tp
  have tsp : t.regs 13 = E c := by rw [tp.sp]; exact u13
  have tm : ∀ y, ¬ Region (E c - BitVec.ofNat 32 frame) frame y → ¬ Region (E c + BitVec.ofNat 32 d) 32 y →
      t.mem y = s.mem y := fun y h1 h2 => by
    have := tp.mem y (by show ¬ Region (u.regs 13 - _) _ _; rwa [u13]) (by show ¬ Region (u.regs 0) _ _; rwa [u0])
    rw [this]; exact congrFun um y
  refine k t (by rw [tpc, hsz, Nat.add_assoc])
    ⟨tsp, fun y hy => by rw [tm y (fun h => hy (hW1 y h)) (fun h => hy (hD y h))]; exact hs.keep y hy⟩
    ?_ ?_
  · have hv' := tp.val
    simp only [callOf] at hv'
    rw [u0, u1, u2, um] at hv'
    exact hv'
  · intro y hy hn
    refine tm y (fun h => ?_) hn
    rw [region_iff (by omega)] at h hy
    rw [eF] at h
    omega

end M0Crypto.Release.X25519Op
