import M0Crypto.Release.Ed25519CallProg
import M0Crypto.Release.Ed25519FeAddSub

set_option linter.unusedSimpArgs false

/-!
# Call programs: values, views and loaders

The dynamic side of a call program. A run has a public context `Ctx` (code base, the caller's
entry `sp0`, the external pointers and the public parameters); a symbolic value `SV` denotes a
word of it. A view of kind `Kd` at a location relates memory to a value `V` (`Rel`): bytes are
exact, a field element is congruent modulo `p`, a SHA-512 context and a point are related by the
callees' relations `Rels` (the SHA-512 and point lanes define them; here they are parameters with
their locality). `Inv` is what a program run carries: every live view holds, and while no
external buffer has been written, the external buffers hold their entry bytes (the snapshot that
lets inputs be read after the caller's buffers may alias its outputs).

`ld_run` gives the registers after a call's operand loads, generic in the loaders: each register
holds the value of its symbolic value, memory and the other registers are unchanged.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Frame (Disj)

/-! ## Context and values -/

/-- The public context of a run: code base, the caller's entry SP, external pointers, public
parameters. -/
structure Ctx where
  base : Word
  sp0 : Word
  ptr : Nat → Word
  prm : Nat → Word

/-- SP of the frame, `top` bytes below `sp0`. -/
def Ctx.fsp (c : Ctx) (top : Nat) : Word := c.sp0 - BitVec.ofNat 32 top

def SV.val (c : Ctx) (sp : Word) : SV → Word
  | .sp o => sp + BitVec.ofNat 32 o
  | .ext i e => c.ptr i + BitVec.ofNat 32 e
  | .prm i => c.prm i
  | .k n => BitVec.ofNat 32 n

def XLen.val (c : Ctx) : XLen → Nat
  | .k n => n
  | .p i => (c.prm i).toNat

def Loc.addr (c : Ctx) (sp : Word) : Loc → Word
  | .fr o => sp + BitVec.ofNat 32 o
  | .ex i e => c.ptr i + BitVec.ofNat 32 e
  | .rg _ => 0

/-- A value of a view. -/
inductive V where
  | b (l : List Byte)
  | f (x : Int)
  | c (M : List Byte)
  | p (P : Spec.Ed25519.Point)
  | w (x : Word)
  | none

/-- The relations of the SHA-512 context and of an extended point, with their locality: they
depend on the `ctxSize`, `128` bytes at their address only. -/
structure Rels where
  ctx : Mem → Word → List Byte → Prop
  pt : Mem → Word → Spec.Ed25519.Point → Prop
  /-- The context's first word is its stream length. -/
  ctx_len : ∀ {m a M}, ctx m a M → read32 m a = BitVec.ofNat 32 M.length
  ctx_memEq : ∀ {W m m' a M}, MemEq W m m' → Sep [⟨a, ctxSize⟩] W → ctx m a M → ctx m' a M
  pt_memEq : ∀ {W m m' a P}, MemEq W m m' → Sep [⟨a, 128⟩] W → pt m a P → pt m' a P

variable (Rs : Rels)

/-- The value of a sum of public lengths. -/
def slen (c : Ctx) (sp : Word) (n : List SV) : Nat := (n.map fun v => (v.val c sp).toNat).sum

/-- **The view relation**: memory `m` at `a` holds value `v` as kind `k`. -/
def Rel (c : Ctx) (sp : Word) : Kd → Mem → Word → V → Prop
  | .bytes n, m, a, .b l => bytesAt m a n = l
  | .sc, m, a, .b l => bytesAt m a 32 = l ∧ Spec.Ed25519.decodeInt l < Spec.Ed25519.L
  | .cl, m, a, .b l => bytesAt m a 32 = l ∧ Spec.Ed25519.decodeInt l < 2 ^ 255
  | .fe, m, a, .f x => ModP (feVal m a) x
  | .ctx n, m, a, .c M => Rs.ctx m a M ∧ M.length = slen c sp n
  | .pt, m, a, .p P => Rs.pt m a P
  | .pw v, m, a, _ => read32 m a = v.val c sp
  | .cw, m, a, .w x => read32 m a = x
  | .rw, _, a, .w x => a = x
  | .fc, m, a, .f x => (feVal m a : Int) = x ∧ x < Field25519Congr.p
  | .fe4, m, a, .p P => ModP (feVal m a) P.X ∧ ModP (feVal m (a + BitVec.ofNat 32 32)) P.Y ∧
      ModP (feVal m (a + BitVec.ofNat 32 64)) P.Z ∧ ModP (feVal m (a + BitVec.ofNat 32 96)) P.T
  | _, _, _, _ => False

/-- The bound of a refined kind on its bytes; another kind bounds nothing. -/
def Kd.Bnd : Kd → List (BitVec 8) → Prop
  | .sc, l => Spec.Ed25519.decodeInt l < Spec.Ed25519.L
  | .cl, l => Spec.Ed25519.decodeInt l < 2 ^ 255
  | _, _ => True

theorem L_lt : Spec.Ed25519.L < 2 ^ 255 := by decide

/-- A refined kind's bound gives the bound of every kind above it. -/
theorem Kd.bnd_le {k k' : Kd} (h : k.le k' = true) {l : List (BitVec 8)} (hb : k.Bnd l) : k'.Bnd l := by
  simp only [Kd.le, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | ⟨-, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · exact hb
  · trivial
  · exact Nat.lt_trans hb L_lt
  · trivial

/-- **The kind order is sound**: a view of kind `k` holds as every kind above it. -/
theorem Kd.le_rel {c : Ctx} {sp : Word} {k k' : Kd} (h : k.le k' = true) {m : Mem} {a : Word} {v : V}
    (hr : Rel Rs c sp k m a v) : Rel Rs c sp k' m a v := by
  simp only [Kd.le, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | ⟨hk, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · exact hr
  · cases k <;> simp only [Kd.isRef, Bool.false_eq_true] at hk <;> cases v <;> simp only [Rel] at hr ⊢ <;>
      exact hr.1
  · cases v <;> simp only [Rel] at hr ⊢; exact ⟨hr.1, Nat.lt_trans hr.2 L_lt⟩
  · cases v <;> simp only [Rel] at hr ⊢; rw [hr.1]; rfl

theorem Kd.le_sz {k k' : Kd} (h : k.le k' = true) : k'.sz = k.sz := by
  simp only [Kd.le, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | ⟨hk, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · rfl
  · cases k <;> simp only [Kd.isRef, Bool.false_eq_true] at hk <;> rfl
  · rfl
  · rfl

/-- A refined kind's view holds its bytes' bound. -/
theorem Kd.bnd_of_rel {c : Ctx} {sp : Word} {k : Kd} (hk : k.isRef = true) {m : Mem} {a : Word} {v : V}
    (hr : Rel Rs c sp k m a v) : k.Bnd (bytesAt m a 32) := by
  cases k <;> simp only [Kd.isRef, Bool.false_eq_true] at hk <;> cases v <;> simp only [Rel] at hr <;>
    exact hr.1 ▸ hr.2

/-- `feVal` at offset `o` of 128 bytes across a frame fact apart from them. -/
theorem feVal_off_memEq {W : List Rgn} {m m' : Mem} {a : Word} (h : MemEq W m m') (hs : Sep [⟨a, 128⟩] W)
    {o : Nat} (ho : o + 32 ≤ 128) : feVal m' (a + BitVec.ofNat 32 o) = feVal m (a + BitVec.ofNat 32 o) := by
  unfold feVal; congr 1; apply List.map_congr_left; intro i hi
  have hi8 : i < 8 := List.mem_range.mp hi
  rw [Frame.read32_congr fun k hk => ?_]
  simp only [ofNat_add_assoc]
  exact h _ (Sep.not_has hs ⟨⟨a, 128⟩, List.mem_singleton_self _, ⟨o + 4 * i + k, show o + 4 * i + k < 128 by omega, rfl⟩⟩)

theorem Rel.memEq {c : Ctx} {sp : Word} {k : Kd} {W : List Rgn} {m m' : Mem} {a : Word} {v : V}
    (h : MemEq W m m') (hs : Sep [⟨a, k.sz⟩] W) (hr : Rel Rs c sp k m a v) : Rel Rs c sp k m' a v := by
  cases k <;> cases v <;> simp only [Rel, Kd.sz] at hr hs ⊢
  all_goals first
    | exact hr.elim
    | exact hr
    | (rw [h.bytes hs]; exact hr)
    | (rw [Ed25519FeAddSub.feVal_memEq h hs]; exact hr)
    | exact ⟨Rs.ctx_memEq h hs hr.1, hr.2⟩
    | exact Rs.pt_memEq h hs hr
    | (rw [h.read32 hs]; exact hr)
    | (rw [Ed25519FeAddSub.feVal_memEq h hs]; exact hr)
    | (have e0 := feVal_off_memEq h hs (o := 0) (by omega)
       rw [show a + BitVec.ofNat 32 0 = a from BitVec.add_zero _] at e0
       rw [e0, feVal_off_memEq h hs (o := 32) (by omega), feVal_off_memEq h hs (o := 64) (by omega),
        feVal_off_memEq h hs (o := 96) (by omega)]; exact hr)

/-! ## Static typing of a run -/

/-- The word view at frame offset `o` in `Γ`, if any. -/
def pwAt (Γ : List (Loc × Kd)) (o : Nat) : Option SV :=
  Γ.findSome? fun x => match x with
    | (.fr o', .pw v) => if o' = o then some v else none
    | _ => none

/-- The symbolic value a loader leaves, given the word views `Γ`. -/
def Ld.sv (Γ : List (Loc × Kd)) : Ld → Option SV
  | .S off => some (.sp off)
  | .W off e => match pwAt Γ off with
    | some (.ext i e₀) => some (.ext i (e₀ + e))
    | some (.sp o) => some (.sp (o + e))
    | some v => if e = 0 then some v else none
    | none => none
  | .K n => some (.k n)
  | .A _ => none
  | .C _ _ _ => none

/-- The registers known before a call's loads, `σ`, updated by the loads `as`. -/
def regsOf (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) (as : List (LowReg × Ld)) : List (Reg × SV) :=
  as.filterMap (fun a => (a.2.sv Γ).map fun v => (a.1.toReg, v)) ++
    σ.filter fun p => !(as.any fun a => a.1.toReg == p.1)

/-- Registers `regs` hold the values `σ` says. -/
def Holds (c : Ctx) (sp : Word) (σ : List (Reg × SV)) (regs : Reg → Word) : Prop :=
  ∀ p ∈ σ, p.1.val < 14 ∧ regs p.1 = p.2.val c sp

/-! ## Loaders -/

/-- What a loader leaves in its register, from the memory and `sp`. -/
def Ld.mval (m : Mem) (sp : Word) : Ld → Word
  | .S off => sp + BitVec.ofNat 32 off
  | .W off e => read32 m (sp + BitVec.ofNat 32 off) + BitVec.ofNat 32 e
  | .K n => BitVec.ofNat 32 n
  | .A _ => 0
  | .C _ _ _ => 0

/-- The loader is encodable: word-aligned offsets, constants below 256. -/
def Ld.ok : Ld → Bool
  | .S off => off % 4 == 0
  | .W off _ => off % 4 == 0
  | .K n => decide (n < 256)
  | .A _ => false
  | .C _ _ _ => false

/-- `u` has the memory of `t` and its registers other than `r` and `pc`. -/
def Only (r : LowReg) (t u : State) : Prop :=
  u.mem = t.mem ∧ ∀ q : Reg, q ≠ 15 → q ≠ r.toReg → u.regs q = t.regs q

theorem Only.refl (r : LowReg) (t : State) : Only r t t := ⟨rfl, fun _ _ _ => rfl⟩

theorem Only.trans {r : LowReg} {t u v : State} (h1 : Only r t u) (h2 : Only r u v) : Only r t v :=
  ⟨h2.1.trans h1.1, fun q h15 hr => (h2.2 q h15 hr).trans (h1.2 q h15 hr)⟩

theorem toReg_val (r : LowReg) : r.toReg.val = r.val := rfl

theorem ne15 : ∀ {r : LowReg}, r.toReg ≠ 15 := by decide

theorem ne13 : ∀ {r : LowReg}, (13 : Reg) ≠ r.toReg := by decide

theorem setWidth8 {n : Nat} (h : n < 256) : (BitVec.ofNat 8 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem addsN_run (r : LowReg) : ∀ (f n : Nat) (t : State), n ≤ 252 * f →
    Only r t (execAll (addsN r f n) t) ∧
      (execAll (addsN r f n) t).regs r.toReg = t.regs r.toReg + BitVec.ofNat 32 n ∧
      (addsN r f n).all Instr.falls = true
  | 0, n, t, h => by
    obtain rfl : n = 0 := Nat.le_zero.mp (by simpa using h)
    simp [addsN, execAll, Only.refl]
  | f + 1, n, t, h => by
    by_cases h0 : n = 0
    · subst h0; simp [addsN, execAll, Only.refl]
    · simp only [addsN, h0, ↓reduceIte, execAll, List.all_cons, Bool.and_eq_true]
      generalize hsd : (Instr.addImm8 r (BitVec.ofNat 8 (min n 252))).next t = s
      have hs : Only r t s ∧ s.regs r.toReg = t.regs r.toReg + BitVec.ofNat 32 (min n 252) := by
        subst hsd
        refine ⟨⟨by simp [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setReg], fun q h15 hq => ?_⟩, ?_⟩
        · simp [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setReg, hq, h15]
        · simp [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setReg, State.reg, ne15,
            M0Crypto.Proofs.addWithCarry_fst, setWidth8 (show min n 252 < 256 by omega)]
      obtain ⟨h1, h2, h3⟩ := addsN_run r f (n - min n 252) s (by omega)
      refine ⟨hs.1.trans h1, by rw [h2, hs.2, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega,
        rfl, h3⟩

theorem adds_run (r : LowReg) (n : Nat) (t : State) :
    Only r t (execAll (adds r n) t) ∧
      (execAll (adds r n) t).regs r.toReg = t.regs r.toReg + BitVec.ofNat 32 n ∧
      (adds r n).all Instr.falls = true :=
  addsN_run r n n t (by omega)

theorem spAddr_run (r : LowReg) {off : Nat} (h4 : off % 4 = 0) (t : State) :
    Only r t (execAll (spAddr r off) t) ∧
      (execAll (spAddr r off) t).regs r.toReg = t.regs 13 + BitVec.ofNat 32 off ∧
      (spAddr r off).all Instr.falls = true := by
  have one : ∀ (k : Nat), k < 256 → Only r t ((Instr.addRdSp r (BitVec.ofNat 8 k)).next t) ∧
      ((Instr.addRdSp r (BitVec.ofNat 8 k)).next t).regs r.toReg = t.regs 13 + BitVec.ofNat 32 (k * 4) := by
    intro k hk
    refine ⟨⟨by simp [Instr.next, Instr.exec, State.setReg], fun q h15 hq => ?_⟩, ?_⟩
    · simp [Instr.next, Instr.exec, State.setReg, hq, h15]
    · have hk' : (BitVec.ofNat 8 k).toNat = k := by simp; omega
      simp only [Instr.next, Instr.exec, State.setReg, State.sp, hk', ite_true]
  unfold spAddr
  split
  · obtain ⟨h1, h2⟩ := one (off / 4) (by omega)
    refine ⟨h1, ?_, rfl⟩
    have e : off / 4 * 4 = off := by omega
    simp only [execAll]; rw [h2, e]
  · obtain ⟨h1, h2⟩ := one 255 (by omega)
    obtain ⟨a1, a2, a3⟩ := adds_run r (off - 1020) ((Instr.addRdSp r (BitVec.ofNat 8 255)).next t)
    simp only [execAll, List.all_cons, a3, Bool.and_true] at a1 a2 ⊢
    refine ⟨h1.trans a1, ?_, rfl⟩
    rw [a2, h2, BitVec.add_assoc, ← BitVec.ofNat_add, show 255 * 4 + (off - 1020) = off by omega]

theorem ldrSpI_run (r : LowReg) {off : Nat} (h4 : off % 4 = 0) (t : State) :
    Only r t (execAll (ldrSpI r off) t) ∧
      (execAll (ldrSpI r off) t).regs r.toReg = read32 t.mem (t.regs 13 + BitVec.ofNat 32 off) ∧
      (ldrSpI r off).all Instr.falls = true := by
  unfold ldrSpI
  split
  · refine ⟨⟨by simp [execAll, Instr.next, Instr.exec, State.setReg], fun q h15 hq => ?_⟩, ?_, rfl⟩
    · simp [execAll, Instr.next, Instr.exec, State.setReg, hq, h15]
    · simp [execAll, Instr.next, Instr.exec, State.setReg, State.sp, ne15]
      congr 3; omega
  · obtain ⟨a1, a2, a3⟩ := spAddr_run r h4 t
    rw [execAll_append]
    refine ⟨a1.trans ⟨by simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg], fun q h15 hq => ?_⟩,
      ?_, by simp [List.all_append, a3]; rfl⟩
    · simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, hq, h15]
    · simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, ne15, MemOp.width]
      rw [a2, a1.1]

/-- **A loader**: its register receives `Ld.mval`, nothing else changes. -/
theorem Ld.run (r : LowReg) {l : Ld} (hl : l.ok = true) (t : State) :
    Only r t (execAll (l.emit r) t) ∧ (execAll (l.emit r) t).regs r.toReg = l.mval t.mem (t.regs 13) ∧
      (l.emit r).all Instr.falls = true := by
  cases l with
  | S off =>
    simp only [Ld.ok, beq_iff_eq] at hl
    exact spAddr_run r hl t
  | W off e =>
    simp only [Ld.ok, beq_iff_eq] at hl
    obtain ⟨a1, a2, a3⟩ := ldrSpI_run r hl t
    obtain ⟨b1, b2, b3⟩ := adds_run r e (execAll (ldrSpI r off) t)
    simp only [Ld.emit, execAll_append, Ld.mval, List.all_append, a3, b3, Bool.and_self]
    exact ⟨a1.trans b1, by rw [b2, a2], trivial⟩
  | K n =>
    simp only [Ld.ok, decide_eq_true_eq] at hl
    refine ⟨⟨by simp [Ld.emit, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ],
      fun q h15 hq => ?_⟩, ?_, rfl⟩
    · simp [Ld.emit, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, hq, h15]
    · simp [Ld.emit, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, Ld.mval, ne15,
        setWidth8 hl]
  | A _ => simp [Ld.ok] at hl
  | C _ _ _ => simp [Ld.ok] at hl

/-- The loaders are encodable and load distinct registers. -/
def ldsOk (as : List (LowReg × Ld)) : Bool :=
  as.all (fun a => a.2.ok) && (as.map fun a => a.1.val).Nodup

theorem lds_run : ∀ (as : List (LowReg × Ld)) (t : State), ldsOk as = true →
    (execAll (ldsEmit as) t).mem = t.mem ∧
    (∀ q : Reg, q ≠ 15 → (∀ a ∈ as, q ≠ a.1.toReg) → (execAll (ldsEmit as) t).regs q = t.regs q) ∧
    (∀ a ∈ as, (execAll (ldsEmit as) t).regs a.1.toReg = a.2.mval t.mem (t.regs 13)) ∧
    (ldsEmit as).all Instr.falls = true
  | [], t, _ => ⟨rfl, fun _ _ _ => rfl, fun _ h => (nomatch h), rfl⟩
  | (r, l) :: as, t, h => by
    simp only [ldsOk, List.all_cons, Bool.and_eq_true, List.map_cons, List.nodup_cons,
      decide_eq_true_eq] at h
    obtain ⟨⟨hl, hall⟩, hr, hnd⟩ := h
    have hok : ldsOk as = true := by simp [ldsOk, hall, hnd]
    obtain ⟨a1, a2, a3⟩ := Ld.run r hl t
    obtain ⟨b1, b2, b3, b4⟩ := lds_run as (execAll (l.emit r) t) hok
    have hu13 : (execAll (l.emit r) t).regs 13 = t.regs 13 := a1.2 13 (by decide) ne13
    simp only [ldsEmit, execAll_append, List.all_append, a3, b4, Bool.and_self]
    refine ⟨b1.trans a1.1, fun q h15 hq => ?_, fun a ha => ?_, trivial⟩
    · rw [b2 q h15 fun a ha => hq a (List.mem_cons_of_mem _ ha),
        a1.2 q h15 (hq _ List.mem_cons_self)]
    · rcases List.mem_cons.mp ha with rfl | ha
      · rw [b2 r.toReg ne15 (fun a ha he => hr (by
          rw [List.mem_map]; exact ⟨a, ha, by have := congrArg Fin.val he; simpa [LowReg.toReg] using this.symm⟩)), a2]
      · rw [b3 a ha, a1.1, hu13]

end M0Crypto.Release.Ed25519CallProg
