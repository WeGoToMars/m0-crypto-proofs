import M0Crypto.Sym.Access
import M0Crypto.Sym.Norm

/-!
# Symbolic alignment and write-region checks for a straight-line segment

`Reach.block` needs, besides the bytes (`seqAt`) and fall-through (`falls`), two facts
about the concrete state: every data access is aligned (`alignedAll`), and every write
lands in the allowed set `Wr` (`WritesTo`). Both are decided here from the symbolic
trace (`symTrace`, layer 2), given two small annotations:

* `al : List (Reg × Nat)`: base registers with a known alignment at segment entry
  (`(13, 4)`: `sp` is a multiple of 4);
* `rg : List (Reg × Word × Nat)`: write regions, `(r, k, n)` = the `n` bytes from
  `regs r + k` at segment entry, which the caller shows are in `Wr`.

Each access address is normalised (`norm`) and split by `peel` into an entry register
plus a constant (`reg0 r + k`, with `+`/`-` constants). An access whose address does
not have this form fails the check (no silent acceptance).
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- `e` as entry register plus constant, if it has that form. -/
def peel : SExpr → Option (Reg × Word)
  | .reg0 r => some (r, 0#32)
  | .add e (.const k) => (peel e).map fun p => (p.1, p.2 + k)
  | .sub e (.const k) => (peel e).map fun p => (p.1, p.2 - k)
  | _ => none

/-- A PC-relative literal address `((pc + 4) &&& ~~~3) + k` with `4 ∣ k`: aligned for every
width dividing 4, whatever `pc` is (the `ldr Rt, [pc, #imm]` shape of `symAccesses`). -/
def litAligned : SExpr → Bool
  | .add (.and _ (.not (.const c))) (.const k) => c == 3#32 && k.toNat % 4 == 0
  | _ => false

/-- One access is aligned: it is a PC-relative literal address (`litAligned`), or its base
register has an alignment that the width divides, and so does the constant offset. Widths are
1, 2 or 4. -/
def accAligned (al : List (Reg × Nat)) (a : SAccess) : Bool :=
  (a.width == 1 || a.width == 2 || a.width == 4) &&
  (litAligned a.addr ||
  match peel (norm a.addr) with
  | some (r, k) => al.any fun p => p.1 == r && p.2 % a.width == 0 && k.toNat % a.width == 0
  | none => false)

/-- A write access lies inside one region; reads always pass. -/
def accCovered (rg : List (Reg × Word × Nat)) (a : SAccess) : Bool :=
  a.kind == .read ||
  match peel (norm a.addr) with
  | some (r, k) => rg.any fun p => p.1 == r && (k - p.2.1).toNat + a.width ≤ p.2.2
  | none => false

def alignChk (al : List (Reg × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all (accAligned al)

def writeChk (rg : List (Reg × Word × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all (accCovered rg)

/-! ## Soundness -/

/-- An address that `peel` reads as `(r, k)` denotes `regs r + k`. Written by cases on
every constructor, as `norm_sound` is, because `peel` is stuck on non-constructor input. -/
theorem peel_sound (s0 : State) : ∀ (e : SExpr) (r : Reg) (k : Word),
    peel e = some (r, k) → e.denote s0 = s0.regs r + k
  | .reg0 r, r', k, h => by
    simp only [peel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SExpr.denote]
  | .add e x, r, k, h => by
    cases x
    case const c =>
      simp only [peel] at h
      revert h
      cases hp : peel e with
      | none => intro h; simp at h
      | some p =>
        intro h
        change some (p.1, p.2 + c) = some (r, k) at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [SExpr.denote]
        rw [peel_sound s0 e p.1 p.2 hp]
        bv_omega
    all_goals simp [peel] at h
  | .sub e x, r, k, h => by
    cases x
    case const c =>
      simp only [peel] at h
      revert h
      cases hp : peel e with
      | none => intro h; simp at h
      | some p =>
        intro h
        change some (p.1, p.2 - c) = some (r, k) at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [SExpr.denote]
        rw [peel_sound s0 e p.1 p.2 hp]
        bv_omega
    all_goals simp [peel] at h
  | .const _, _, _, h => by simp [peel] at h
  | .and _ _, _, _, h => by simp [peel] at h
  | .or _ _, _, _, h => by simp [peel] at h
  | .xor _ _, _, _, h => by simp [peel] at h
  | .not _, _, _, h => by simp [peel] at h
  | .mul _ _, _, _, h => by simp [peel] at h
  | .uxth _, _, _, h => by simp [peel] at h
  | .awc _ _ _, _, _, h => by simp [peel] at h
  | .lsl _ _, _, _, h => by simp [peel] at h
  | .lsr _ _, _, _, h => by simp [peel] at h
  | .ror _ _ _, _, _, h => by simp [peel] at h
  | .ld32 _ _, _, _, h => by simp [peel] at h
  | .ld16 _ _, _, _, h => by simp [peel] at h
  | .ld8 _ _, _, _, h => by simp [peel] at h
  | .rotl _ _, _, _, h => by simp [peel] at h

/-- Divisibility of a word's value by `w` survives addition, for `w ∣ 2^32`. -/
theorem add_toNat_mod_of_dvd (x y : Word) (w : Nat) (hw : w ∣ 2 ^ 32)
    (hx : x.toNat % w = 0) (hy : y.toNat % w = 0) : (x + y).toNat % w = 0 := by
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ hw, Nat.add_mod, hx, hy]
  simp

theorem and_not3_toNat' (a : Word) : (a &&& ~~~3#32).toNat = a.toNat - a.toNat % 4 := by
  have h1 : (a &&& ~~~3#32) &&& (a &&& 3#32) = 0 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases a[i] <;> cases (3#32)[i] <;> simp
  have h2 : (a &&& ~~~3#32) + (a &&& 3#32) = a := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ h1]
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
    cases a[i] <;> cases (3#32)[i] <;> rfl
  have h3 : (a &&& 3#32).toNat = a.toNat % 4 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod a.toNat 2
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_add, h3] at this
  have : a.toNat < 2 ^ 32 := a.isLt
  have : (a &&& ~~~3#32).toNat < 2 ^ 32 := (a &&& ~~~3#32).isLt
  omega

/-- An aligned annotation makes the access aligned. -/
theorem accAligned_sound (s0 : State) (al : List (Reg × Nat))
    (hal : ∀ p ∈ al, (s0.regs p.1).toNat % p.2 = 0) (a : SAccess)
    (h : accAligned al a = true) : (a.denote s0).aligned = true := by
  unfold accAligned at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hw, hm⟩ := h
  have hdiv : a.width ∣ 2 ^ 32 := by
    have h3 : a.width = 1 ∨ a.width = 2 ∨ a.width = 4 := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hw; omega
    rcases h3 with h3 | h3 | h3 <;> rw [h3] <;> decide
  by_cases hl : litAligned a.addr = true
  · have hcases : ∀ e, litAligned e = true → ∃ x c k, e = .add (.and x (.not (.const c))) (.const k) ∧
        c = 3#32 ∧ k.toNat % 4 = 0 := by
      intro e he
      match e, he with
      | .add (.and x (.not (.const c))) (.const k), he =>
        simp only [litAligned, Bool.and_eq_true, beq_iff_eq] at he
        exact ⟨x, c, k, rfl, he.1, by simpa using he.2⟩
    obtain ⟨x, c, k, he, hc, hk⟩ := hcases _ hl
    simp only [Access.aligned, SAccess.denote, beq_iff_eq]
    rw [he]
    simp only [SExpr.denote]
    subst hc
    have hw4 : a.width ∣ 4 := by
      have h3 : a.width = 1 ∨ a.width = 2 ∨ a.width = 4 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hw; omega
      rcases h3 with h3 | h3 | h3 <;> rw [h3] <;> decide
    have hm4 : ((x.denote s0 &&& ~~~3#32) + k).toNat % 4 = 0 := by
      apply add_toNat_mod_of_dvd _ _ _ (by decide)
      · rw [and_not3_toNat']; omega
      · exact hk
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hw4 (Nat.dvd_of_mod_eq_zero hm4))
  · simp only [hl, Bool.false_or] at hm
    generalize hpe : peel (norm a.addr) = pe at hm
    cases pe with
    | none => simp at hm
    | some p =>
      obtain ⟨r, k⟩ := p
      have hn : a.addr.denote s0 = s0.regs r + k := by
        rw [← norm_sound s0 a.addr]; exact peel_sound s0 _ r k hpe
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨x, hmem, ⟨hr, hmw⟩, hkw⟩ := hm
      subst hr
      have hx := hal x hmem
      simp only [Access.aligned, SAccess.denote, beq_iff_eq]
      rw [hn]
      apply add_toNat_mod_of_dvd _ _ _ hdiv
      · exact Nat.mod_eq_zero_of_dvd
          (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hmw) (Nat.dvd_of_mod_eq_zero hx))
      · exact hkw

/-- Rearrangement used at the end of `accCovered_sound`: `k` is `q + (k - q)`. -/
theorem add_sub_rearr (R q k X : Word) : R + k + X = R + q + ((k - q) + X) := by
  have hc : q + (k - q) = k := by
    rw [BitVec.add_comm]; exact BitVec.sub_add_cancel k q
  rw [BitVec.add_assoc R q, ← BitVec.add_assoc q (k - q) X, hc, BitVec.add_assoc R k X]

/-- A write access allowed by `accCovered` lies inside one annotated region. -/
theorem accCovered_sound (s0 : State) (rg : List (Reg × Word × Nat)) (a : SAccess)
    (h : accCovered rg a = true) (y : Word) (hy : Writes [a.denote s0] y) :
    ∃ p ∈ rg, ∃ o < p.2.2, y = s0.regs p.1 + p.2.1 + BitVec.ofNat 32 o := by
  obtain ⟨x, hx, hkind, k', hk', hyx⟩ := hy
  rw [List.mem_singleton] at hx
  subst hx
  have hk : a.kind = .write := hkind
  have hk'' : k' < a.width := hk'
  have hyx' : y = a.addr.denote s0 + BitVec.ofNat 32 k' := hyx
  unfold accCovered at h
  generalize hpe : peel (norm a.addr) = pe at h
  cases pe with
  | none => simp [hk] at h
  | some p =>
    obtain ⟨r, k⟩ := p
    have hn : a.addr.denote s0 = s0.regs r + k := by
      rw [← norm_sound s0 a.addr]; exact peel_sound s0 _ r k hpe
    simp only [hk, Bool.or_eq_true, beq_iff_eq, reduceCtorEq, false_or, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨q, hq, hqr, hle⟩ := h
    subst hqr
    refine ⟨q, hq, (k - q.2.1).toNat + k', by omega, ?_⟩
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, hyx', hn]
    exact add_sub_rearr _ _ _ _

/-- A segment whose alignment check passes is aligned on the concrete state. -/
theorem alignChk_sound (al : List (Reg × Nat)) (is : List Instr) (hs : ∀ i ∈ is, Sound i)
    (s : State) (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (h : alignChk al is = true) : alignedAll is s = true := by
  have hA := alignedAll_sym is hs s SState.init
  rw [SState.init_denote] at hA
  rw [hA]
  unfold alignChk at h
  simp only [List.all_eq_true] at h ⊢
  intro e he a ha
  exact accAligned_sound s al hal a (h e he a ha)

/-- Every write of a segment whose write check passes lies inside an annotated region,
stated per event. -/
theorem writeChk_sound (rg : List (Reg × Word × Nat)) (is : List Instr) (hs : ∀ i ∈ is, Sound i)
    (s : State) (h : writeChk rg is = true) :
    ∀ e ∈ traceAll is s, ∀ y, Writes e.accesses y →
      ∃ p ∈ rg, ∃ o < p.2.2, y = s.regs p.1 + p.2.1 + BitVec.ofNat 32 o := by
  have hT := symTrace_sound is hs s SState.init
  rw [SState.init_denote] at hT
  intro e he y hy
  rw [← hT, List.mem_map] at he
  obtain ⟨⟨pc, i, acc⟩, hse, rfl⟩ := he
  unfold writeChk at h
  have h2 : acc.all (accCovered rg) = true := List.all_eq_true.mp h _ hse
  obtain ⟨x, hx, hkind, k, hk, hyx⟩ := hy
  have hx' : x ∈ acc.map (SAccess.denote s) := hx
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hx'
  exact accCovered_sound s rg a' (List.all_eq_true.mp h2 a' ha') y
    ⟨a'.denote s, List.mem_singleton_self _, hkind, k, hk, hyx⟩

end M0Crypto.Sym
