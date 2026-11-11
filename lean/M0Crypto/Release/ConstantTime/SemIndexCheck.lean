import M0Crypto.Release.ConstantTime.SemIndex

/-! Boolean checks and diagnostics for the register indices recorded in an abstract state.

The diagnostic scans the optional flag comparison first, followed by relational facts and
links, matching the conjunction order of `AbsState.indicesOk`. Within a record, its first invalid
register is reported.
-/

namespace M0Crypto.Release.ConstantTime

def regIndexCheck (r : Nat) : Bool := decide (r < numRegs) && !(r == 13)

def opndIndexCheck : Opnd → Bool
  | .reg r => regIndexCheck r
  | .imm _ => true

def cmpIndexCheck (c : Cmp) : Bool := regIndexCheck c.a && opndIndexCheck c.b

def aflIndexCheck (f : AFl) : Bool :=
  match f.cmp with
  | none => true
  | some c => cmpIndexCheck c

def factIndexCheck (f : Fact) : Bool := regIndexCheck f.1 && regIndexCheck f.2.1

def linkIndexCheck (l : Lnk) : Bool := regIndexCheck l.i && regIndexCheck l.j

/-- Boolean counterpart of `AbsState.indicesOk`. -/
def AbsState.indicesCheck (s : AbsState) : Bool :=
  aflIndexCheck s.fl && s.rel.all factIndexCheck && s.lnk.all linkIndexCheck

theorem regIndexCheck_eq_true_iff (r : Nat) :
    regIndexCheck r = true ↔ regIndexOk r := by
  simp [regIndexCheck, regIndexOk]

theorem opndIndexCheck_eq_true_iff (o : Opnd) :
    opndIndexCheck o = true ↔ opndIndexOk o := by
  cases o <;> simp [opndIndexCheck, opndIndexOk, regIndexCheck_eq_true_iff]

theorem cmpIndexCheck_eq_true_iff (c : Cmp) :
    cmpIndexCheck c = true ↔ cmpIndexOk c := by
  simp [cmpIndexCheck, cmpIndexOk, regIndexCheck_eq_true_iff,
    opndIndexCheck_eq_true_iff]

theorem aflIndexCheck_eq_true_iff (f : AFl) :
    aflIndexCheck f = true ↔ aflIndexOk f := by
  cases hc : f.cmp with
  | none => simp [aflIndexCheck, hc, aflIndexOk]
  | some c =>
    simp [aflIndexCheck, hc, aflIndexOk, cmpIndexCheck_eq_true_iff]

theorem factIndexCheck_eq_true_iff (f : Fact) :
    factIndexCheck f = true ↔ factIndexOk f := by
  simp [factIndexCheck, factIndexOk, regIndexCheck_eq_true_iff]

theorem linkIndexCheck_eq_true_iff (l : Lnk) :
    linkIndexCheck l = true ↔ linkIndexOk l := by
  simp [linkIndexCheck, linkIndexOk, regIndexCheck_eq_true_iff]

theorem AbsState.indicesCheck_eq_true_iff (s : AbsState) :
    s.indicesCheck = true ↔ s.indicesOk := by
  have hfl : aflIndexCheck s.fl = true ↔ aflIndexOk s.fl :=
    aflIndexCheck_eq_true_iff s.fl
  have hrel : s.rel.all factIndexCheck = true ↔ ∀ f ∈ s.rel, factIndexOk f := by
    simp [List.all_eq_true, factIndexCheck_eq_true_iff]
  have hlnk : s.lnk.all linkIndexCheck = true ↔ ∀ l ∈ s.lnk, linkIndexOk l := by
    simp [List.all_eq_true, linkIndexCheck_eq_true_iff]
  change (aflIndexCheck s.fl && s.rel.all factIndexCheck &&
    s.lnk.all linkIndexCheck) = true ↔
    (aflIndexOk s.fl ∧ (∀ f ∈ s.rel, factIndexOk f) ∧
      ∀ l ∈ s.lnk, linkIndexOk l)
  rw [Bool.and_eq_true, Bool.and_eq_true, hfl, hrel, hlnk]
  constructor
  · rintro ⟨⟨hfl, hrel⟩, hlnk⟩
    exact ⟨hfl, ⟨hrel, hlnk⟩⟩
  · rintro ⟨hfl, ⟨hrel, hlnk⟩⟩
    exact ⟨⟨hfl, hrel⟩, hlnk⟩

/-- The first invalid register record, including the first invalid register in it. -/
inductive IndexFailure where
  | flagCmp (cmp : Cmp) (register : Nat)
  | fact (record : Fact) (register : Nat)
  | link (record : Lnk) (register : Nat)
  deriving DecidableEq, Repr

def opndIndexFailure? : Opnd → Option Nat
  | .reg r => if regIndexCheck r then none else some r
  | .imm _ => none

def cmpIndexFailure? (c : Cmp) : Option Nat :=
  if regIndexCheck c.a then opndIndexFailure? c.b else some c.a

def factIndexFailure? (f : Fact) : Option Nat :=
  if regIndexCheck f.1 then
    if regIndexCheck f.2.1 then none else some f.2.1
  else some f.1

def linkIndexFailure? (l : Lnk) : Option Nat :=
  if regIndexCheck l.i then
    if regIndexCheck l.j then none else some l.j
  else some l.i

def factFailure? : List Fact → Option IndexFailure
  | [] => none
  | f :: fs =>
    match factIndexFailure? f with
    | some r => some (.fact f r)
    | none => factFailure? fs

def linkFailure? : List Lnk → Option IndexFailure
  | [] => none
  | l :: ls =>
    match linkIndexFailure? l with
    | some r => some (.link l r)
    | none => linkFailure? ls

/-- First invalid index record, if any. This is intended for use with `#eval`. -/
def AbsState.indicesFailure (s : AbsState) : Option IndexFailure :=
  match s.fl.cmp with
  | some c =>
    match cmpIndexFailure? c with
    | some r => some (.flagCmp c r)
    | none =>
      match factFailure? s.rel with
      | some e => some e
      | none => linkFailure? s.lnk
  | none =>
    match factFailure? s.rel with
    | some e => some e
    | none => linkFailure? s.lnk

theorem opndIndexFailure?_eq_none (o : Opnd) :
    opndIndexFailure? o = none ↔ opndIndexCheck o = true := by
  cases o <;> simp [opndIndexFailure?, opndIndexCheck, regIndexCheck]

theorem cmpIndexFailure?_eq_none (c : Cmp) :
    cmpIndexFailure? c = none ↔ cmpIndexCheck c = true := by
  unfold cmpIndexFailure? cmpIndexCheck
  by_cases h : regIndexCheck c.a = true <;> simp [h, opndIndexFailure?_eq_none]

theorem factIndexFailure?_eq_none (f : Fact) :
    factIndexFailure? f = none ↔ factIndexCheck f = true := by
  unfold factIndexFailure? factIndexCheck
  by_cases h : regIndexCheck f.1 = true <;>
    by_cases h' : regIndexCheck f.2.1 = true <;> simp [h, h']

theorem linkIndexFailure?_eq_none (l : Lnk) :
    linkIndexFailure? l = none ↔ linkIndexCheck l = true := by
  unfold linkIndexFailure? linkIndexCheck
  by_cases h : regIndexCheck l.i = true <;>
    by_cases h' : regIndexCheck l.j = true <;> simp [h, h']

theorem factFailure_eq_none (fs : List Fact) :
    factFailure? fs = none ↔ fs.all factIndexCheck = true := by
  induction fs with
  | nil => simp [factFailure?]
  | cons f fs ih =>
    simp only [factFailure?, List.all_cons, Bool.and_eq_true]
    cases h : factIndexFailure? f with
    | none => simp [h, (factIndexFailure?_eq_none f).mp h, ih]
    | some r =>
      have hf : factIndexCheck f ≠ true := by
        intro ht
        have := (factIndexFailure?_eq_none f).mpr ht
        simp [h] at this
      simp [h, hf]

theorem linkFailure_eq_none (ls : List Lnk) :
    linkFailure? ls = none ↔ ls.all linkIndexCheck = true := by
  induction ls with
  | nil => simp [linkFailure?]
  | cons l ls ih =>
    simp only [linkFailure?, List.all_cons, Bool.and_eq_true]
    cases h : linkIndexFailure? l with
    | none => simp [h, (linkIndexFailure?_eq_none l).mp h, ih]
    | some r =>
      have hl : linkIndexCheck l ≠ true := by
        intro ht
        have := (linkIndexFailure?_eq_none l).mpr ht
        simp [h] at this
      simp [h, hl]

theorem AbsState.indicesFailure_eq_none (s : AbsState) :
    s.indicesFailure = none ↔ s.indicesCheck = true := by
  have hp : (match factFailure? s.rel with
      | some e => some e
      | none => linkFailure? s.lnk) = none ↔
      s.rel.all factIndexCheck = true ∧ s.lnk.all linkIndexCheck = true := by
    cases h : factFailure? s.rel with
    | none =>
      have hs := (factFailure_eq_none s.rel).mp h
      simp only [h, hs, true_and, linkFailure_eq_none]
    | some e =>
      have hs : s.rel.all factIndexCheck ≠ true := by
        intro ht
        have hh := (factFailure_eq_none s.rel).mpr ht
        simp [h] at hh
      simp [hs]
  cases hc : s.fl.cmp with
  | none => simpa only [AbsState.indicesFailure, AbsState.indicesCheck, aflIndexCheck, hc,
      Bool.true_and, Bool.and_eq_true] using hp
  | some c =>
    cases he : cmpIndexFailure? c with
    | none =>
      have hcmp := (cmpIndexFailure?_eq_none c).mp he
      simpa only [AbsState.indicesFailure, AbsState.indicesCheck, aflIndexCheck, hc, he, hcmp,
        Bool.true_and, Bool.and_eq_true] using hp
    | some r =>
      have hcmp : cmpIndexCheck c ≠ true := by
        intro ht
        have := (cmpIndexFailure?_eq_none c).mpr ht
        simp [he] at this
      simp [AbsState.indicesFailure, AbsState.indicesCheck, aflIndexCheck, hc, he, hcmp]

end M0Crypto.Release.ConstantTime
