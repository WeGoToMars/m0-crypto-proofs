import M0Crypto.Release.Ed25519DsmBody
import M0Crypto.Release.Ed25519TablesCompact
import M0Crypto.Release.Ed25519TablesFast

/-!
# `m0c_ge_dsm`'s values up to `p`

* `dsV_er`, `dsBV_er`: the callees' and the block's values keep `VR` (field values equal modulo
  `p`);
* `ops_ok`, `runs_ok`: every source of the updates is a view or a field element at one of the
  buffer offsets `XL` (`A`, the zero and `2 d`, `m0c_ed_odd_b`), for digits of widths `3` and `5`;
* `dsm_er`: two runs whose buffers hold those field elements equal modulo `p` end with values
  related by `VR`;
* `dsmPre`, `dsmSem`: the premise on `ge_dsm`'s input values and their semantics, the run over a
  memory `mS` that holds `A`'s values modulo `p`, the digit bytes and the code;
* `dsm_sem`: under `dsmPre`, `dsmSem` gives `p2` values of `[s]B − [h]A`.
-/

namespace M0Crypto.Release.Ed25519DsmSem

open M0Crypto.Armv6M (Word Reg Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GlueRun
open M0Crypto.Release.Ed25519GeProg (FA faV vop)
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519DsmVal
open M0Crypto.Release.Ed25519MulBaseVal (frR identV)
open M0Crypto.Release.Ed25519WnafDigits (Digit)
open M0Crypto.Release.Field25519Congr (ModP)

/-! ## The callees keep values up to `p` -/

theorem vop_er {g : Int → Int → Int} (hg : ∀ {a a' b b'}, ModP a a' → ModP b b' → ModP (g a b) (g a' b'))
    {x x' y y' : V} (hx : VR x x') (hy : VR y y') : VR (vop g x y) (vop g x' y') := by
  rcases hx.cases with ⟨a, a', rfl, rfl, ha⟩ | rfl
  · rcases hy.cases with ⟨b, b', rfl, rfl, hb⟩ | rfl
    · exact hg ha hb
    · cases y <;> first | exact hg ha (ModP.refl _) | exact VR.refl _
  · rcases hy.cases with ⟨b, b', rfl, rfl, hb⟩ | rfl
    · cases x <;> first | exact hg (ModP.refl _) hb | exact VR.refl _
    · exact VR.refl _

theorem faV_er (a : FA) {vs vs' : List V} (h : All2 VR vs vs') : VR (faV a vs) (faV a vs') := by
  rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> rcases vs' with _ | ⟨x', _ | ⟨y', _ | ⟨z', vs'⟩⟩⟩ <;>
    simp only [All2, and_true, and_false] at h
  · exact VR.refl _
  · cases a
    case sqr => exact vop_er (fun h1 h2 => ModP.mul h1 h2) h h
    all_goals exact VR.refl _
  · cases a
    case add => exact vop_er (fun h1 h2 => ModP.add h1 h2) h.1 h.2
    case sub => exact vop_er (fun h1 h2 => ModP.sub h1 h2) h.1 h.2
    case mul => exact vop_er (fun h1 h2 => ModP.mul h1 h2) h.1 h.2
    all_goals exact VR.refl _
  · cases a <;> exact VR.refl _

theorem copy_er {vs vs' : List V} (h : All2 VR vs vs') :
    VR (Ed25519FePow.paV .copyOut vs) (Ed25519FePow.paV .copyOut vs') := by
  rcases vs with _ | ⟨x, _ | ⟨y, vs⟩⟩ <;> rcases vs' with _ | ⟨x', _ | ⟨y', vs'⟩⟩ <;>
    simp only [All2, and_true, and_false] at h
  · exact VR.refl _
  · rcases h.cases with ⟨a, a', rfl, rfl, ha⟩ | rfl
    · exact ha
    · exact VR.refl _
  · cases x <;> cases x' <;> exact VR.refl _

theorem dsV_er : ∀ (a : DS) {vs vs' : List V}, All2 VR vs vs' → All2 VR (dsV a vs) (dsV a vs')
  | .f a, _, _, h => ⟨faV_er a h, trivial⟩
  | .copy, _, _, h => ⟨copy_er h, trivial⟩
  | .copy2, _, _, h => h
  | .copy3, _, _, h => h
  | .zero, _, _, _ => all2_rfl _

theorem all2_b : ∀ {ls : List (List Spec.Ed25519.Byte)} {vs : List V}, All2 VR (ls.map V.b) vs → vs = ls.map V.b
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, t⟩ => by rw [all2_b t]; exact congrArg (· :: _) (Eq.symm h)

theorem all2_b' : ∀ {ls : List (List Spec.Ed25519.Byte)} {vs : List V}, All2 VR vs (ls.map V.b) → vs = ls.map V.b
  | [], [], _ => rfl
  | _ :: _, v :: _, ⟨h, t⟩ => by
    rw [all2_b' t]
    rcases h.cases with ⟨_, _, -, h, -⟩ | h
    · cases h
    · exact congrArg (· :: _) h

/-- Four byte values. -/
def IsB4 (vs : List V) : Prop := ∃ a b c d, vs = [.b a, .b b, .b c, .b d]

theorem identV_none {vs : List V} (h : ¬ IsB4 vs) : identV vs = [.none, .none, .none, .none] := by
  unfold identV
  split
  · exact absurd ⟨_, _, _, _, rfl⟩ h
  · rfl

theorem identV_eq {vs vs' : List V} (h : All2 VR vs vs') : identV vs = identV vs' := by
  by_cases h1 : IsB4 vs
  · obtain ⟨a, b, c, d, rfl⟩ := h1
    rw [all2_b (ls := [a, b, c, d]) h]; rfl
  · by_cases h2 : IsB4 vs'
    · obtain ⟨a, b, c, d, rfl⟩ := h2
      exact absurd ⟨a, b, c, d, all2_b' (ls := [a, b, c, d]) h⟩ h1
    · rw [identV_none h1, identV_none h2]

theorem dsBV_er : ∀ (b : DB) {vs vs' : List V}, All2 VR vs vs' → All2 VR (dsBV b vs) (dsBV b vs')
  | .ident, _, _, h => by simp only [dsBV]; rw [identV_eq h]; exact all2_rfl _

/-! ## The sources -/

/-- The buffer offsets whose field elements the updates read: `A`'s four, the zero and `2 d`,
`m0c_ed_odd_b`'s 24. -/
def XL : List (Nat × Nat) :=
  [(3, 0), (3, 32), (3, 64), (3, 96), (4, 0), (4, 96)] ++ (List.range 24).map fun j => (5, 32 * j)

def srcB : Src → Bool
  | .view _ => true
  | .extF ⟨.ex r o, .k n⟩ => n == 32 && decide ((r, o) ∈ XL)
  | _ => false

def opB (r : ROp DS DB) : Bool := (srcsOf r).all srcB

theorem ops_ok : (preR ++ idR ++ endR ++ dblR ++ cvR true ++ cvR false).all opB = true ∧
    (∀ k < 2, ∀ s < 2, (frR DS.f (saL k s)).all opB = true) ∧
    ∀ k < 8, ∀ s < 2, (frR DS.f (sbL k s)).all opB = true := by
  decide +kernel

theorem pass_ok {a b : Int} (ha : Digit 3 a) (hb : Digit 5 b) : (passR a b).all opB = true := by
  obtain ⟨h0, hsa, hsb⟩ := ops_ok
  simp only [List.all_append, Bool.and_eq_true] at h0
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hd⟩, ht⟩, hf⟩ := h0
  unfold passR
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨hd, by cases (a != 0 || b != 0) <;> assumption⟩, ?_⟩, ?_⟩
  · split
    · rfl
    · rename_i h
      simp only [List.all_append, Bool.and_eq_true]
      exact ⟨hsa _ (dig3 ha h).2 _ (sgn_lt a), by cases (b != 0) <;> assumption⟩
  · split
    · rfl
    · rename_i h
      simp only [List.all_append, Bool.and_eq_true]
      exact ⟨hsb _ (dig5 hb h).2 _ (sgn_lt b), hf⟩

theorem runs_ok {hd sd : Nat → Int} : ∀ n, (∀ i < n, Digit 3 (hd i) ∧ Digit 5 (sd i)) → (runsR hd sd n).all opB = true
  | 0, _ => rfl
  | n + 1, h => by
    rw [runsR, List.all_append, pass_ok (h n (by omega)).1 (h n (by omega)).2, runs_ok n fun i hi => h i (by omega)]
    rfl

/-- **The run's updates**, for digits of widths `3` and `5`. -/
theorem all_ok {hd sd : Nat → Int} {n : Nat} (h : ∀ i < n, Digit 3 (hd i) ∧ Digit 5 (sd i)) :
    (preR ++ idR ++ runsR hd sd n ++ endR).all opB = true := by
  have h0 := ops_ok.1
  simp only [List.all_append, Bool.and_eq_true] at h0 ⊢
  exact ⟨⟨h0.1.1.1.1, runs_ok n h⟩, h0.1.1.1.2⟩

/-- Two runs' buffers hold the field elements at `XL` equal modulo `p`. -/
def W (c : Ctx) (m0 : Mem) (c' : Ctx) (m0' : Mem) : Prop :=
  ∀ x ∈ XL, ModP (Field25519Routines.feVal m0 (c.ptr x.1 + BitVec.ofNat 32 x.2))
    (Field25519Routines.feVal m0' (c'.ptr x.1 + BitVec.ofNat 32 x.2))

theorem sok_ex {c c' : Ctx} {m0 m0' : Mem} {r o : Nat}
    (h : ModP (Field25519Routines.feVal m0 (c.ptr r + BitVec.ofNat 32 o)) (Field25519Routines.feVal m0' (c'.ptr r + BitVec.ofNat 32 o))) :
    SOk dsGeo c m0 c' m0' (.extF ⟨.ex r o, .k 32⟩) := h

theorem sok {c c' : Ctx} {m0 m0' : Mem} (hw : W c m0 c' m0') (s : Src) (h : srcB s = true) :
    SOk dsGeo c m0 c' m0' s := by
  cases s with
  | view => trivial
  | extF r =>
    obtain ⟨l, len⟩ := r
    cases l with
    | ex r o =>
      cases len with
      | k n =>
        simp only [srcB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        exact sok_ex (hw (r, o) h)
      | p => simp only [srcB, Bool.false_eq_true] at h
    | fr => simp only [srcB, Bool.false_eq_true] at h
    | rg => simp only [srcB, Bool.false_eq_true] at h
  | slice => simp only [srcB, Bool.false_eq_true] at h
  | ext => simp only [srcB, Bool.false_eq_true] at h
  | pv => simp only [srcB, Bool.false_eq_true] at h

/-- **Two runs up to `p`**: from values related by `VR`, two runs over buffers that hold the field
elements at `XL` equal modulo `p` keep them related, for digits of widths `3` and `5`. -/
theorem dsm_er {c c' : Ctx} {m0 m0' : Mem} (hw : W c m0 c' m0') {hd sd : Nat → Int} {n : Nat}
    (hn : ∀ i < n, Digit 3 (hd i) ∧ Digit 5 (sd i)) {E E' : Loc → V} (h : ER E E') :
    ER (runD c m0 (preR ++ idR ++ runsR hd sd n ++ endR) E) (runD c' m0' (preR ++ idR ++ runsR hd sd n ++ endR) E') :=
  run_er (fun a _ _ => dsV_er a) (fun b _ _ => dsBV_er b) _ h fun r hr s hs =>
    sok hw s (List.all_eq_true.mp (List.all_eq_true.mp (all_ok hn) r hr) s hs)

/-! ## The semantics -/

open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Thumb (CodeAt)
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519DsmBlocks (digOf)
open M0Crypto.Release.Ed25519ScalarMul (dsmTop)
open M0Crypto.Release.Ed25519VerifyVal (wnafBytes)
open M0Crypto.Release.Ed25519GeProg (RepV Rep2V fI fI_emod)
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Release.Ed25519Bridge (Bpt)
open M0Crypto.Artifacts.Ed25519Compact (ed_zero ed_odd_b)
open M0Crypto.Spec.Ed25519 (L encodeInt decodeInt)

/-- The bytes `l` from address `0` and the code `B` from `2^31`. -/
def lmem (l B : List Spec.Ed25519.Byte) : Mem := fun y =>
  if y.toNat < 2 ^ 31 then l.getD y.toNat 0 else B.getD (y.toNat - 2 ^ 31) 0

theorem lmem_bytes {l B : List Spec.Ed25519.Byte} {o n : Nat} (h : o + n ≤ l.length) (h31 : l.length ≤ 2 ^ 31) :
    bytesAt (lmem l B) (BitVec.ofNat 32 o) n = (l.drop o).take n := by
  apply List.ext_getElem (by simp only [Footprint.bytesAt_length, List.length_take, List.length_drop]; omega)
  intro i h1 _
  have e : (BitVec.ofNat 32 o + BitVec.ofNat 32 i).toNat = o + i := by
    simp only [Footprint.bytesAt_length] at h1
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, lmem, e]
  simp only [Footprint.bytesAt_length] at h1
  rw [ite_eq_left (show o + i < 2 ^ 31 by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem lmem_code {l B : List Spec.Ed25519.Byte} (h : B.length < 2 ^ 31) : CodeAt (lmem l B) (BitVec.ofNat 32 (2 ^ 31)) B := by
  intro i hi
  have e : (BitVec.ofNat 32 (2 ^ 31) + BitVec.ofNat 32 i).toNat = 2 ^ 31 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [lmem, e]
  rw [ite_eq_right (show ¬ 2 ^ 31 + i < 2 ^ 31 by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- A field value's integer. -/
def fv : V → Int
  | .f x => x
  | _ => 0

/-- The bytes of field values modulo `p`. -/
def encA (xs : List V) : List Spec.Ed25519.Byte := xs.flatMap fun v => encodeInt (fv v % Field25519Congr.p).toNat

/-- The context of `mS`: `A` at `0`, the zero and `2 d` and `m0c_ed_odd_b` in the code. -/
def cS : Ctx where
  base := BitVec.ofNat 32 (2 ^ 31)
  sp0 := 0
  ptr := fun i => if i = 4 then BitVec.ofNat 32 (2 ^ 31 + ed_zero) else if i = 5 then BitVec.ofNat 32 (2 ^ 31 + ed_odd_b) else 0
  prm := fun _ => 0

/-- The memory of `ge_dsm`'s semantics: `A`'s values modulo `p` at `0`, the digit bytes of `s` at
`128` and of `h` at `384`, build `b`'s code from `2^31`. -/
def mS (b : Build) (xs : List V) (l1 l2 : List Spec.Ed25519.Byte) : Mem := lmem (encA xs ++ l1 ++ l2) b.bytes

/-- **`m0c_ge_dsm`'s premise on its input values**: the digit bytes are `wnafBytes 5 s` and
`wnafBytes 3 h` for some `s, h < L`, and the four field values represent some point `A` as `p3`. -/
def dsmPre (vs : List V) : Prop :=
  ∃ s h : Nat, s < L ∧ h < L ∧ ∃ xs A, vs = .b (wnafBytes 5 s) :: .b (wnafBytes 3 h) :: xs ∧ RepV xs A

/-- **`m0c_ge_dsm`'s semantics**: its outputs from the run over `mS`. -/
def dsmSem (b : Build) : List V → List V
  | .b l1 :: .b l2 :: xs =>
    let m := mS b xs l1 l2
    let E := runD cS m (preR ++ idR ++ runsR (digOf m (BitVec.ofNat 32 384)) (digOf m (BitVec.ofNat 32 128))
      (dsmTop (digOf m (BitVec.ofNat 32 128)) (digOf m (BitVec.ofNat 32 384)) 256) ++ endR) fun _ => .none
    [E (.ex 0 0), E (.ex 0 32), E (.ex 0 64)]
  | _ => []

theorem tables_ok : ∀ b : Build, Ed25519Tables.TablesOk b
  | .compact => Ed25519TablesCompact.tables_ok
  | .fast => Ed25519TablesFast.tables_ok

theorem wnafBytes_length (w k : Nat) : (wnafBytes w k).length = 256 := by simp [wnafBytes]

theorem enc_drop (n : Nat) {k : Nat} (h : 32 ≤ k) : (encodeInt n).drop k = [] :=
  List.drop_eq_nil_of_le (by rw [encodeInt_length]; exact h)

section
variable (b : Build) (x y z t : Int) (l1 l2 : List Spec.Ed25519.Byte)

/-- The bytes of `mS`. -/
theorem mS_bytes (h1 : l1.length = 256) (h2 : l2.length = 256) :
    let m := mS b [.f x, .f y, .f z, .f t] l1 l2
    bytesAt m (BitVec.ofNat 32 128) 256 = l1 ∧ bytesAt m (BitVec.ofNat 32 384) 256 = l2 ∧
      bytesAt m (BitVec.ofNat 32 0) 32 = encodeInt (x % Field25519Congr.p).toNat ∧
      bytesAt m (BitVec.ofNat 32 32) 32 = encodeInt (y % Field25519Congr.p).toNat ∧
      bytesAt m (BitVec.ofNat 32 64) 32 = encodeInt (z % Field25519Congr.p).toNat ∧
      bytesAt m (BitVec.ofNat 32 96) 32 = encodeInt (t % Field25519Congr.p).toNat := by
  have hl : (encA [.f x, .f y, .f z, .f t]).length = 128 := by simp [encA, encodeInt_length]
  have hL : (encA [.f x, .f y, .f z, .f t] ++ l1 ++ l2).length = 640 := by simp only [List.length_append, hl, h1, h2]
  simp only [mS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [lmem_bytes (by omega) (by omega)] <;>
    simp [encA, fv, List.drop_append, encodeInt_length, h1, h2, enc_drop, List.take_of_length_le]


theorem feS {m : Mem} {o : Nat} {x : Int} (h : bytesAt m (BitVec.ofNat 32 o) 32 = encodeInt (x % Field25519Congr.p).toNat) :
    (Field25519Routines.feVal m (BitVec.ofNat 32 o) : Int) = x % Field25519Congr.p := by
  have h0 : 0 ≤ x % Field25519Congr.p := Int.emod_nonneg _ (by decide)
  have h1 : x % Field25519Congr.p < Field25519Congr.p := Int.emod_lt_of_pos _ (by decide)
  have h2 : (x % Field25519Congr.p).toNat < 2 ^ 256 := by simp only [Field25519Congr.p] at h0 h1 ⊢; omega
  rw [← Ed25519GeCompressProg.dec_fe, h, decodeInt_encodeInt, Nat.mod_eq_of_lt h2, Int.toNat_of_nonneg h0]

theorem cS3 (m : Mem) (o : Nat) :
    Field25519Routines.feVal m (cS.ptr 3 + BitVec.ofNat 32 o) = Field25519Routines.feVal m (BitVec.ofNat 32 o) := by
  rw [show cS.ptr 3 = 0#32 from rfl, BitVec.zero_add]

theorem xF_S {m : Mem} {o : Nat} {x : Int} (h : bytesAt m (BitVec.ofNat 32 o) 32 = encodeInt (x % Field25519Congr.p).toNat) :
    fI (xF cS m 3 o) = fI x := by
  have e1 : xF cS m 3 o = (Field25519Routines.feVal m (BitVec.ofNat 32 o) : Int) :=
    congrArg (fun n : Nat => (n : Int)) (cS3 m o)
  rw [e1, feS h, fI_emod]

/-- **`m0c_ge_dsm`'s semantics represent `[s]B − [h]A`** when `dsmPre` holds: the digit bytes are
`wnafBytes 5 s` and `wnafBytes 3 h`, `s, h < L`, and the four field values represent `A`. -/
theorem dsm_sem (b : Build) {s h : Nat} {xs : List V} {A : EdPt} (hs : s < L) (hh : h < L) (hA : RepV xs A) :
    Rep2V (dsmSem b (.b (wnafBytes 5 s) :: .b (wnafBytes 3 h) :: xs)) ((s : Int) • Bpt - (h : Int) • A) := by
  obtain ⟨x, y, z, t, rfl, hr⟩ := hA
  obtain ⟨b1, b2, e0, e1, e2, e3⟩ := mS_bytes b x y z t _ _ (wnafBytes_length 5 s) (wnafBytes_length 3 h)
  have hc : CodeAt (mS b [.f x, .f y, .f z, .f t] (wnafBytes 5 s) (wnafBytes 3 h)) (BitVec.ofNat 32 (2 ^ 31)) b.bytes :=
    lmem_code (by rw [Ed25519.Build.bytes_length]; cases b <;> decide)
  simp only [dsmSem]
  generalize mS b [.f x, .f y, .f z, .f t] (wnafBytes 5 s) (wnafBytes 3 h) = m at b1 b2 e0 e1 e2 e3 hc ⊢
  have hK := k_ok b hc (show cS.ptr 4 = BitVec.ofNat 32 (2 ^ 31) + BitVec.ofNat 32 ed_zero by decide)
  have hOB := ob_ok b hc (tables_ok b) (show cS.ptr 5 = BitVec.ofNat 32 (2 ^ 31) + BitVec.ofNat 32 ed_odd_b by decide)
  have hRA : RepV (aV cS m) A := ⟨_, _, _, _, rfl, by rw [xF_S e0, xF_S e1, xF_S e2, xF_S e3]; exact hr⟩
  obtain ⟨hR0, hk⟩ := id_val (c := cS) (m0 := m) (runD cS m preR fun _ => .none)
  obtain ⟨-, hR⟩ := loop_val (bE := dbS) (semB := dsBV) hSD hs hh b1 b2 hOB ((pre_val hRA hK _).of hk) hR0
  simp only [runD_app]
  rw [end_val]
  exact hR


/-! ## A run's values against the semantics -/

theorem code_fe {m : Mem} {base : Word} {B : List Spec.Ed25519.Byte} (hc : CodeAt m base B) {off : Nat}
    (h : off + 32 ≤ B.length) : Field25519Routines.feVal m (base + BitVec.ofNat 32 off) = decodeInt ((B.drop off).take 32) := by
  rw [← Ed25519GeCompressProg.dec_fe, Ed25519ScReduceProg.code_bytes hc h]

theorem code_same {m m' : Mem} {base base' : Word} {B : List Spec.Ed25519.Byte} (hc : CodeAt m base B)
    (hc' : CodeAt m' base' B) {off o : Nat} (h : off + o + 32 ≤ B.length) :
    Field25519Routines.feVal m (base + BitVec.ofNat 32 off + BitVec.ofNat 32 o) =
      Field25519Routines.feVal m' (base' + BitVec.ofNat 32 off + BitVec.ofNat 32 o) := by
  rw [Thumb.ofNat_add_assoc, Thumb.ofNat_add_assoc, code_fe hc h, code_fe hc' h]

theorem dig_eq {m m' : Mem} {a a' : Word} (h : bytesAt m a 256 = bytesAt m' a' 256) :
    ∀ i < 256, digOf m a i = digOf m' a' i := by
  intro i hi
  have e := congrArg (·[i]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at e
  rw [digOf, digOf, e]

theorem runsR_congr {hd sd hd' sd' : Nat → Int} :
    ∀ n, (∀ i < n, hd i = hd' i ∧ sd i = sd' i) → runsR hd sd n = runsR hd' sd' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [runsR, runsR, (h n (by omega)).1, (h n (by omega)).2, runsR_congr n fun i hi => h i (by omega)]

/-- **A run against the semantics**: over a memory with build `b`'s code, the digit bytes of
`wnaf 5 s` and `wnaf 3 h` (`s, h < L`) and field elements equal modulo `p` to `x, y, z, t`, the
updates over the digits leave outputs related by `VR` to `dsmSem`'s. -/
theorem dsm_vr (b : Build) {c : Ctx} {m0 : Mem} {s h : Nat} {x y z t : Int} (hs : s < L) (hh : h < L)
    (hc : CodeAt m0 c.base b.bytes) (h4 : c.ptr 4 = c.base + BitVec.ofNat 32 ed_zero)
    (h5 : c.ptr 5 = c.base + BitVec.ofNat 32 ed_odd_b)
    (b1 : bytesAt m0 (c.ptr 1) 256 = wnafBytes 5 s) (b2 : bytesAt m0 (c.ptr 2) 256 = wnafBytes 3 h)
    (a0 : ModP (Field25519Routines.feVal m0 (c.ptr 3 + BitVec.ofNat 32 0)) x)
    (a1 : ModP (Field25519Routines.feVal m0 (c.ptr 3 + BitVec.ofNat 32 32)) y)
    (a2 : ModP (Field25519Routines.feVal m0 (c.ptr 3 + BitVec.ofNat 32 64)) z)
    (a3 : ModP (Field25519Routines.feVal m0 (c.ptr 3 + BitVec.ofNat 32 96)) t) :
    let E := runD c m0 (preR ++ idR ++ runsR (digOf m0 (c.ptr 2)) (digOf m0 (c.ptr 1))
      (dsmTop (digOf m0 (c.ptr 1)) (digOf m0 (c.ptr 2)) 256) ++ endR) fun _ => .none
    All2 VR [E (.ex 0 0), E (.ex 0 32), E (.ex 0 64)]
      (dsmSem b [.b (wnafBytes 5 s), .b (wnafBytes 3 h), .f x, .f y, .f z, .f t]) := by
  obtain ⟨b1', b2', e0, e1, e2, e3⟩ := mS_bytes b x y z t _ _ (wnafBytes_length 5 s) (wnafBytes_length 3 h)
  have hc' : CodeAt (mS b [.f x, .f y, .f z, .f t] (wnafBytes 5 s) (wnafBytes 3 h)) (BitVec.ofNat 32 (2 ^ 31)) b.bytes :=
    lmem_code (by rw [Ed25519.Build.bytes_length]; cases b <;> decide)
  have hL : ed_zero + 128 ≤ b.bytes.length ∧ ed_odd_b + 768 ≤ b.bytes.length := by
    rw [Ed25519.Build.bytes_length]; cases b <;> decide
  simp only [dsmSem]
  generalize mS b [.f x, .f y, .f z, .f t] (wnafBytes 5 s) (wnafBytes 3 h) = m at b1' b2' e0 e1 e2 e3 hc' ⊢
  have d1 := dig_eq (b1.trans b1'.symm)
  have d2 := dig_eq (b2.trans b2'.symm)
  have ht := Ed25519VerifyVal.dsmTop_congr 256 fun i hi => ⟨d1 i hi, d2 i hi⟩
  have hn := (Ed25519ScalarMul.dsmTop_spec (digOf m (BitVec.ofNat 32 128)) (digOf m (BitVec.ofNat 32 384)) 256).1
  rw [ht, runsR_congr _ fun i hi => ⟨d2 i (by omega), d1 i (by omega)⟩]
  have hw : W c m0 cS m := by
    have h4S : cS.ptr 4 = BitVec.ofNat 32 (2 ^ 31) + BitVec.ofNat 32 ed_zero := by decide
    have h5S : cS.ptr 5 = BitVec.ofNat 32 (2 ^ 31) + BitVec.ofNat 32 ed_odd_b := by decide
    intro p hp
    simp only [XL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩
    · dsimp only; rw [cS3, feS e0]; exact a0.trans (ModP.emod_left x).symm
    · dsimp only; rw [cS3, feS e1]; exact a1.trans (ModP.emod_left y).symm
    · dsimp only; rw [cS3, feS e2]; exact a2.trans (ModP.emod_left z).symm
    · dsimp only; rw [cS3, feS e3]; exact a3.trans (ModP.emod_left t).symm
    · dsimp only; rw [h4, h4S, code_same hc hc' (by omega)]; exact ModP.refl _
    · dsimp only; rw [h4, h4S, code_same hc hc' (by omega)]; exact ModP.refl _
    · dsimp only; rw [h5, h5S, code_same hc hc' (by omega)]; exact ModP.refl _
  have her := dsm_er hw (n := dsmTop (digOf m (BitVec.ofNat 32 128)) (digOf m (BitVec.ofNat 32 384)) 256) (fun i hi => (Ed25519VerifyVal.verify_digits hs hh b1' b2' i (by omega)).symm)
    (E := fun _ => .none) (E' := fun _ => .none) fun _ => VR.refl _
  exact ⟨her _, her _, her _, trivial⟩

end

end M0Crypto.Release.Ed25519DsmSem
