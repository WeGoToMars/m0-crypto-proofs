import M0Crypto.Release.Ed25519DsmSem
import M0Crypto.Release.Ed25519CallProgCalleeW
import M0Crypto.Release.Ed25519WnafAd

/-!
# `m0c_ge_dsm` at verify's call

* `dq`, `bszD`: the callee with no program body; the body is `0x2832 … 0x2d00`;
* `xpD`, `xpvD`: its extra public values, the 64 words of each digit array; `dP`, `zP`: the digit
  words and the zero tests from them;
* `xpreD`: the digits are of widths `5` and `3`; `PostD`: under `dsmPre`, the outputs hold
  `dsmSem`;
* `dsm_body`: the body's run from `At` at its start to the epilogue, with the trace `ΨD` of the
  public values.
-/

namespace M0Crypto.Release.Ed25519DsmAd

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GlueRun
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519DsmBlocks
open M0Crypto.Release.Ed25519DsmRun
open M0Crypto.Release.Ed25519DsmPass
open M0Crypto.Release.Ed25519DsmLoop
open M0Crypto.Release.Ed25519DsmBody
open M0Crypto.Release.Ed25519DsmSem
open M0Crypto.Release.Ed25519DsmVal (preR idR endR runsR dsV dsBV runD dig3 dig5)
open M0Crypto.Release.Ed25519WnafDigits (Digit)
open M0Crypto.Release.Ed25519WnafAd (wordsAt wordsOf bytesOfW bytes_words wordsAt_eq)
open M0Crypto.Release.Ed25519VerifyProg (ioDsm)
open M0Crypto.Release.Ed25519ScalarMul (dsmTop)
open M0Crypto.Release.Field25519Congr (ModP)

/-! ## The callee and its public values -/

abbrev dq : CalleeP DS DB := dsQ ioDsm .nil

/-- The body's size: from `0x2832` to the epilogue at `0x2d00`. -/
def bszD : Nat := 0x4ce

theorem dq_facts : dq.body = 0x2832 ∧ dq.st0 = stE ∧ dq.epiW bszD = 0x2d00 ∧ dq.okF = true := by decide +kernel

/-- The extra public values: the 64 words of each digit array. -/
def xpD (st : State) : List Word := wordsAt st.mem (st.regs 1) 64 ++ wordsAt st.mem (st.regs 2) 64

def xpvD : List V → List Word
  | .b l1 :: .b l2 :: _ => wordsOf l1 64 ++ wordsOf l2 64
  | _ => []

/-- The public values at entry. -/
abbrev pubD (_ : Word) (st : State) : Nat → Word := dq.s.pubX xpD st

/-- Digit `i` of the array whose words start at public value `o`, as a word. -/
def dP (p : Nat → Word) (o i : Nat) : Word := sw ((bytesOfW (fun j => p (o + j)) 64).getD i 0)

/-- The zero test of index `i` from the public values. -/
def zP (p : Nat → Word) (i : Nat) : Bool := decide ((dP p 69 i).toInt = 0 ∧ (dP p 5 i).toInt = 0)

/-- The digits are of widths `5` (of `s`, at `r1`) and `3` (of `h`, at `r2`). -/
def xpreD (_ : Word) (s : State) : Prop :=
  ∀ i < 256, Digit 5 (digOf s.mem (s.regs 1) i) ∧ Digit 3 (digOf s.mem (s.regs 2) i)

/-- **The result**: under `dsmPre`, the outputs hold `dsmSem`. -/
def PostD (b : Ed25519.Build) (Rs : Rels) (s : State) (m : Mem) (_ : Word) : Prop :=
  ∀ c sp vs, PreV ioDsm c sp s.regs → InsRel Rs c sp ioDsm s vs → dsmPre vs → OutsRel Rs c sp ioDsm s m (dsmSem b vs)

/-- The body's trace at the public values `p`. -/
def ΨD (T : DS → Word → (Nat → Word) → List Event) (base : Word) (p : Nat → Word) : TrP :=
  bodyTr T (dq.ctx base p) (zP p) (dP p 69) (dP p 5) (Tr.is [])

/-! ## The trace is a function of the digits below `256` -/

section tr
variable (T : DS → Word → (Nat → Word) → List Event) (c : Ctx)

theorem lpTr_congr {da db da' db' : Nat → Word} (Ψx : TrP) :
    ∀ n, (∀ i < n, da i = da' i ∧ db i = db' i) → lpTr T c da db Ψx n = lpTr T c da' db' Ψx n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [lpTr]
    rw [(h n (by omega)).1, (h n (by omega)).2, lpTr_congr Ψx n fun i hi => h i (by omega)]

theorem scanTr_congr {z z' : Nat → Bool} {Ψ Ψ' : Nat → TrP} :
    ∀ j, (∀ i ≤ j, z i = z' i) → (∀ k, k ≤ j ∨ k = 2 ^ 32 - 1 → Ψ k = Ψ' k) →
      scanTr (c := c) z Ψ j = scanTr (c := c) z' Ψ' j
  | 0, hz, hΨ => by
    simp only [scanTr, scanHd]
    rw [hz 0 (Nat.le_refl _), hΨ 0 (.inl (Nat.le_refl _)), hΨ (2 ^ 32 - 1) (.inr rfl)]
  | j + 1, hz, hΨ => by
    simp only [scanTr, scanHd]
    rw [hz (j + 1) (Nat.le_refl _), hΨ (j + 1) (.inl (Nat.le_refl _)), hΨ 0 (.inl (Nat.zero_le _)),
      scanTr_congr j (fun i hi => hz i (by omega)) fun k hk => hΨ k (hk.imp_left fun h => by omega)]

theorem bodyTr_congr {z z' : Nat → Bool} {da db da' db' : Nat → Word} (Ψ : TrP)
    (h : ∀ i < 256, z i = z' i ∧ da i = da' i ∧ db i = db' i) :
    bodyTr T c z da db Ψ = bodyTr T c z' da' db' Ψ := by
  simp only [bodyTr]
  rw [scanTr_congr c 255 (fun i hi => (h i (by omega)).1) fun k hk => by
    have := (nOf_spec (by omega : k ≤ 255 ∨ k = 2 ^ 32 - 1)).1
    rw [lpTr_congr T c _ (nOf k) fun i hi => ⟨(h i (by omega)).2.1, (h i (by omega)).2.2⟩]]

end tr

/-- **The scan's count is `dsmTop`'s.** -/
theorem top_eq {z : Nat → Bool} {sd hd : Nat → Int} (hz : ∀ i, z i = decide (hd i = 0 ∧ sd i = 0)) :
    ∀ j, j ≤ 255 → nOf (topI z j) = dsmTop sd hd (j + 1)
  | 0, _ => by
    simp only [topI, dsmTop, hz 0]
    by_cases h : hd 0 = 0 ∧ sd 0 = 0
    · simp [h, nOf]
    · simp [h, nOf]
  | j + 1, hj => by
    simp only [topI, hz (j + 1)]
    rw [dsmTop]
    by_cases h : hd (j + 1) = 0 ∧ sd (j + 1) = 0
    · simp only [h, and_self, decide_true, ↓reduceIte]; exact top_eq hz j (by omega)
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, nOf]
      rw [ite_eq_right (by omega)]

theorem bytesOfW_congr {w w' : Nat → Word} {n : Nat} (h : ∀ j < n, w j = w' j) : bytesOfW w n = bytesOfW w' n :=
  List.map_congr_left fun j hj => by rw [h (j / 4) (by have := List.mem_range.mp hj; omega)]

/-- **The digit arrays from the public values.** -/
theorem pub_bytes (base : Word) (s : State) :
    bytesOfW (fun j => pubD base s (5 + j)) 64 = bytesAt s.mem (s.regs 1) 256 ∧
      bytesOfW (fun j => pubD base s (69 + j)) 64 = bytesAt s.mem (s.regs 2) 256 := by
  have hl : ∀ r, (wordsAt s.mem (s.regs r) 64).length = 64 := fun _ => by simp [wordsAt]
  have hp : dq.s.pubs.length = 5 := by decide
  refine ⟨?_, ?_⟩ <;> rw [show (256 : Nat) = 4 * 64 from rfl, ← bytes_words] <;> refine bytesOfW_congr fun j hj => ?_ <;>
    simp only [pubD, CalleeS.pubX, pubOf, xpD, List.getD_eq_getElem?_getD]
  · rw [List.getElem?_append_right (by simp [hp]), List.getElem?_append_left (by simp [hl, hp]; omega)]
    simp [hp]
  · rw [List.getElem?_append_right (by simp [hp]; omega), List.getElem?_append_right (by simp [hl, hp]; omega)]
    simp only [List.length_map, hp, hl]
    rw [show 69 + j - 5 - 64 = j by omega]

/-! ## The body's run -/

theorem io_eq : ioDsm.ins = [(1, 0, .view (.bytes 256)), (2, 0, .view (.bytes 256)), (3, 0, In.view .fe),
      (3, 32, In.view .fe), (3, 64, In.view .fe), (3, 96, In.view .fe)] ∧
    ioDsm.outs = [(0, 0, .fe), (0, 32, .fe), (0, 64, .fe)] := ⟨rfl, rfl⟩

/-- A `.fe` view's value related by `VR` to `w` gives `w` at the same bytes. -/
theorem rel_fe {Rs : Rels} {c c' : Ctx} {sp sp' : Word} {m : Mem} {a : Word} {v w : V}
    (h : Rel Rs c sp .fe m a v) (hv : VR v w) : Rel Rs c' sp' .fe m a w := by
  rcases hv.cases with ⟨x, y, rfl, rfl, hxy⟩ | rfl
  · exact ModP.trans h hxy
  · cases v <;> exact h

theorem runA_D {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {ads : ∀ a, Ad Rs B BS (dsS a)}
    {bds : ∀ b, Bd Rs (dbS b)} (hA : ∀ a, (ads a).sem = dsV a) (hB : ∀ b, (bds b).sem = dsBV b) (c : Ctx) (m0 : Mem)
    (L : List (ROp DS DB)) (E : Loc → V) : runA ads bds c m0 L E = runD c m0 L E := by
  simp only [runA, runD]
  rw [show (fun a => (ads a).sem) = dsV from funext hA, show (fun b => (bds b).sem) = dsBV from funext hB]

theorem send_outs : (∀ o ∈ [0, 32, 64], (Loc.ex 0 o, Kd.fe) ∈ Send.Γ ∧ Loc.ex 0 o ∉ N) := by decide +kernel

section body
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {Rs : Rels}

/-- **The body** from its start to the epilogue at `0x2d00`: the trace `ΨD` of the public values
and, under `dsmPre`, the outputs of `dsmSem`. -/
theorem dsm_body (b : Ed25519.Build) (hB : B = b.bytes) (cd : Code B BS) (cl : CodeL B BS) (cb : CodeB B BS)
    (ads : ∀ a, Ad Rs B BS (dsS a)) (bds : ∀ k, Bd Rs (dbS k)) (hA : ∀ a, (ads a).sem = dsV a)
    (hBd : ∀ k, (bds k).sem = dsBV k) (base : Word) (s : State) (e : (dq.RW (PostD b Rs) xpreD).Entry base s)
    (t : State) {Wc Rc : List Rgn} (g : GeoOk (dq.ctx base (pubD base s)) dsGeo Wc Rc)
    (F : Caller base (dq.ctx base (pubD base s)).sp0 dsGeo.N Wc) (hcR : Sub [codeR base] Rc)
    (hat : At Rs B (dq.ctx base (pubD base s)) dsGeo t.mem dq.body dq.st0 (fun _ => .none) t)
    (hrd : ∀ i (x : XInfo), dsGeo.xs[i]? = some x → x.r = true →
      ∀ y, Has (x.rgns (dq.ctx base (pubD base s)) i) y → t.mem y = s.mem y) :
    ReachFT base (PcIn base dsGeo.cs) (Has Rc) (Has Wc) (InStackWindow (dq.ctx base (pubD base s)).sp0 dsGeo.N) t
      (fun u => u.pc = base + BitVec.ofNat 32 (dq.epiW bszD) ∧ u.regs 13 = t.regs 13 ∧ PostD b Rs s u.mem (u.regs 0))
      (ΨD (fun a => (ads a).T) base (pubD base s)) := by
  obtain ⟨hb0, hs0, hep, -⟩ := dq_facts
  rw [hb0, hs0] at hat
  generalize hcc : dq.ctx base (pubD base s) = c at g F hat hrd ⊢
  have hbase : c.base = base := by rw [← hcc]; rfl
  have hp0 : c.ptr 0 = s.regs 0 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 0) (by decide)
  have hp1 : c.ptr 1 = s.regs 1 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 1) (by decide)
  have hp2 : c.ptr 2 = s.regs 2 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 2) (by decide)
  have hp3 : c.ptr 3 = s.regs 3 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 3) (by decide)
  have h4 : c.ptr 4 = c.base + BitVec.ofNat 32 Artifacts.Ed25519Compact.ed_zero := by rw [← hcc]; rfl
  have h5 : c.ptr 5 = c.base + BitVec.ofNat 32 Artifacts.Ed25519Compact.ed_odd_b := by rw [← hcc]; rfl
  have agr : ∀ r < 4, ∀ (L : Nat) (x : XInfo), dsGeo.xs[r]? = some x → x.len = .k L → x.r = true → 0 < L →
      ∀ i < L, t.mem (c.ptr r + BitVec.ofNat 32 i) = s.mem (c.ptr r + BitVec.ofNat 32 i) :=
    fun r _ L x hx hL hr hL0 i hi => hrd r x hx hr _ ⟨⟨c.ptr r, L⟩, by
      simp [XInfo.rgns, hL, XLen.v]; omega, ⟨i, hi, rfl⟩⟩
  have bt : ∀ r, r = 1 ∨ r = 2 → bytesAt t.mem (c.ptr r) 256 = bytesAt s.mem (c.ptr r) 256 := fun r hr =>
    bytesAt_congr fun i hi => agr r (by omega) 256 ⟨.k 256, false, true, false⟩
      (by rcases hr with rfl | rfl <;> rfl) rfl rfl (by decide) i hi
  have feA : ∀ o, o + 32 ≤ 128 → Field25519Routines.feVal t.mem (c.ptr 3 + BitVec.ofNat 32 o) =
      Field25519Routines.feVal s.mem (s.regs 3 + BitVec.ofNat 32 o) := fun o ho => by
    rw [← Ed25519GeCompressProg.dec_fe, ← Ed25519GeCompressProg.dec_fe, ← hp3]
    congr 1
    refine bytesAt_congr fun k hk => ?_
    rw [ofNat_add_assoc]
    exact agr 3 (by decide) 128 ⟨.k 128, false, true, true⟩ rfl rfl rfl (by decide) _ (by omega)
  have bt1 := bt 1 (.inl rfl)
  have bt2 := bt 2 (.inr rfl)
  have dd : ∀ i < 256, dP (pubD base s) 5 i = dv t.mem c 1 i ∧ dP (pubD base s) 69 i = dv t.mem c 2 i := fun i hi => by
    simp only [dP, dv, (pub_bytes base s).1, (pub_bytes base s).2, Ed25519WnafAd.bytesAt_getD hi, ← hp1, ← hp2]
    rw [agr 1 (by decide) 256 _ rfl rfl rfl (by decide) i hi, agr 2 (by decide) 256 _ rfl rfl rfl (by decide) i hi]
    exact ⟨rfl, rfl⟩
  have hz : ∀ i < 256, zP (pubD base s) i = zd t.mem c i := fun i hi => by
    simp only [zP, zd, (dd i hi).1, (dd i hi).2, dv_toInt]
  have htr : ΨD (fun a => (ads a).T) base (pubD base s) =
      bodyTr (TA ads) c (zd t.mem c) (dv t.mem c 2) (dv t.mem c 1) (Tr.is []) := by
    rw [ΨD, hcc]; exact bodyTr_congr _ _ _ fun i hi => ⟨hz i hi, (dd i hi).2, (dd i hi).1⟩
  have dg : ∀ i < 256, Digit 5 (digOf t.mem (c.ptr 1) i) ∧ Digit 3 (digOf t.mem (c.ptr 2) i) := fun i hi => by
    rw [dig_eq bt1 i hi, dig_eq bt2 i hi, hp1, hp2]; exact e.pre.2 i hi
  have hka : ∀ i < 256, (dv t.mem c 2 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dv t.mem c 2 i) < 2 := fun i hi h0 => by
    rw [dv_toInt] at h0; simp only [Ed25519DsmLoop.kOf, dv_toInt]; exact (dig3 (dg i hi).2 h0).2
  have hkb : ∀ i < 256, (dv t.mem c 1 i).toInt ≠ 0 → Ed25519DsmLoop.kOf (dv t.mem c 1 i) < 8 := fun i hi h0 => by
    rw [dv_toInt] at h0; simp only [Ed25519DsmLoop.kOf, dv_toInt]; exact (dig5 (dg i hi).1 h0).2
  rw [htr]
  rw [← hbase] at F hcR ⊢
  refine body_go Rs t.mem ads bds g F hcR cd cl cb hka hkb hat fun E' u hag hu => ReachT.done ⟨?_, ?_, ?_⟩
  · rw [hep]; exact hu.1
  · rw [hu.2.1, hat.2.1]
  · intro c' sp vs _ hI hpre
    obtain ⟨sv, hv, hs, hh, xs, A, rfl, x, y, z, w, rfl, -⟩ := hpre
    simp only [InsRel, io_eq.1, All2, Rel, In.kd] at hI
    obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := hI
    have hV := dsm_vr b hs hh (by rw [← hB]; exact hat.2.2.1) h4 h5
      (bt1.trans (by rw [hp1, ← BitVec.add_zero (s.regs 1)]; exact i1))
      (bt2.trans (by rw [hp2, ← BitVec.add_zero (s.regs 2)]; exact i2))
      (by rw [feA 0 (by decide)]; exact i3) (by rw [feA 32 (by decide)]; exact i4)
      (by rw [feA 64 (by decide)]; exact i5) (by rw [feA 96 (by decide)]; exact i6)
    have hL1 : (fun i => (dv t.mem c 1 i).toInt) = digOf t.mem (c.ptr 1) := funext (dv_toInt t.mem c 1)
    have hL2 : (fun i => (dv t.mem c 2 i).toInt) = digOf t.mem (c.ptr 2) := funext (dv_toInt t.mem c 2)
    have hn : nOf (topI (zd t.mem c) 255) = dsmTop (digOf t.mem (c.ptr 1)) (digOf t.mem (c.ptr 2)) 256 :=
      top_eq (fun _ => rfl) 255 (Nat.le_refl _)
    rw [hL1, hL2, hn, runA_D hA hBd] at hag
    have ro : ∀ o ∈ [0, 32, 64], Rel Rs c (dsGeo.fsp c) .fe u.mem (s.regs 0 + BitVec.ofNat 32 o)
        (runD c t.mem (preR ++ idR ++ runsR (digOf t.mem (c.ptr 2)) (digOf t.mem (c.ptr 1))
          (dsmTop (digOf t.mem (c.ptr 1)) (digOf t.mem (c.ptr 2)) 256) ++ endR) (fun _ => .none) (.ex 0 o)) := by
      intro o ho
      rw [← hag _ (send_outs o ho).2, ← hp0]
      exact (hu.2.2.2.2.1.1 _ (send_outs o ho).1).2
    simp only [OutsRel, io_eq.2]
    generalize dsmSem b _ = L at hV ⊢
    rcases L with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;> simp only [All2, and_true, and_false] at hV
    exact ⟨rel_fe (ro 0 (by simp)) hV.1, rel_fe (ro 32 (by simp)) hV.2.1, rel_fe (ro 64 (by simp)) hV.2.2, trivial⟩

end body

end M0Crypto.Release.Ed25519DsmAd
