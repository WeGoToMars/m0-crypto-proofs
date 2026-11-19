import M0Crypto.Release.Ed25519DecompressBits
import M0Crypto.Release.Ed25519CallProgCalleeW
import M0Crypto.Release.Ed25519WnafAd
import M0Crypto.Release.Ed25519VerifyStitch

/-!
# `m0c_ge_decompress` at verify's calls

* `dq`, `bszX`: the callee with interface `ioDecZ` (no unconditional outputs); the body is
  `0x2040 … 0x2268`;
* `xpX`, `xpvX`: its extra public values, the 32 input bytes as 8 words; `inP` reads them back;
* `ΨX`: the body's trace, with `decodeCode`'s tests on the input bytes;
* `PostX`: `r0 = 0` exactly when the input bytes decode, and then `out` holds the field values
  of the decoded point (`decCo`, `csemX`);
* `dec_body`: the body's run from `At` at its start to the epilogue.
-/

namespace M0Crypto.Release.Ed25519DecompressW

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519DecompressStitch
open M0Crypto.Release.Ed25519DecompressOut (inB yN sgN dk_ok DcK)
open M0Crypto.Release.Ed25519WnafAd (wordsAt wordsOf bytesOfW bytes_words)
open M0Crypto.Release.Ed25519VerifyProg (ioDec ioDecZ decCo)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519GeProg (fI)
open M0Crypto.Release.Ed25519Bridge (ofSpec)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-! ## The callee and its public values -/

abbrev dq : CalleeP DA DB := dcQ ioDecZ .nil

/-- The body's size: from `0x2040` to the epilogue at `0x2268`. -/
def bszX : Nat := 0x228

theorem dq_facts : dq.body = oP0 ∧ dq.st0 = stE ∧ dq.epiW bszX = oDone ∧ dq.okF = true := by decide +kernel

/-- The extra public values: the 32 input bytes as 8 words. -/
def xpX (st : State) : List Word := wordsAt st.mem (st.regs 1) 8

def xpvX : List V → List Word
  | [.b l] => wordsOf l 8
  | _ => []

/-- The public values at entry. -/
abbrev pubX (_ : Word) (st : State) : Nat → Word := dq.s.pubX xpX st

/-- The input bytes from the public values. -/
def inP (p : Nat → Word) : List (BitVec 8) := bytesOfW (fun j => p (3 + j)) 8

theorem bw_congr {w w' : Nat → Word} {n : Nat} (h : ∀ j < n, w j = w' j) : bytesOfW w n = bytesOfW w' n :=
  List.map_congr_left fun j hj => by rw [h (j / 4) (by have := List.mem_range.mp hj; omega)]

theorem pub_in (base : Word) (s : State) : inP (pubX base s) = bytesAt s.mem (s.regs 1) 32 := by
  have hp : dq.s.pubs.length = 3 := by decide
  rw [show (32 : Nat) = 4 * 8 from rfl, ← bytes_words]
  refine bw_congr fun j hj => ?_
  simp only [pubX, CalleeS.pubX, pubOf, xpX, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hp])]
  simp [hp]

/-- **The body's trace** at the public values `p`: `decodeCode`'s tests on the input bytes. -/
noncomputable def ΨX (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word) : TrP :=
  bodyTr Rs b (dq.ctx base p) (b0 (inP p)) (b1 (inP p)) (b2 (inP p)) (bz (inP p)) (bs (inP p)) (bn (inP p))

/-! ## The result -/

/-- No entry premise: any input bytes, at any alignment. -/
def xpreX (_ : Word) (_ : State) : Prop := True

/-- The status: the input bytes decode. -/
def okX : List V → Bool
  | [.b l] => (Spec.Ed25519.decodePoint l).isSome
  | _ => false

theorem okX_b (l : List (BitVec 8)) : okX [.b l] = (Spec.Ed25519.decodePoint l).isSome := rfl

/-- The four field values of a point. -/
def ptV (P : Ed25519EdwardsExtended.Ext Fp) : List V :=
  [.f (P.X.val : Int), .f (P.Y.val : Int), .f (P.Z.val : Int), .f (P.T.val : Int)]

/-- The outputs on success: the decoded point's field values. -/
def csemX : List V → List V
  | [.b l] => ((Spec.Ed25519.decodePoint l).map fun Q => ptV (ofSpec Q)).getD []
  | _ => []

/-- The interface with the point's outputs. -/
def ioDecO : Iface := { ioDecZ with outs := decCo }

/-- **The result**: `r0 = 0` exactly when the input bytes decode, and then `out` holds the decoded
point. -/
def PostX (Rs : Rels) (s : State) (m : Mem) (r0 : Word) : Prop :=
  ∀ c sp vs, InsRel Rs c sp ioDecZ s vs → (r0 = 0#32 ↔ okX vs = true) ∧
    (okX vs = true → OutsRel Rs c sp ioDecO s m (csemX vs))

theorem dec_in {Rs : Rels} {c : Ctx} {sp : Word} {s : State} {vs : List V} (h : InsRel Rs c sp ioDecZ s vs) :
    vs = [.b (bytesAt s.mem (s.regs 1) 32)] := by
  rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, ioDecZ, ioDec, and_true, and_false, In.kd, ALen.val] at h
  obtain ⟨l, rfl, hl⟩ := rel_bytes Rs h
  rw [BitVec.add_zero] at hl
  rw [hl]

/-- A field value's representative. -/
theorem modP_fI {z : Int} {x : Fp} (h : fI z = x) : ModP z (x.val : Int) := by
  have e := Ed25519DecompressVal.canon_nat z
  rw [h] at e
  have h0 : 0 ≤ z % (Field25519Reduce.pN : Int) := Int.emod_nonneg _ (by decide)
  have hl : x.val < Field25519Reduce.pN := x.val_lt
  show z % Field25519Congr.p = (x.val : Int) % Field25519Congr.p
  rw [← Ed25519DecompressVal.pN_eq, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega), ← Int.toNat_of_nonneg h0, e]

/-- The output views at the end of the body. -/
theorem outs_views : (Loc.ex 0 0, Kd.fe) ∈ t9.Γ ∧ (Loc.ex 0 32, Kd.fe) ∈ t9.Γ ∧ (Loc.ex 0 64, Kd.fe) ∈ t9.Γ ∧
    (Loc.ex 0 96, Kd.fe) ∈ t9.Γ := by decide +kernel

/-! ## The result from the body's end -/

/-- **The result** from the status and, on success, the views at the end of the body. -/
theorem post_of {Rs : Rels} {b : Build} {c : Ctx} {m0 : Mem} {s u : State} (hk : DcK c m0)
    (hin : inB c m0 = bytesAt s.mem (s.regs 1) 32) (hp0 : c.ptr 0 = s.regs 0)
    (hr0 : u.regs 0 = if okD Rs b c m0 then 0#32 else 1#32)
    (hH : okD Rs b c m0 = true → Inv Rs c dcGeo m0 t9 (Eo Rs b c m0) u.mem) : PostX Rs s u.mem (u.regs 0) := by
  intro c' sp vs hI
  have hv := dec_in hI
  have hok := dc_ok hk hr0
  rw [hin] at hok
  refine ⟨by rw [hv, okX_b]; exact hok, fun hd => ?_⟩
  rw [hv, okX_b] at hd
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hd
  have hD : okD Rs b c m0 = true := by
    have h0 := hok.mpr hd
    rw [hr0] at h0
    cases h : okD Rs b c m0
    · rw [h] at h0; exact absurd h0 (by decide)
    · rfl
  have hI9 := hH hD
  have hP : Ed25519Decode.decodeCode (yN c m0) (sgN c m0) = some (ofSpec Q) := by
    have hl : (inB c m0).length = 32 := bytesAt_length _ _ _
    have hd := Ed25519Bytes.decodeInt_lt (inB c m0)
    rw [hl] at hd
    have e := Ed25519Decode.decodePoint_eq (inB c m0)
    rw [hin, hQ, Option.map_some, ← hin, Nat.mod_eq_of_lt (a := decodeInt (inB c m0) / 2 ^ 255) (by omega)] at e
    exact e.symm
  have hcs : csemX vs = ptV (ofSpec Q) := by
    rw [hv]; simp only [csemX, hQ, Option.map_some, Option.getD_some]
  obtain ⟨⟨x, ex, fx⟩, ⟨y, ey, fy⟩, ⟨z, ez, fz⟩, ⟨w, ew, fw⟩⟩ := dc_out hk hP
  have ro : ∀ o, (Loc.ex 0 o, Kd.fe) ∈ t9.Γ → ModP (Field25519Routines.feVal u.mem (s.regs 0 + BitVec.ofNat 32 o))
      (match Eo Rs b c m0 (.ex 0 o) with | .f v => v | _ => 0) := fun o ho => by
    have h := (hI9.1 _ ho).2
    revert h
    rw [show (Loc.ex 0 o).addr c (dcGeo.fsp c) = s.regs 0 + BitVec.ofNat 32 o by rw [← hp0]; rfl]
    cases Eo Rs b c m0 (.ex 0 o) <;> simp [Rel]
  have hco : decCo = [(0, 0, .fe), (0, 32, .fe), (0, 64, .fe), (0, 96, .fe)] := rfl
  rw [hcs]
  simp only [OutsRel, ioDecO, hco, ptV, All2, Rel, and_true]
  have r0 := ro 0 outs_views.1; have r1 := ro 32 outs_views.2.1
  have r2 := ro 64 outs_views.2.2.1; have r3 := ro 96 outs_views.2.2.2
  rw [ex] at r0; rw [ey] at r1; rw [ez] at r2; rw [ew] at r3
  exact ⟨ModP.trans r0 (modP_fI fx), ModP.trans r1 (modP_fI fy),
    ModP.trans r2 (modP_fI fz), ModP.trans r3 (modP_fI fw)⟩

/-! ## The body's run -/

section body
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {Rs : Rels}

/-- **The body** from its start to the epilogue at `0x2268`: the trace `ΨX` of the public values
and the result `PostX`. -/
theorem dec_body (b : Build) (hB : B = b.bytes) (base : Word) (s : State) (t : State) {Wc Rc : List Rgn}
    (g : GeoOk (dq.ctx base (pubX base s)) dcGeo Wc Rc)
    (F : Caller base (dq.ctx base (pubX base s)).sp0 dcGeo.N Wc) (hcR : Sub [codeR base] Rc)
    (hat : At Rs B (dq.ctx base (pubX base s)) dcGeo t.mem dq.body dq.st0 (fun _ => .none) t)
    (hrd : ∀ i (x : XInfo), dcGeo.xs[i]? = some x → x.r = true →
      ∀ y, Has (x.rgns (dq.ctx base (pubX base s)) i) y → t.mem y = s.mem y) :
    ReachFT base (PcIn base dcGeo.cs) (Has Rc) (Has Wc) (InStackWindow (dq.ctx base (pubX base s)).sp0 dcGeo.N) t
      (fun u => u.pc = base + BitVec.ofNat 32 (dq.epiW bszX) ∧ u.regs 13 = t.regs 13 ∧ PostX Rs s u.mem (u.regs 0))
      (ΨX Rs b base (pubX base s)) := by
  subst hB
  obtain rfl : BS = b.size := (CodeBytes.len (B := b.bytes)).symm.trans (b.codeBytes.len)
  obtain ⟨hb0, hs0, hep, -⟩ := dq_facts
  rw [hb0, hs0] at hat
  rw [ΨX]
  generalize hcc : dq.ctx base (pubX base s) = c at g F hat hrd ⊢
  have hbase : c.base = base := by rw [← hcc]; rfl
  have hp0 : c.ptr 0 = s.regs 0 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 0) (by decide)
  have hp1 : c.ptr 1 = s.regs 1 := by rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pubX (r := 1) (by decide)
  have h2 : c.ptr 2 = c.base + BitVec.ofNat 32 Artifacts.Ed25519Compact.ed_zero := by rw [← hcc]; rfl
  have hk := dk_ok b hat.2.2.1 h2
  have hin : inB c t.mem = bytesAt s.mem (s.regs 1) 32 := by
    rw [← hp1, inB, show (Loc.ex 1 0).addr c (dcGeo.fsp c) = c.ptr 1 from BitVec.add_zero _]
    refine bytesAt_congr fun i hi => ?_
    exact hrd 1 ⟨.k 32, false, true, false⟩ rfl rfl _ ⟨⟨c.ptr 1, 32⟩, by simp [XInfo.rgns, XLen.v], ⟨i, hi, rfl⟩⟩
  obtain ⟨e0, e1, e2, ez, es, en⟩ := bits_eq (Rs := Rs) (b := b) hk
  rw [pub_in, ← hin, ← ez, ← en, ← e0, ← e1, ← e2, ← es]
  rw [← hbase] at F hcR ⊢
  exact ReachFT.mono (body_run g F hcR hat) (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (fun u hu => ⟨by rw [hep]; exact hu.1, by rw [hu.2.1, hat.2.1], post_of hk hin hp0 hu.2.2.1 hu.2.2.2⟩)
    fun _ h => h

end body

end M0Crypto.Release.Ed25519DecompressW
