import M0Crypto.Release.Ed25519VerifyProg
import M0Crypto.Release.Ed25519DecompressBlocks
import M0Crypto.Release.Ed25519Verify
import M0Crypto.Release.Ed25519TablesCompact
import M0Crypto.Release.Ed25519TablesFast

/-!
# The blocks, tests and verdict of `m0c_ed25519_verify`

* `loadS_run`, `loadSD`: the block `loadS` puts the 32 bytes of `s` at `SS` (its `Bd`);
* `lt_run`: the block `lt` (`SS − L` into `TMP`, eight words of `subs`/`sbcs`) leaves the carry
  set exactly when the 32 bytes at `r1` are at least those at `r2`, with `r3`'s 32 bytes apart
  from both; memory changes only there;
* `lt_spec`: with `L` at `r2`, `blo` continues exactly when `s < L`; `l9_val`: the first 32
  bytes of `m0c_ed_l9` are `L` in both builds;
* `verify_tests`: the specification's verdict is the conjunction of the routine's tests, in its
  order: `A` decodes, `R` decodes, `s < L`, `X = x_R Z`, `Y = y_R Z`;
* `dec_test`, `eq_test`: the status tests after `ge_decompress` (`Ed25519DecompressProg.dec_status`)
  and `fe_eq` give those tests' values; `verdict_r0`: the verdict block the tests choose leaves
  the contract's `r0`.
-/

namespace M0Crypto.Release.Ed25519VerifyBlocks

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519Words (wsum)
open M0Crypto.Release.Ed25519VerifyProg (ltW ltG loadSG ioLoadS SS vbS VB)
open M0Crypto.Release.Ed25519DecompressProg (wf awc div_step psum_wsum grp loads_run rel_bytes)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (vf_fail vf_success)

/-! ## One word -/

/-- The complement of word `j`, as `sbcs` adds it. -/
def cw (G : Nat → Nat) (j : Nat) : Nat := 2 ^ 32 - 1 - G j

/-- Word `k` with `sbcs`: `r1`–`r3` kept, the store at `r3 + 4k`, the carry of
`F + (2^32 − 1 − G) + c`. -/
theorem sbc_run (u : State) {k : Nat} (hk : k < 32) :
    (execAll (ltW (.dp .sbcs 4 5) k) u).regs 1 = u.regs 1 ∧ (execAll (ltW (.dp .sbcs 4 5) k) u).regs 2 = u.regs 2 ∧
    (execAll (ltW (.dp .sbcs 4 5) k) u).regs 3 = u.regs 3 ∧
    (∃ v, (execAll (ltW (.dp .sbcs 4 5) k) u).mem = write32 u.mem (u.regs 3 + BitVec.ofNat 32 (4 * k)) v) ∧
    (execAll (ltW (.dp .sbcs 4 5) k) u).c.toNat =
      (wf u.mem (u.regs 1) k + cw (wf u.mem (u.regs 2)) k + u.c.toNat) / 2 ^ 32 := by
  have hk' : k % 32 * 4 = 4 * k := by omega
  have e1 : LowReg.toReg 1 = 1 := rfl
  have e2 : LowReg.toReg 2 = 2 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  have e4 : LowReg.toReg 4 = 4 := rfl
  have e5 : LowReg.toReg 5 = 5 := rfl
  have a := awc (read32 u.mem (u.regs 1 + BitVec.ofNat 32 (4 * k))) (~~~(read32 u.mem (u.regs 2 + BitVec.ofNat 32 (4 * k)))) u.c
  simp (config := {decide := true}) [ltW, execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg,
    State.reg, MemOp.width, M0Crypto.Thumb.addFlags, State.setNZCV, State.setNZ, hk', e1, e2, e3, e4, e5, wf,
    cw] at a ⊢
  exact ⟨⟨_, rfl⟩, a.2⟩

/-- Word `0` with `subs`: the carry of `F + (2^32 − 1 − G) + 1`. -/
theorem sub_run (u : State) :
    (execAll (ltW (.subReg 4 4 5) 0) u).regs 1 = u.regs 1 ∧ (execAll (ltW (.subReg 4 4 5) 0) u).regs 2 = u.regs 2 ∧
    (execAll (ltW (.subReg 4 4 5) 0) u).regs 3 = u.regs 3 ∧
    (∃ v, (execAll (ltW (.subReg 4 4 5) 0) u).mem = write32 u.mem (u.regs 3 + BitVec.ofNat 32 (4 * 0)) v) ∧
    (execAll (ltW (.subReg 4 4 5) 0) u).c.toNat =
      (wf u.mem (u.regs 1) 0 + cw (wf u.mem (u.regs 2)) 0 + 1) / 2 ^ 32 := by
  have e1 : LowReg.toReg 1 = 1 := rfl
  have e2 : LowReg.toReg 2 = 2 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  have e4 : LowReg.toReg 4 = 4 := rfl
  have e5 : LowReg.toReg 5 = 5 := rfl
  have a := awc (read32 u.mem (u.regs 1 + BitVec.ofNat 32 0)) (~~~(read32 u.mem (u.regs 2 + BitVec.ofNat 32 0))) true
  simp (config := {decide := true}) [ltW, execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg,
    State.reg, MemOp.width, M0Crypto.Thumb.addFlags, State.setNZCV, State.setNZ, e1, e2, e3, e4, e5, wf,
    cw] at a ⊢
  exact ⟨⟨_, rfl⟩, a.2⟩

/-! ## The load of `s` -/

/-- Equal words give equal bytes. -/
theorem bytes_of_words {m1 m2 : Mem} {a1 a2 : Word} {n : Nat}
    (h : ∀ j < n, read32 m1 (a1 + BitVec.ofNat 32 (4 * j)) = read32 m2 (a2 + BitVec.ofNat 32 (4 * j))) :
    bytesAt m1 a1 (4 * n) = bytesAt m2 a2 (4 * n) := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  simp only [bytesAt, List.length_map, List.length_range] at h1
  have e : ∀ a : Word, a + BitVec.ofNat 32 i = a + BitVec.ofNat 32 (4 * (i / 4)) + BitVec.ofNat 32 (i % 4) :=
    fun a => by rw [ofNat_add_assoc]; congr 2; omega
  rw [e a1, e a2, Frame.byte_of_read32 m1 _ _ (Nat.mod_lt _ (by omega)),
    Frame.byte_of_read32 m2 _ _ (Nat.mod_lt _ (by omega)), h _ (by omega)]

/-- **The block `loadS`**: with the input apart from `SS`, `SS` holds its 32 bytes. -/
theorem loadS_run (t : State) (hsep : ∀ o < 32, ∀ q < 32,
      t.regs 13 + BitVec.ofNat 32 (SS + o) ≠ t.regs 2 + BitVec.ofNat 32 q) :
    bytesAt (execAll loadSG t).mem (t.regs 13 + BitVec.ofNat 32 SS) 32 = bytesAt t.mem (t.regs 2) 32 := by
  obtain ⟨-, -, hw, -⟩ := loads_run (o₀ := SS) (by decide) (by decide) t hsep 8 (Nat.le_refl _)
  show bytesAt (execAll ((List.range 8).flatMap (grp SS)) t).mem _ (4 * 8) = bytesAt _ _ (4 * 8)
  apply bytes_of_words
  intro j hj
  rw [← hw j hj, M0Crypto.Armv6M.slot, ofNat_add_assoc]
  congr 3; unfold SS Ed25519VerifyProg.SB; omega

section
open M0Crypto.Release.Ed25519CallProg (Ctx Rels Rel InsRel OutsRel PreV All2 In ALen rgnsC SRgn Bd)

/-- `SS` holds the input's bytes. -/
def loadSV : List Ed25519CallProg.V → List Ed25519CallProg.V
  | [.b l] => [.b l]
  | _ => []

/-- **The `loadS` block's post**: `SS` from the input bytes, apart from `SS` by `apt`. -/
theorem loadS_post (Rs : Rels) (c : Ctx) (sp : Word) (t : State) (vs : List Ed25519CallProg.V)
    (hpv : PreV ioLoadS c sp t.regs) (hin : InsRel Rs c sp ioLoadS t vs) :
    OutsRel Rs c sp ioLoadS t (execAll loadSG t).mem ((loadSV vs).take ioLoadS.outs.length) := by
  rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, ioLoadS, and_true, and_false, In.kd, ALen.val] at hin
  obtain ⟨l, rfl, hl⟩ := rel_bytes Rs hin
  have hs := hpv.2.2 _ (List.mem_singleton_self _)
  simp only [rgnsC, SRgn.rgnC, ALen.val, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    show (32 = 0) = False from by decide, ite_false] at hs
  have hsep : ∀ o < 32, ∀ q < 32, t.regs 13 + BitVec.ofNat 32 (SS + o) ≠ t.regs 2 + BitVec.ofNat 32 q := by
    intro o ho q hq he
    refine hs.not_has (y := t.regs 13 + BitVec.ofNat 32 (SS + o)) ⟨_, List.mem_singleton_self _, o, ho, ?_⟩
      ⟨_, List.mem_singleton_self _, q, hq, ?_⟩
    · exact (ofNat_add_assoc _ _ _).symm
    · rw [he, BitVec.add_zero]
  simp only [OutsRel, All2, ioLoadS, loadSV, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
    Rel, and_true]
  rw [BitVec.add_zero] at hl
  rw [loadS_run t hsep, hl]

/-- The verify blocks' `Bd`s; `lt`'s difference is scratch. -/
def loadSD (Rs : Rels) : Bd Rs (vbS .loadS) :=
  ⟨loadSV, fun c sp t vs _ _ hpv hin => loadS_post Rs c sp t vs hpv hin,
    fun _ _ _ _ _ _ _ _ _ h => by simp [vbS, ioLoadS] at h⟩

end

/-! ## The borrow chain -/

/-- The carry past word `n + 1` of `F + cw G + 1`. -/
theorem bor_step (F H : Nat → Nat) (n : Nat) :
    (F (n + 1) + H (n + 1) + (wsum F (n + 1) + wsum H (n + 1) + 1) / 2 ^ (32 * (n + 1))) / 2 ^ 32 =
      (wsum F (n + 2) + wsum H (n + 2) + 1) / 2 ^ (32 * (n + 2)) := by
  rw [Nat.add_comm (F (n + 1) + H (n + 1)), div_step _ _ _ _ (Nat.two_pow_pos _), ← Nat.pow_add,
    show 32 * (n + 1) + 32 = 32 * (n + 2) by omega, Ed25519Words.wsum_succ F (n + 1), Ed25519Words.wsum_succ H (n + 1)]
  congr 1; rw [Nat.mul_add]; omega

/-- The bytes `[0, 32)` from `a`. -/
def Out (a y : Word) : Prop := ∀ o < 32, y ≠ a + BitVec.ofNat 32 o

/-- Words `1 … n` from a state `u` after word `0` of `t`: `r1`–`r3` kept, memory changed only
at `r3`, the carry past word `n`. -/
theorem chain (t u : State) (hsep : ∀ o < 32, ∀ q < 32, t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 1 + BitVec.ofNat 32 q ∧
      t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 2 + BitVec.ofNat 32 q)
    (h1 : u.regs 1 = t.regs 1) (h2 : u.regs 2 = t.regs 2) (h3 : u.regs 3 = t.regs 3)
    (hm : ∀ y, Out (t.regs 3) y → u.mem y = t.mem y)
    (hc : u.c.toNat = (wsum (wf t.mem (t.regs 1)) 1 + wsum (cw (wf t.mem (t.regs 2))) 1 + 1) / 2 ^ (32 * 1)) :
    ∀ n, n ≤ 7 →
      (execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u).regs 1 = t.regs 1 ∧
      (execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u).regs 2 = t.regs 2 ∧
      (execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u).regs 3 = t.regs 3 ∧
      (∀ y, Out (t.regs 3) y → (execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u).mem y = t.mem y) ∧
      (execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u).c.toNat =
        (wsum (wf t.mem (t.regs 1)) (n + 1) + wsum (cw (wf t.mem (t.regs 2))) (n + 1) + 1) / 2 ^ (32 * (n + 1))
  | 0, _ => ⟨h1, h2, h3, hm, hc⟩
  | n + 1, hn => by
    obtain ⟨r1, r2, r3, rm, rc⟩ := chain t u hsep h1 h2 h3 hm hc n (by omega)
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      execAll_append]
    generalize execAll ((List.range n).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)) u = w at r1 r2 r3 rm rc
    obtain ⟨q1, q2, q3, ⟨v, qm⟩, qc⟩ := sbc_run w (k := n + 1) (by omega)
    have hrd : ∀ j : Fin 2, ∀ a : Word, (a = t.regs 1 ∨ a = t.regs 2) →
        (∀ o < 32, ∀ q < 32, t.regs 3 + BitVec.ofNat 32 o ≠ a + BitVec.ofNat 32 q) →
        wf w.mem a (n + 1) = wf t.mem a (n + 1) := by
      intro _ a _ ha
      unfold wf; congr 1
      apply Frame.read32_congr
      intro q hq
      rw [ofNat_add_assoc]
      exact rm _ fun o ho e => ha o ho (4 * (n + 1) + q) (by omega) e.symm
    have hF := hrd 0 _ (.inl rfl) fun o ho q hq => (hsep o ho q hq).1
    have hG := hrd 1 _ (.inr rfl) fun o ho q hq => (hsep o ho q hq).2
    refine ⟨q1.trans r1, q2.trans r2, q3.trans r3, fun y hy => ?_, ?_⟩
    · rw [qm, M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq e => hy (4 * (n + 1) + q) (by omega) (by
          rw [e, r3, ofNat_add_assoc])]
      exact rm y hy
    · rw [qc, r1, r2, hF, show cw (wf w.mem (t.regs 2)) (n + 1) = cw (wf t.mem (t.regs 2)) (n + 1) by
        unfold cw; rw [hG], rc]
      exact bor_step _ _ n

/-- The complement words and the words sum to `2^(32 n) − 1`. -/
theorem cw_sum (G : Nat → Nat) (hG : ∀ j, G j < 2 ^ 32) :
    ∀ n, wsum (cw G) n + wsum G n + 1 = 2 ^ (32 * n)
  | 0 => rfl
  | n + 1 => by
    have ih := cw_sum G hG n
    have h := hG n
    rw [Ed25519Words.wsum_succ, Ed25519Words.wsum_succ, show 32 * (n + 1) = 32 * n + 32 by omega, Nat.pow_add,
      show wsum (cw G) n + 2 ^ (32 * n) * cw G n + (wsum G n + 2 ^ (32 * n) * G n) + 1 =
        (wsum (cw G) n + wsum G n + 1) + 2 ^ (32 * n) * (cw G n + G n) by rw [Nat.mul_add]; omega, ih,
      show cw G n + G n = 4294967295 by unfold cw; omega]
    omega

/-- The carry past the last word: set exactly when `B ≤ A`. -/
theorem bor_fin {A B C : Nat} (hs : C + B + 1 = 2 ^ (32 * 8)) (hA : A < 2 ^ (32 * 8))
    (c : Bool) (hc : c.toNat = (A + C + 1) / 2 ^ (32 * (7 + 1))) : c = decide (B ≤ A) := by
  by_cases h : B ≤ A
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)] at hc
    rw [decide_eq_true h]
    cases c
    · simp only [Bool.toNat_false] at hc; omega
    · rfl
  · rw [Nat.div_eq_of_lt (by omega)] at hc
    rw [decide_eq_false h]
    cases c
    · rfl
    · simp only [Bool.toNat_true] at hc; omega

/-- The value of 32 bytes is the sum of their eight words. -/
theorem dec_wsum (m : Mem) (a : Word) : decodeInt (bytesAt m a 32) = wsum (wf m a) 8 := by
  have h := Ed25519FePow.decode_feVal m a
  rw [Field25519Facts.feVal_psum, psum_wsum] at h
  exact_mod_cast h

/-- **The block `lt`**: with `r3`'s 32 bytes apart from those at `r1` and `r2`, the carry is set
exactly when the value at `r1` is at least that at `r2`; memory changes only at `r3`, and
`r1`–`r3` are kept. -/
theorem lt_run (t : State) (hsep : ∀ o < 32, ∀ q < 32, t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 1 + BitVec.ofNat 32 q ∧
      t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 2 + BitVec.ofNat 32 q) :
    (execAll ltG t).c = decide (decodeInt (bytesAt t.mem (t.regs 2) 32) ≤ decodeInt (bytesAt t.mem (t.regs 1) 32)) ∧
    (∀ y, Out (t.regs 3) y → (execAll ltG t).mem y = t.mem y) ∧
    (execAll ltG t).regs 1 = t.regs 1 ∧ (execAll ltG t).regs 2 = t.regs 2 ∧ (execAll ltG t).regs 3 = t.regs 3 := by
  obtain ⟨u1, u2, u3, ⟨v, um⟩, uc⟩ := sub_run t
  rw [ltG, execAll_append]
  generalize execAll (ltW (.subReg 4 4 5) 0) t = u at u1 u2 u3 um uc
  have hm : ∀ y, Out (t.regs 3) y → u.mem y = t.mem y := fun y hy => by
    rw [um, M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq e => hy q (by omega) (by rw [e, ofNat_add_assoc, Nat.mul_zero, Nat.zero_add])]
  obtain ⟨w1, w2, w3, wm, wc⟩ := chain t u hsep u1 u2 u3 hm (by rw [uc]; simp [wsum]) 7 (by omega)
  refine ⟨?_, wm, w1, w2, w3⟩
  rw [dec_wsum, dec_wsum]
  exact bor_fin (cw_sum (wf t.mem (t.regs 2)) (fun j => (read32 _ _).isLt) 8)
    (Ed25519Words.wsum_lt (f := wf t.mem (t.regs 1)) (n := 8) fun j _ => (read32 _ _).isLt) _ wc

/-- **The `s < L` test**: with `L` at `r2`, `blo` (carry clear) continues exactly when the
32 bytes at `r1` are below `L`. -/
theorem lt_spec (t : State) (hsep : ∀ o < 32, ∀ q < 32, t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 1 + BitVec.ofNat 32 q ∧
      t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 2 + BitVec.ofNat 32 q)
    (hL : decodeInt (bytesAt t.mem (t.regs 2) 32) = Spec.Ed25519.L) :
    ((execAll ltG t).c = false ↔ decodeInt (bytesAt t.mem (t.regs 1) 32) < Spec.Ed25519.L) ∧
    ∀ y, Out (t.regs 3) y → (execAll ltG t).mem y = t.mem y := by
  obtain ⟨hc, hm, -⟩ := lt_run t hsep
  refine ⟨?_, hm⟩
  rw [hc, hL, decide_eq_false_iff_not, Nat.not_le]

/-- **`m0c_ed_l9` holds `L`** in its first 32 bytes, in both builds. -/
theorem l9_val : ∀ b : Build,
    decodeInt ((b.bytes.drop M0Crypto.Artifacts.Ed25519Compact.ed_l9).take 32) = Spec.Ed25519.L := by
  intro b; cases b <;> decide +kernel

/-! ## The verdict -/

open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge M0Crypto.Release.Ed25519Verify

/-- **The specification's verdict is the routine's tests**, in its order: `A` decodes, `R`
decodes, `s < L`, then `X = x_R Z` and `Y = y_R Z` with `ER` the decoded `R` and `SB` the
double multiplication's result, which represents `[s]B − [k mod L]A` when `s < L`. -/
theorem verify_tests {sig M Apk : List Spec.Ed25519.Byte} {SB ER : Ext Fp}
    (hER : ∀ R, Spec.Ed25519.decodePoint (sig.take 32) = some R → ER = ofSpec R)
    (hSB : ∀ R A', Spec.Ed25519.decodePoint (sig.take 32) = some R → Spec.Ed25519.decodePoint Apk = some A' →
      ∃ Apt : EdPt, SpecRep A' Apt ∧ (decodeInt (sig.drop 32) < Spec.Ed25519.L →
        Rep2 SB ((decodeInt (sig.drop 32) : Int) • Bpt -
          ((decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M)) % Spec.Ed25519.L : Nat) : Int) • Apt))) :
    Spec.Ed25519.verify sig M Apk =
      ((Spec.Ed25519.decodePoint Apk).isSome && (Spec.Ed25519.decodePoint (sig.take 32)).isSome &&
        decide (decodeInt (sig.drop 32) < Spec.Ed25519.L) && decide (SB.X = ER.X * SB.Z) &&
        decide (SB.Y = ER.Y * SB.Z)) := by
  cases hA : Spec.Ed25519.decodePoint Apk with
  | none => rw [verify_of_decode_A_none hA]; rfl
  | some A' =>
    cases hR : Spec.Ed25519.decodePoint (sig.take 32) with
    | none => rw [verify_of_decode_R_none hR]; simp
    | some R =>
      obtain ⟨Apt, hr, hs⟩ := hSB R A' hR hA
      rw [verify_eq hR hA hr hs, hER R hR]
      simp [eqCode, Bool.and_assoc]

/-! ## The status tests and the verdict -/

section
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519Reduce (pN)

/-- **`ge_decompress`'s status test** `cmp r0, #0`: `Z` exactly when the bytes decode. -/
theorem dec_test (s : State) {l : List Spec.Ed25519.Byte}
    (h0 : s.regs 0 = 0#32 ↔ (Spec.Ed25519.decodePoint l).isSome = true) :
    ((Instr.cmpImm 0 0).next s).z = (Spec.Ed25519.decodePoint l).isSome := by
  rw [Ed25519DecompressProg.cmp0_z]
  exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq]; exact h0)

/-- **`fe_eq`'s status test** `cmp r0, #0` (`fe_eq`'s post, `Ed25519FeEq.eqR`): `Z` exactly when
the field values agree. -/
theorem eq_test (s : State) {a b : Nat} {x y : Int} {X Y : Fp} (ha : ModP a x) (hb : ModP b y)
    (hX : Ed25519GeProg.fI x = X) (hY : Ed25519GeProg.fI y = Y) (h0 : s.regs 0 = 0#32 ↔ a % pN = b % pN) :
    ((Instr.cmpImm 0 0).next s).z = decide (X = Y) := by
  rw [← hX, ← hY]
  exact Bool.eq_iff_iff.mpr ((Ed25519DecompressProg.st_spec s ha hb h0).trans decide_eq_true_iff.symm)

/-- The verdict blocks: `movs r0, #0` (then `b` to the epilogue), and `movs r0, #0; mvns r0, r0`. -/
def okG : List Instr := [.movImm 0 0]
def failG : List Instr := [.movImm 0 0, .dp .mvns 0 0]

theorem verdict_at (b : Build) : seqAt b.bytes vf_success okG = true ∧ seqAt b.bytes vf_fail failG = true := by
  cases b <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem ok_r0 (s : State) : (execAll okG s).regs 0 = 0#32 := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  simp [okG, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, e0]

theorem fail_r0 (s : State) : (execAll failG s).regs 0 = 0xffffffff#32 := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  simp [failG, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, e0]

/-- **The verdict**: the block the tests choose (`okG` when all pass, else `failG`) leaves the
contract's `r0`, `0` exactly when the specification accepts and `−1` otherwise. -/
theorem verdict_r0 {sig M Apk : List Spec.Ed25519.Byte} {SB ER : Ext Fp}
    (hER : ∀ R, Spec.Ed25519.decodePoint (sig.take 32) = some R → ER = ofSpec R)
    (hSB : ∀ R A', Spec.Ed25519.decodePoint (sig.take 32) = some R → Spec.Ed25519.decodePoint Apk = some A' →
      ∃ Apt : EdPt, SpecRep A' Apt ∧ (decodeInt (sig.drop 32) < Spec.Ed25519.L →
        Rep2 SB ((decodeInt (sig.drop 32) : Int) • Bpt -
          ((decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M)) % Spec.Ed25519.L : Nat) : Int) • Apt)))
    {ok : Bool} (hok : ok = ((Spec.Ed25519.decodePoint Apk).isSome && (Spec.Ed25519.decodePoint (sig.take 32)).isSome &&
        decide (decodeInt (sig.drop 32) < Spec.Ed25519.L) && decide (SB.X = ER.X * SB.Z) &&
        decide (SB.Y = ER.Y * SB.Z))) (s : State) :
    (execAll (if ok then okG else failG) s).regs 0 = if Spec.Ed25519.verify sig M Apk then 0 else 0xffffffff#32 := by
  rw [verify_tests hER hSB, ← hok]
  cases ok
  · exact fail_r0 s
  · exact ok_r0 s

end

end M0Crypto.Release.Ed25519VerifyBlocks
