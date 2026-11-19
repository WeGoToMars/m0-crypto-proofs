import M0Crypto.Release.Ed25519WordLoop
import M0Crypto.Release.Ed25519Words
import M0Crypto.Release.Ed25519Sha512Exec
import M0Crypto.Release.Field25519AddSubChain
import M0Crypto.Release.Ed25519Barrett
import M0Crypto.Release.Ed25519Sha512Group

set_option linter.unusedSimpArgs false

/-!
# Multi-word chains of the scalar routines (reusable)

* `wv m p k`: word `k` from `p` as a `Nat`, the word function of `Ed25519Words.wsum`; `wv_write`:
  a store at word `i` is `upd` at `i`.
* `chainI neg cin yld ra rb rd x y k n`: words `k … k + n − 1` of an `adds`/`adcs` (`neg = false`)
  or `subs`/`sbcs` (`neg = true`) chain, each `ldr x, [ra, #4w]; ldr y, [rb, #4w]; op x, y;
  str x, [rd, #4w]`. Without `cin` the first word has no carry in; without `yld` the second
  operand is the register `y` for every word. Macro `sub_words` of `m0c_sc_reduce` and verify is
  `chainI true false true`; the two chains of `m0c_sc_muladd` are `chainI false false true` and
  `chainI false true false`.
* `chain_run`: one lemma for every such chain, in any registers and at any word offset: the stored
  words and the carries as `Nat` equations (`Ed25519Words.add_chain`, `sub_chain`), the flags'
  carry out, the frame. `chain_sub`: the borrow form for `sub_chain`.
* `selMask rd`: `sbcs rd, rd; mvns rd, rd` after a chain, the select mask (`m0c_sc_reduce` uses `r3`).
-/

namespace M0Crypto.Release.Ed25519ScalarChain

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519Words (wsum upd upd_ne upd_same)
open M0Crypto.Release.Field25519AddSubChain (dop op3 opY regs_dop c_dop regs_op3 c_op3 mem_dop mem_op3)

/-- Word `k` from `p`. -/
def wv (m : Mem) (p : Word) (k : Nat) : Nat := (read32 m (p + BitVec.ofNat 32 (4 * k))).toNat

theorem wv_lt (m : Mem) (p : Word) (k : Nat) : wv m p k < 2 ^ 32 := (read32 m _).isLt

/-- Word `k < L` of a region apart from a frame fact's footprint is kept. -/
theorem wv_keep {f : List Rgn} {m m' : Mem} (h : MemEq f m m') {p : Word} {k : Nat}
    (hs : Sep [⟨p + BitVec.ofNat 32 (4 * k), 4⟩] f) : wv m' p k = wv m p k := by
  simp only [wv, h.read32 hs]

/-- **A store at word `i`** of a region of `L` words that does not wrap. -/
theorem wv_write (m : Mem) (p v : Word) {L i : Nat} (hp : p.toNat + 4 * L ≤ 2 ^ 32) (hi : i < L) :
    ∀ k < L, wv (write32 m (p + BitVec.ofNat 32 (4 * i)) v) p k = upd (wv m p) i v.toNat k := by
  intro k hk
  by_cases h : k = i
  · subst h; simp [wv, upd, M0Crypto.Armv6M.read32_write32_same]
  · rw [upd_ne _ _ h]
    have := p.isLt
    exact wv_keep (Ed25519WordLoop.memEq_write32 m _ v) (by fp_simp; omega)

/-! ## One instruction -/

theorem nx_strImm_mem (s : State) (t n : LowReg) (k : BitVec 5) : ((Instr.memImm .str t n k).next s).mem =
    write32 s.mem (s.regs n.toReg + BitVec.ofNat 32 (k.toNat * 4)) (s.regs t.toReg) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width, (toReg_ne_15 _)]

theorem nx_strImm (s : State) (t n : LowReg) (k : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memImm .str t n k).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width, (toReg_ne_15 _), hr]

theorem c_ldrImm (s : State) (t n : LowReg) (k : BitVec 5) : ((Instr.memImm .ldr t n k).next s).c = s.c := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width]

theorem c_strImm (s : State) (t n : LowReg) (k : BitVec 5) : ((Instr.memImm .str t n k).next s).c = s.c := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width]

/-! ## The chain -/

/-- The operation of word `i`: no carry in on the first word unless `cin`. -/
def opW (neg cin : Bool) (x y : LowReg) (i : Nat) : Instr :=
  if i = 0 ∧ cin = false then op3 neg x x y else .dp (dop neg) x y

/-- Word `k + i` of the chain. -/
def chainW (neg cin yld : Bool) (ra rb rd x y : LowReg) (k i : Nat) : List Instr :=
  [.memImm .ldr x ra (BitVec.ofNat 5 (k + i))] ++
    (if yld then [.memImm .ldr y rb (BitVec.ofNat 5 (k + i))] else []) ++
    [opW neg cin x y i, .memImm .str x rd (BitVec.ofNat 5 (k + i))]

def chainI (neg cin yld : Bool) (ra rb rd x y : LowReg) (k n : Nat) : List Instr :=
  (List.range n).flatMap (chainW neg cin yld ra rb rd x y k)

/-- The registers of a chain: `x` and `y` apart from each other and from the pointers. -/
structure Regs (yld : Bool) (ra rb rd x y : LowReg) : Prop where
  xy : x ≠ y
  xa : x ≠ ra
  xb : x ≠ rb
  xd : x ≠ rd
  ya : y ≠ ra
  yb : y ≠ rb
  yd : y ≠ rd

theorem lo_ne {a b : LowReg} (h : a ≠ b) : a.toReg ≠ b.toReg := fun e => h (by
  have := congrArg Fin.val e; exact Fin.ext (by simpa [LowReg.toReg] using this))

/-- The words a chain reads from `ra` and `rb` are not stored before they are read: `rd` equals
the source or lies apart from it. -/
def Safe (rd r : Word) (n : Nat) : Prop := rd = r ∨ Frame.Disj rd n r n

/-- **One word.** -/
theorem chainW_run (neg cin yld : Bool) (ra rb rd x y : LowReg) (k i : Nat) (v : State)
    (hR : Regs yld ra rb rd x y) (hk : k + i < 32) :
    let X := read32 v.mem (v.regs ra.toReg + BitVec.ofNat 32 (4 * (k + i)))
    let Y := if yld then read32 v.mem (v.regs rb.toReg + BitVec.ofNat 32 (4 * (k + i))) else v.regs y.toReg
    let A := addWithCarry X (opY neg Y) (if i = 0 ∧ cin = false then neg else v.c)
    (execAll (chainW neg cin yld ra rb rd x y k i) v).mem =
      write32 v.mem (v.regs rd.toReg + BitVec.ofNat 32 (4 * (k + i))) A.1 ∧
    (execAll (chainW neg cin yld ra rb rd x y k i) v).c = A.2.1 ∧
    ∀ r : Reg, r ≠ x.toReg → (yld = true → r ≠ y.toReg) → r ≠ 15 →
      (execAll (chainW neg cin yld ra rb rd x y k i) v).regs r = v.regs r := by
  intro X Y A
  have e5 : (BitVec.ofNat 5 (k + i)).toNat * 4 = 4 * (k + i) := by
    simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨xy, xa, xb, xd, ya, yb, yd⟩ := hR
  have l := lo_ne xy; have l2 := lo_ne xa; have l3 := lo_ne xb; have l4 := lo_ne xd
  have l5 := lo_ne ya; have l6 := lo_ne yb; have l7 := lo_ne yd
  -- the loads
  obtain ⟨u, hu⟩ : ∃ u, u = execAll ([.memImm .ldr x ra (BitVec.ofNat 5 (k + i))] ++
      (if yld then [.memImm .ldr y rb (BitVec.ofNat 5 (k + i))] else [])) v := ⟨_, rfl⟩
  have ux : u.regs x.toReg = X ∧ u.regs y.toReg = Y ∧ u.mem = v.mem ∧ u.c = v.c ∧
      ∀ r : Reg, r ≠ x.toReg → (yld = true → r ≠ y.toReg) → r ≠ 15 → u.regs r = v.regs r := by
    subst hu
    have L := fun (u : State) (t n : LowReg) (r : Reg) (h : r ≠ 15) =>
      Ed25519Sha512Exec.nx_ldrImm u r h t n (BitVec.ofNat 5 (k + i))
    have M := fun (u : State) (t n : LowReg) => Ed25519Sha512Exec.mem_ldrImm t n (BitVec.ofNat 5 (k + i)) u
    cases yld
    · simp only [List.append_nil, ite_false, execAll, Y, Bool.false_eq_true]
      refine ⟨by rw [L _ _ _ _ (toReg_ne_15 _), ite_eq_left rfl, e5], by rw [L _ _ _ _ (toReg_ne_15 _), ite_eq_right (Ne.symm l)],
        M _ _ _, c_ldrImm _ _ _ _, fun r h1 _ h3 => by rw [L _ _ _ _ h3, ite_eq_right h1]⟩
    · simp only [List.cons_append, List.nil_append, ite_true, execAll, Y]
      refine ⟨by rw [L _ _ _ _ (toReg_ne_15 _), ite_eq_right l, L _ _ _ _ (toReg_ne_15 _), ite_eq_left rfl, e5],
        by rw [L _ _ _ _ (toReg_ne_15 _), ite_eq_left rfl, M, L _ _ _ _ (toReg_ne_15 _), ite_eq_right (Ne.symm l3), e5],
        by rw [M, M], by rw [c_ldrImm, c_ldrImm],
        fun r h1 h2 h3 => by rw [L _ _ _ _ h3, ite_eq_right (h2 (by simp)), L _ _ _ _ h3, ite_eq_right h1]⟩
  have hw : chainW neg cin yld ra rb rd x y k i = ([.memImm .ldr x ra (BitVec.ofNat 5 (k + i))] ++
      (if yld then [.memImm .ldr y rb (BitVec.ofNat 5 (k + i))] else [])) ++
      [opW neg cin x y i, .memImm .str x rd (BitVec.ofNat 5 (k + i))] := rfl
  rw [hw, execAll_append, ← hu]
  obtain ⟨ux, uy, um, uc, uk⟩ := ux
  have hop : ((opW neg cin x y i).next u).regs x.toReg = A.1 ∧ ((opW neg cin x y i).next u).c = A.2.1 ∧
      ((opW neg cin x y i).next u).mem = u.mem ∧
      ∀ r : Reg, r ≠ x.toReg → r ≠ 15 → ((opW neg cin x y i).next u).regs r = u.regs r := by
    unfold opW; split
    · rename_i h
      refine ⟨?_, ?_, mem_op3 _ _ _ _ _, fun r h1 h2 => ?_⟩
      · rw [regs_op3 _ _ _ _ _ _ (toReg_ne_15 _), ite_eq_left rfl]; simp [State.reg, ux, uy, A, h]
      · rw [c_op3]; simp [State.reg, ux, uy, A, h]
      · rw [regs_op3 _ _ _ _ _ _ h2, ite_eq_right h1]
    · rename_i h
      have hc : (if i = 0 ∧ cin = false then neg else v.c) = v.c := ite_eq_right h
      refine ⟨?_, ?_, mem_dop _ _ _ _, fun r h1 h2 => ?_⟩
      · rw [regs_dop _ _ _ _ _ (toReg_ne_15 _), ite_eq_left rfl]; simp [State.reg, ux, uy, uc, A, hc]
      · rw [c_dop]; simp [State.reg, ux, uy, uc, A, hc]
      · rw [regs_dop _ _ _ _ _ h2, ite_eq_right h1]
  obtain ⟨ox, oc, om, ok⟩ := hop
  simp only [execAll, nx_strImm_mem, c_strImm, e5, ox, oc, om, um, ok _ (Ne.symm l4) (toReg_ne_15 _),
    uk _ (Ne.symm l4) (fun _ => Ne.symm l7) (toReg_ne_15 _)]
  exact ⟨by simp, by simp, fun r h1 h2 h3 => by
    rw [nx_strImm _ _ _ _ _ h3, ok r h1 h3, uk r h1 h2 h3]⟩

/-- The second operand of word `j`, from the chain's entry state `u`. -/
def yW (yld : Bool) (rb y : LowReg) (k : Nat) (u : State) (j : Nat) : Word :=
  if yld then read32 u.mem (u.regs rb.toReg + BitVec.ofNat 32 (4 * (k + j))) else u.regs y.toReg

/-- **A chain of `n` words** from `u`, words `k … k + n − 1` of `rd`, `ra`, `rb`, none wrapping:
memory changes only in the stored words, registers other than `x`, `y` are kept, and the carries
`c` (`c 0` the carry in, `c n` the flag at the end) link the words as `Nat` equations. -/
theorem chain_run (neg cin yld : Bool) (ra rb rd x y : LowReg) (k N : Nat) (u : State)
    (hR : Regs yld ra rb rd x y) (hk : k + N ≤ 32)
    (hd : (u.regs rd.toReg).toNat + 4 * (k + N) ≤ 2 ^ 32)
    (ha : Safe (u.regs rd.toReg) (u.regs ra.toReg) (4 * (k + N)))
    (hb : yld = true → Safe (u.regs rd.toReg) (u.regs rb.toReg) (4 * (k + N))) :
    ∀ n ≤ N, MemEq [⟨u.regs rd.toReg + BitVec.ofNat 32 (4 * k), 4 * n⟩] u.mem
      (execAll (chainI neg cin yld ra rb rd x y k n) u).mem ∧
    (∀ r : Reg, r ≠ x.toReg → (yld = true → r ≠ y.toReg) → r ≠ 15 →
      (execAll (chainI neg cin yld ra rb rd x y k n) u).regs r = u.regs r) ∧
    ∃ c : Nat → Bool, c 0 = (if cin then u.c else neg) ∧
      ((0 < n ∨ cin = true) → (execAll (chainI neg cin yld ra rb rd x y k n) u).c = c n) ∧
      ∀ j < n, wv (execAll (chainI neg cin yld ra rb rd x y k n) u).mem (u.regs rd.toReg) (k + j) +
        2 ^ 32 * (c (j + 1)).toNat = wv u.mem (u.regs ra.toReg) (k + j) +
          (opY neg (yW yld rb y k u j)).toNat + (c j).toNat
  | 0, _ => ⟨MemEq.rfl' _ _, fun _ _ _ _ => rfl, fun _ => if cin then u.c else neg, rfl,
      fun h => by cases cin <;> simp_all [chainI, execAll], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨hm, hr, c, c0, cn, hc⟩ := chain_run neg cin yld ra rb rd x y k N u hR hk hd ha hb n (by omega)
    rw [chainI, Ed25519Sha512Group.flatMap_range_succ, execAll_append]
    rw [chainI] at hm hr cn hc
    generalize execAll ((List.range n).flatMap (chainW neg cin yld ra rb rd x y k)) u = v at hm hr cn hc
    obtain ⟨wm, wc, wr⟩ := chainW_run neg cin yld ra rb rd x y k n v hR (by omega)
    have := (u.regs rd.toReg).isLt; have := (u.regs ra.toReg).isLt; have := (u.regs rb.toReg).isLt
    have rd' : v.regs rd.toReg = u.regs rd.toReg := hr _ (Ne.symm (lo_ne hR.xd)) (fun _ => Ne.symm (lo_ne hR.yd)) (toReg_ne_15 _)
    have ra' : v.regs ra.toReg = u.regs ra.toReg := hr _ (Ne.symm (lo_ne hR.xa)) (fun _ => Ne.symm (lo_ne hR.ya)) (toReg_ne_15 _)
    -- the words this pass reads are not yet stored
    have src : ∀ q : Word, Safe (u.regs rd.toReg) q (4 * (k + N)) →
        read32 v.mem (q + BitVec.ofNat 32 (4 * (k + n))) = read32 u.mem (q + BitVec.ofNat 32 (4 * (k + n))) :=
      fun q hq => hm.read32 (by
        have := q.isLt
        rcases hq with rfl | hq <;> (try simp only [Frame.Disj] at hq) <;> fp_simp <;> omega)
    have hX : read32 v.mem (v.regs ra.toReg + BitVec.ofNat 32 (4 * (k + n))) =
        read32 u.mem (u.regs ra.toReg + BitVec.ofNat 32 (4 * (k + n))) := by rw [ra', src _ ha]
    have hY : (if yld then read32 v.mem (v.regs rb.toReg + BitVec.ofNat 32 (4 * (k + n))) else v.regs y.toReg) =
        yW yld rb y k u n := by
      cases yld
      · simp only [yW, Bool.false_eq_true, ite_false]
        exact hr _ (lo_ne hR.xy).symm (fun h => absurd h (by decide)) (toReg_ne_15 _)
      · simp only [yW, ite_true]
        rw [hr _ (Ne.symm (lo_ne hR.xb)) (fun _ => Ne.symm (lo_ne hR.yb)) (toReg_ne_15 _), src _ (hb rfl)]
    rw [hX, hY] at wm wc; rw [rd'] at wm
    have hci : (if n = 0 ∧ cin = false then neg else v.c) = c n := by
      by_cases h : n = 0 ∧ cin = false
      · rw [ite_eq_left h, h.1, c0, h.2]; rfl
      · rw [ite_eq_right h, cn (by cases cin <;> simp_all <;> omega)]
    rw [hci] at wm wc
    have hw := wv_write v.mem (u.regs rd.toReg) (addWithCarry (read32 u.mem (u.regs ra.toReg +
      BitVec.ofNat 32 (4 * (k + n)))) (opY neg (yW yld rb y k u n)) (c n)).1 hd (show k + n < k + N by omega)
    refine ⟨?_, fun r h1 h2 h3 => by rw [wr r h1 h2 h3, hr r h1 h2 h3],
      fun j => if j ≤ n then c j else (execAll (chainW neg cin yld ra rb rd x y k n) v).c,
      by simp [c0], fun _ => by simp only [show ¬ n + 1 ≤ n by omega, ite_false], fun j hj => ?_⟩
    · rw [wm]; refine hm.trans (Ed25519WordLoop.memEq_write32 _ _ _) |>.mono ?_
      simp only [List.cons_append, List.nil_append]; fp_tac
    · rw [wm, hw _ (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · simp only [upd_ne _ _ (show k + j ≠ k + n by omega), show j + 1 ≤ n by omega, show j ≤ n by omega,
          ite_true]; exact hc j hj
      · subst hj
        simp only [upd_same, show ¬ j + 1 ≤ j by omega, Nat.le_refl, ite_true, ite_false, wc, yW]
        exact Field25519Carry.adc_nat _ _ _

/-- The borrow form of a `subs`/`sbcs` chain (`Ed25519Words.sub_chain`): `b = 1 − c`. -/
theorem chain_sub {r X Y : Word} {c c' : Bool}
    (h : r.toNat + 2 ^ 32 * c'.toNat = X.toNat + (opY true Y).toNat + c.toNat) :
    r.toNat + Y.toNat + (1 - c.toNat) = X.toNat + 2 ^ 32 * (1 - c'.toNat) := by
  simp only [opY, ite_true, BitVec.toNat_not] at h
  have := Y.isLt
  cases c <;> cases c' <;> simp at h ⊢ <;> omega

/-! ## The select mask -/

/-- `sbcs rd, rd; mvns rd, rd`: all ones in `rd` when the chain before it did not borrow. -/
def selMask (rd : LowReg) : List Instr := [.dp .sbcs rd rd, .dp .mvns rd rd]

theorem selMask_run (rd : LowReg) (v : State) :
    (execAll (selMask rd) v).regs rd.toReg = (if v.c then BitVec.allOnes 32 else 0#32) ∧
    (execAll (selMask rd) v).mem = v.mem ∧
    ∀ r : Reg, r ≠ rd.toReg → r ≠ 15 → (execAll (selMask rd) v).regs r = v.regs r := by
  refine ⟨?_, by simp [selMask, execAll, Ed25519Sha512Exec.mem_dp], fun r h3 h15 => ?_⟩
  · have e := Ed25519Barrett.borrow_mask (v.regs rd.toReg) v.c
    simp [selMask, execAll, Instr.next, Instr.exec, State.setReg, State.reg, State.setNZ, State.setNZCV,
      addFlags, addWithCarry] at e ⊢
    exact e
  · have h3' : r.val ≠ rd.val := fun h => h3 (Fin.ext (by simp [LowReg.toReg, h]))
    simp only [selMask, execAll]
    rw [Ed25519Sha512Exec.nx_keep _ r h15 _ (by simp [Instr.dsts]; omega),
      Ed25519Sha512Exec.nx_keep _ r h15 _ (by simp [Instr.dsts]; omega)]

end M0Crypto.Release.Ed25519ScalarChain
