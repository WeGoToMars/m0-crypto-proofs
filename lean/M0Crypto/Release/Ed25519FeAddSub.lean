import M0Crypto.Release.Ed25519Routines
import M0Crypto.Release.Field25519AddSub
import M0Crypto.Release.Ed25519FieldRoutines

set_option linter.unusedSimpArgs false

/-!
# `m0c_fe_add` and `m0c_fe_sub`

Both are `push {lr}`, a straight-line body of the `Field25519` family (`fe_add_body`,
`fe_sub_body`) and `pop {pc}`. `wrap_tspec` proves the call lemma of any such routine from the
body's value lemma and the decided checks of its accesses and trace; `add_tspec` and `sub_tspec`
apply it to the two bodies at any offset, and `fe_add_tspec`, `fe_sub_tspec` to the offsets of
each build.
-/

namespace M0Crypto.Release.Ed25519FeAddSub

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519AddSub (feAddBody feSubBody)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts

section

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- `push {lr}`, `body`, `pop {pc}`. -/
def wrap (body : List Instr) : List Instr := .push 0 true :: body ++ [.pop 0 true]

/-- The decided checks of a body: it falls through, keeps `sp`, aligns `r0`-`r2`, writes the
32 bytes from `r0`, reads the 32 bytes from `r1` and from `r2`, and its trace reads `r0`-`r2`. -/
def bodyOk (body : List Instr) : Bool :=
  body.all Instr.falls && keepsSp body && seqSize body % 2 == 0 && Sym.alignChk [(0, 4), (1, 4), (2, 4)] body &&
  Sym.writeChk [((0 : Reg), 0#32, 32)] body &&
  Sym.readChk (fun _ => true) [((1 : Reg), 0#32, 32), ((2 : Reg), 0#32, 32)] body &&
  traceOk body [0, 1, 2]

/-- `feVal` across a frame fact apart from its 32 bytes. -/
theorem feVal_memEq {W : List Rgn} {m m' : Mem} {a : Word} (h : MemEq W m m')
    (hs : Sep [⟨a, 32⟩] W) : feVal m' a = feVal m a := by
  have hb := h.bytes hs
  unfold feVal; congr 1; apply List.map_congr_left; intro i hi
  have hi8 : i < 8 := List.mem_range.mp hi
  rw [Frame.read32_congr fun k hk => ?_]
  have e := congrArg (·[4 * i + k]?) hb
  simp only [bytesAt, List.getElem?_map, List.getElem?_range, show 4 * i + k < 32 by omega,
    ↓reduceIte, Option.map_some, Option.some.injEq] at e
  rw [ofNat_add_assoc]; exact e

/-- **A field routine `push {lr}; body; pop {pc}`** whose body computes `fn` into `dst`. -/
theorem wrap_tspec {body : List Instr} {fn : Int → Int → Int} {o : Nat}
    (hex : ∀ s : State, (s.regs 0).toNat + 32 ≤ 2 ^ 32 →
      ModP (feVal (execAll body s).mem (s.regs 0)) (fn (feVal s.mem (s.regs 1)) (feVal s.mem (s.regs 2))))
    (hok : bodyOk body = true) (hseq : seqAt B o (wrap body) = true) (ho : o % 2 = 0) :
    Routine.TSpec (fun _ : Unit => fieldR o (seqSize (wrap body)) 4 true fn) (fieldPub true) := by
  simp only [bodyOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hf, hk⟩, hev⟩, ha⟩, hw⟩, hr⟩, htr⟩ := hok
  simp only [beq_iff_eq] at hev
  have e2 : seqSize [Instr.push 0 true] = 2 := rfl
  have hs := hseq
  rw [wrap, ← List.singleton_append, seqAt_append, seqAt_append, seqSize_append, e2, ← Nat.add_assoc] at hs
  simp only [Bool.and_eq_true] at hs
  have hpush : instrAt B o = some (.push 0 true) := instrAt_of_seqAt hs.1.1
  have hpop : instrAt B (o + 2 + seqSize body) = some (.pop 0 true) := instrAt_of_seqAt hs.2
  have hsz : seqSize (wrap body) = seqSize body + 4 := by
    simp [wrap, seqSize_append, seqSize, Instr.size]; omega
  have hlen : o + seqSize (wrap body) ≤ BS := by
    have := seqAt_size B o _ hseq
    rw [B_len] at this
    exact this.resolve_right (by simp [wrap])
  rw [hsz] at hlen
  trefine Routine.tspec_by (fun _ base s e => ?_) (fun _ _ => ?_)
  generalize hP : fieldPub true base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 2 = P 2 ∧ s.regs 13 = P 3 := by
    subst hP; exact ⟨rfl, rfl, rfl, rfl⟩
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  obtain ⟨h0, h1, h2, -, -⟩ := e.pre
  have hcode : rangesSub [(o, o + 2), (o + 2 + seqSize body, o + 2 + seqSize body + 2)]
      [(o, o + (seqSize body + 4))] = true := by
    simp only [rangesSub, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  trefine ReachFT.push_popK (f := fieldR o (seqSize (wrap body)) 4 true fn) (mask := 0)
    (epi := o + 2 + seqSize body) (by decide) hpush hpop ho (by omega) (by simp only [fieldR]; omega)
    (by omega)
    (by rw [show (fieldR o (seqSize (wrap body)) 4 true fn).code = [(o, o + (seqSize body + 4))]
      by simp [fieldR, hsz]]; exact hcode) (by show 4 * nSaved 0 ≤ 4; decide) e q.2.2.2 ?_
  intro t tpc t13 tr hm hc
  have r0 := tr 0 (by decide) (by decide); have r1 := tr 1 (by decide) (by decide)
  have r2 := tr 2 (by decide) (by decide)
  have hwin := e.sepRd
  have hsW := e.sepWr
  simp only [fieldR, ite_true] at hwin hsW
  trefine ReachFT.block hb2 body (o + 2) tpc (by omega) hs.1.2 hf hk
    (PcIn.region (cs := [(o, o + seqSize (wrap body))]) (List.mem_singleton_self _) (by omega)
      (by rw [hsz]; omega))
    [(0, 4), (1, 4), (2, 4)] [((0 : Reg), 0#32, 32)] [((1 : Reg), 0#32, 32), ((2 : Reg), 0#32, 32)]
    ha hw hr (by simp [r0, r1, r2, h0, h1, h2]) ?_ ?_ ⟨4, by simp [fieldR], t13⟩
    (traceAll_blockTr (L := [0, 1, 2]) (vs := [P 0, P 1, P 2]) hf htr tpc
      (by simp [r0, r1, r2, q.1, q.2.1, q.2.2.1])) ?_
  · rintro y ⟨r, hr', hy⟩
    simp only [regions, List.map, List.mem_singleton] at hr'; subst hr'
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by simpa [r0] using hy⟩
  · rintro y ⟨r, hr', hy⟩
    simp only [regions, List.map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨⟨s.regs 1, 32⟩, by simp [fieldR], by simpa [r1] using hy⟩
    · exact ⟨⟨s.regs 2, 32⟩, by simp [fieldR], by simpa [r2] using hy⟩
  refine ReachT.done ⟨?_, ?_, fun r h4 h11 _ hK => absurd (mem_hiRegs h4 h11) hK, ?_⟩
  · rw [execAll_pc _ _ hf, tpc, ofNat_add_assoc]; rfl
  · exact execAll_regs_other _ _ 13 (by decide) hk
  · have hd : (t.regs 0).toNat + 32 ≤ 2 ^ 32 := by
      rw [r0]; exact (hsW _ List.mem_cons_self _ List.mem_cons_self).1
    have ex := hex t hd
    have hsv := saved0_eq (f := fieldR o (seqSize (wrap body)) 4 true fn) (s := s) rfl
    rw [r0, r1, r2, feVal_memEq hm (hsv ▸ sep_of_mem List.mem_cons_self hwin),
      feVal_memEq hm (hsv ▸ sep_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hwin)] at ex
    exact ex
  uniq_tac

theorem add_tspec {o : Nat} (hseq : seqAt B o (wrap feAddBody) = true) (ho : o % 2 = 0) :
    Routine.TSpec (fun _ : Unit => fieldR o (seqSize (wrap feAddBody)) 4 true (· + ·)) (fieldPub true) :=
  wrap_tspec (fun s h => (Field25519AddSub.feAdd_exec s h).1) (by decide +kernel) hseq ho

theorem sub_tspec {o : Nat} (hseq : seqAt B o (wrap feSubBody) = true) (ho : o % 2 = 0) :
    Routine.TSpec (fun _ : Unit => fieldR o (seqSize (wrap feSubBody)) 4 true (· - ·)) (fieldPub true) :=
  wrap_tspec (fun s h => (Field25519AddSub.feSub_exec s h).1) (by decide +kernel) hseq ho

end

/-- `m0c_fe_add` in each build. -/
theorem fe_add_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => fieldR Ed25519Compact.fe_add (seqSize (wrap feAddBody)) 4 true (· + ·)) (fieldPub true) := by
  exact @add_tspec _ _ b.codeBytes _ (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)

/-- `m0c_fe_sub` in each build. -/
theorem fe_sub_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => fieldR Ed25519Compact.fe_sub (seqSize (wrap feSubBody)) 4 true (· - ·)) (fieldPub true) := by
  exact @sub_tspec _ _ b.codeBytes Ed25519Compact.fe_sub (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)

end M0Crypto.Release.Ed25519FeAddSub
