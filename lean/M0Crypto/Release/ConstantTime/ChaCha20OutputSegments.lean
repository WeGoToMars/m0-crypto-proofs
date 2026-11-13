import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ConstantTime.ChaCha20OutputAccess
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Writes

/-! Functional output-loop segments in the artifact execution. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Reg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout

/-- A sequence of aligned output chunks executes with every event covered by
its functional chunk invariant. This proves segment coverage for the entire
straight-line word-output path, not just an individual store. -/
theorem output_chunks_runH (c : ACall) (xc : Frame.Ctx) (hv : Frame.Valid xc)
    (hout : xc.out = c.out) (hlenEq : xc.len = c.len) (block : Nat)
    (hlen : 64 * block + 64 ≤ xc.len.toNat) :
    ∀ count i, i + count ≤ 16 → ∀ t : State,
      t.pc = xc.base + BitVec.ofNat 32 (achOff + achSize * i) →
      t.regs 3 = xc.out + BitVec.ofNat 32 (64 * block) →
      (t.regs 13).toNat % 4 = 0 → (t.regs 2).toNat % 4 = 0 →
      (t.regs 3).toNat % 4 = 0 →
      ∃ steps u tr, runH B xc.base steps t = .ok (u, tr) ∧
        u.pc = xc.base + BitVec.ofNat 32 (achOff + achSize * (i + count)) ∧
        (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 15 → u.regs r = t.regs r) ∧
        (∀ e ∈ tr, OutputSegmentEvent c e) ∧
        (t.regs 13 = xc.fp → t.regs 2 = xc.inp + BitVec.ofNat 32 (64 * block) →
         ReadsFrom (TraceSpec.ChaCha20XorReadRegion xc) tr)
  | 0, i, _, t, hpc, _, _, _, _ => by
    refine ⟨0, t, [], rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hpc
    · intro r _ _ _; rfl
    · simp
    · intro _ _; exact ReadsFrom.nil _
  | count + 1, i, hi, t, hpc, h3, ha13, ha2, ha3 => by
    have hi16 : i < 16 := by omega
    have hbase : xc.base.toNat % 2 = 0 := by have := hv.base4; omega
    have heffect := (ach_effect t i hi16).2
    have hpc' : (execAll (ach i) t).pc =
        xc.base + BitVec.ofNat 32 (achOff + achSize * (i + 1)) := by
      rw [execAll_pc _ _ (ach_falls i), hpc, ofNat_add_assoc, ach_size, off_step]
    have hr3 := heffect 3 (by decide) (by decide) (by decide)
    have hr2 := heffect 2 (by decide) (by decide) (by decide)
    have hr13 := heffect 13 (by decide) (by decide) (by decide)
    obtain ⟨steps, u, tr, hrun, hupc, hregs, hcover, hreads⟩ :=
      output_chunks_runH c xc hv hout hlenEq block hlen count (i + 1) (by omega)
        (execAll (ach i) t) hpc' (hr3.trans h3) (by rw [hr13]; exact ha13)
        (by rw [hr2]; exact ha2) (by rw [hr3]; exact ha3)
    refine ⟨(ach i).length + steps, u, traceAll (ach i) t ++ tr, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runH_block hbase (by rw [B_len]; decide) (ach i) _ t hpc
        (ach_pc_even i) (ach_seq i hi16) (ach_falls i)
        (ach_aligned t i hi16 ha13 ha2 ha3), hrun]
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hupc
    · intro r h0 h1 h15
      exact (hregs r h0 h1 h15).trans (heffect r h0 h1 h15)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact ⟨xc, hv, hout, hlenEq, block, t, h3,
          Or.inl ⟨i, hi16, by omega, he⟩⟩
      · exact hcover e he

    · intro hsp hin
      apply ReadsFrom.append (aligned_chunk_reads_contract xc block i t hi16 hsp hin (by omega))
      apply hreads
      · exact hr13.trans hsp
      · exact hr2.trans hin

set_option maxRecDepth 100000 in
/-- One byte-tail iteration has the same segment coverage, with its loop
counter bounded by the remaining output length. -/
theorem output_tail_runH (c : ACall) (xc : Frame.Ctx) (hv : Frame.Valid xc)
    (hout : xc.out = c.out) (hlenEq : xc.len = c.len) (block : Nat)
    (t : State) (hpc : t.pc = xc.base + BitVec.ofNat 32 blOff)
    (h3 : t.regs 3 = xc.out + BitVec.ofNat 32 (64 * block))
    (hbound : 64 * block + (t.regs 0).toNat < xc.len.toNat) :
    runH B xc.base bl.length t = .ok (execAll bl t, traceAll bl t) ∧
    ∀ e ∈ traceAll bl t, OutputSegmentEvent c e := by
  have hbase : xc.base.toNat % 2 = 0 := by have := hv.base4; omega
  constructor
  · rw [runH_seq hbase (by rw [B_len]; decide) bl blOff t hpc (by decide) bl_at (by decide),
      runSeq_eq bl t (by decide)]
    simp [alignedAll, bl, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, Nat.mod_one]
  · intro e he
    exact ⟨xc, hv, hout, hlenEq, block, t, h3, Or.inr ⟨hbound, he⟩⟩


set_option maxRecDepth 100000 in
/-- Execute the complete nonempty byte-tail loop. Every event either belongs
 to a bounded tail segment or has no memory accesses. -/
theorem output_tail_loop_runH (c : ACall) (xc : Frame.Ctx) (hv : Frame.Valid xc)
    (hout : xc.out = c.out) (hlenEq : xc.len = c.len) (block N : Nat)
    (hN : N ≤ 64) (hlen : 64 * block + N ≤ xc.len.toNat) :
    ∀ count p, p + count = N → 0 < count → ∀ t : State,
      t.pc = xc.base + BitVec.ofNat 32 blOff →
      t.regs 0 = BitVec.ofNat 32 p → t.regs 4 = BitVec.ofNat 32 N →
      t.regs 3 = xc.out + BitVec.ofNat 32 (64 * block) →
      ∃ steps u tr, runH B xc.base steps t = .ok (u, tr) ∧
        u.pc = xc.base + BitVec.ofNat 32 n1Off ∧
        (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → u.regs r = t.regs r) ∧
        (∀ e ∈ tr, OutputSegmentEvent c e ∨ e.accesses = []) ∧
        (t.regs 2 = xc.inp + BitVec.ofNat 32 (64 * block) →
         t.regs 5 = xc.fp → ReadsFrom (TraceSpec.ChaCha20XorReadRegion xc) tr)
  | 0, _, _, hp, _, _, _, _, _ => by omega
  | count + 1, p, hcount, hp, t, hpc, h0, h4, h3 => by
    have hbase : xc.base.toNat % 2 = 0 := by have := hv.base4; omega
    have hpN : p < N := by omega
    have hpval : (t.regs 0).toNat = p := by
      rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbound : 64 * block + (t.regs 0).toNat < xc.len.toNat := by rw [hpval]; omega
    obtain ⟨hbody, hbodyCover⟩ := output_tail_runH c xc hv hout hlenEq block t hpc h3 hbound
    let u := execAll bl t
    have upc : u.pc = xc.base + BitVec.ofNat 32 bloOff := by
      rw [show u = execAll bl t from rfl, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
      rfl
    obtain ⟨_, u0, uc, ur⟩ := bl_effect t
    have ec : u.c = decide (N ≤ p + 1) := by
      change (execAll bl t).c = _
      rw [uc, h4, h0, ofNat_succ]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    let branch := Instr.bcond 3 (brImm8 bloOff blOff)
    by_cases hmore : p + 1 < N
    · have hcond : condPassed 3 u = true := by
        rw [ChaCha20Setup.condPassed_3, ec]; simp [show ¬ N ≤ p + 1 by omega]
      let next := u.setReg 15 (xc.base + BitVec.ofNat 32 blOff)
      have htarget : u.pc + 4#32 + ((brImm8 bloOff blOff) ++ 0#1).signExtend 32 =
          xc.base + BitVec.ofNat 32 blOff := by
        have hjump : BitVec.ofNat 32 bloOff + (4#32 + ((brImm8 bloOff blOff) ++ 0#1).signExtend 32) =
            BitVec.ofNat 32 blOff := by decide
        rw [upc, BitVec.add_assoc, BitVec.add_assoc, hjump]
      have hs : stepH B xc.base u = .ok (next, ⟨u.pc, branch, []⟩) := by
        apply stepH_of_instr hbase (by rw [B_len]; decide) upc (by decide) blo_at (by rw [B_len]; decide)
          (by simp [branch, Instr.accesses])
        change branch.exec u = .ok next
        simp only [branch, Instr.exec, hcond, ite_true, htarget]
        rfl
      have nr : ∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 6 → r.val ≠ 15 → next.regs r = t.regs r := by
        intro r a b d e
        rw [show next = u.setReg 15 _ from rfl, ChaCha20Setup.setReg15_regs _ _ r e]
        exact ur r a b d e
      have n0 : next.regs 0 = BitVec.ofNat 32 (p + 1) := by
        rw [show next = u.setReg 15 _ from rfl, ChaCha20Setup.setReg15_regs _ _ 0 (by decide), u0, h0, ofNat_succ]
      have n4 : next.regs 4 = BitVec.ofNat 32 N := by rw [nr 4 (by decide) (by decide) (by decide) (by decide), h4]
      have n3 : next.regs 3 = xc.out + BitVec.ofNat 32 (64 * block) := by rw [nr 3 (by decide) (by decide) (by decide) (by decide), h3]
      obtain ⟨steps, last, tr, hrun, hlast, hregs, hcover, hreads⟩ :=
        output_tail_loop_runH c xc hv hout hlenEq block N hN hlen count (p + 1) (by omega) (by omega)
          next (ChaCha20Setup.setReg15_pc _ _) n0 n4 n3
      refine ⟨bl.length + (steps + 1), last, traceAll bl t ++ ⟨u.pc, branch, []⟩ :: tr, ?_, hlast, ?_, ?_, ?_⟩
      · rw [runH_add, hbody]
        change (match runH B xc.base (steps + 1) u with
          | Except.error e => Except.error e
          | Except.ok (s', tr') => Except.ok (s', traceAll bl t ++ tr')) =
            Except.ok (last, traceAll bl t ++ ⟨u.pc, branch, []⟩ :: tr)
        rw [runH_one_step steps hs, hrun]
      · intro r a b d e; exact (hregs r a b d e).trans (nr r a b d e)
      · intro e he; rcases List.mem_append.mp he with he | he
        · exact Or.inl (hbodyCover e he)
        · rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr rfl
          · exact hcover e he
      · intro h2 h5
        have nr2 : next.regs 2 = xc.inp + BitVec.ofNat 32 (64 * block) := by
          rw [nr 2 (by decide) (by decide) (by decide) (by decide), h2]
        have nr5 : next.regs 5 = xc.fp := by
          rw [nr 5 (by decide) (by decide) (by decide) (by decide), h5]
        apply ReadsFrom.append (byte_tail_reads_contract xc block t h2 h5 (by rw [hpval]; omega) hbound)
        intro e he y hy
        rcases List.mem_cons.mp he with rfl | he
        · simp [Reads] at hy
        · exact hreads nr2 nr5 e he y hy
    · have hcond : condPassed 3 u = false := by
        rw [ChaCha20Setup.condPassed_3, ec]; simp [show N ≤ p + 1 by omega]
      let next := u.setReg 15 (xc.base + BitVec.ofNat 32 n1Off)
      have htarget : u.pc + 2#32 = xc.base + BitVec.ofNat 32 n1Off := by
        rw [upc, show (2#32 : M0Crypto.Armv6M.Word) = BitVec.ofNat 32 2 from rfl,
          ofNat_add_assoc, blo_next]
      have hs : stepH B xc.base u = .ok (next, ⟨u.pc, branch, []⟩) := by
        apply stepH_of_instr hbase (by rw [B_len]; decide) upc (by decide) blo_at (by rw [B_len]; decide)
          (by simp [branch, Instr.accesses])
        change branch.exec u = .ok next
        simp only [branch, Instr.exec, hcond, Bool.false_eq_true, ite_false, Instr.size, htarget]
        rfl
      refine ⟨bl.length + 1, next, traceAll bl t ++ [⟨u.pc, branch, []⟩], ?_, ?_, ?_, ?_, ?_⟩
      · rw [runH_add, hbody]
        change (match runH B xc.base 1 u with
          | Except.error e => Except.error e
          | Except.ok (s', tr') => Except.ok (s', traceAll bl t ++ tr')) =
            Except.ok (next, traceAll bl t ++ [⟨u.pc, branch, []⟩])
        rw [runH_one_step 0 hs]; rfl
      · exact ChaCha20Setup.setReg15_pc _ _
      · intro r a b d e
        rw [show next = u.setReg 15 _ from rfl, ChaCha20Setup.setReg15_regs _ _ r e]
        exact ur r a b d e
      · intro e he; rcases List.mem_append.mp he with he | he
        · exact Or.inl (hbodyCover e he)
        · simp only [List.mem_singleton] at he; subst e; exact Or.inr rfl
      · intro h2 h5
        apply ReadsFrom.append (byte_tail_reads_contract xc block t h2 h5 (by rw [hpval]; omega) hbound)
        intro e he y hy
        simp only [List.mem_singleton] at he
        subst e
        simp [Reads] at hy


/-- The instruction interval of a word-output chunk or the byte-tail body.
 Its bounds are derived from the functional instruction sequences. -/
def outputInstructionSite (off : Nat) : Bool :=
  (List.range 16).any (fun j =>
    decide (achOff + achSize * j ≤ off ∧ off < achOff + achSize * j + seqSize (ach j))) ||
  decide (blOff ≤ off ∧ off < blOff + seqSize bl)

def walkOutputSites (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    (!untrackedStore st i || (ctx == some decAcceptAt && outputInstructionSite off)) &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out => match out.succs with
      | [(_, next)] => walkOutputSites env ctx (off + i.size) next is
      | _ => walkOutputSites env ctx (off + i.size) st is


/-- The functional frame-or-output write bound preserves the release code. -/
theorem chacha20_write_misses_code (xc : Frame.Ctx) (hv : Frame.Valid xc)
    {y : M0Crypto.Armv6M.Word} (hw : xc.Wr y) {i : Nat} (hi : i < B.length) :
    y ≠ xc.base + BitVec.ofNat 32 i := by
  have hi' : i < M0Crypto.Artifacts.Release.size := by simpa [B_len] using hi
  rcases hw with ⟨o, ho, rfl⟩ | hout
  · obtain ⟨h1, h2, h3⟩ := hv.codeF
    have := ChaCha20Layout.chStackBytes_eq
    exact Frame.ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) hi'
  · obtain ⟨h1, h2, h3⟩ := hv.codeO
    rw [Frame.eq_add_sub xc.out y]
    exact Frame.ne_of_disj h2 h1 (by omega) hout hi'

end M0Crypto.Release.ConstantTime
