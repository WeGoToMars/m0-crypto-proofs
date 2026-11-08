import M0Crypto.Thumb.Seq

/-!
Linear-time evaluation of `seqAt` for the byte checks.

`seqAt bytes off is` fetches each instruction with `instrAt bytes off`, and `hwAt`
reads the artifact with `List.getD`, which walks the list from its head. A check
over a block at offset `off` therefore costs about (instructions) × (offset) list
steps, and the kernel repeats that work when it re-checks the proof.

`seqScan` takes the artifact from the current offset on (`bytes.drop off`), so each
fetch reads only the first few cells. `seqAt_eq_scan` proves that the two agree for
every offset, so a byte check may rewrite `seqAt` to `seqScan` and then evaluate it.
This is a proof device: no statement mentions `seqScan`, and the same bytes and the
same decoder are checked.
-/

namespace M0Crypto.Thumb

/-- `seqAt` for an artifact already cut at the offset of its first instruction. -/
def seqScan : List (BitVec 8) → List Instr → Bool
  | _, [] => true
  | bs, i :: is =>
    instrAt bs 0 == some i && decide (i.size ≤ bs.length) && seqScan (bs.drop i.size) is

theorem getD_drop (bytes : List (BitVec 8)) (off k : Nat) (d : BitVec 8) :
    (bytes.drop off).getD k d = bytes.getD (off + k) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem hwAt_drop (bytes : List (BitVec 8)) (off k : Nat) :
    hwAt (bytes.drop off) k = hwAt bytes (off + k) := by
  simp only [hwAt, getD_drop, Nat.add_assoc]

theorem instrAt_drop (bytes : List (BitVec 8)) (off : Nat) :
    instrAt (bytes.drop off) 0 = instrAt bytes off := by
  simp only [instrAt, hwAt_drop, Nat.add_zero]

/-- `instrAt` for an artifact already cut at the instruction's offset. -/
def instrScan (bs : List (BitVec 8)) : Option Instr := instrAt bs 0

/-- Single-instruction facts: `instrScan` is a definition, so rewriting with this lemma
does not re-enter `instrAt`. -/
theorem instrAt_eq_scan (bytes : List (BitVec 8)) (off : Nat) :
    instrAt bytes off = instrScan (bytes.drop off) :=
  (instrAt_drop bytes off).symm

theorem instr_size_pos (i : Instr) : 0 < i.size := by
  cases i <;> simp [Instr.size]

/-- Every event of a fall-through instruction sequence lies at an offset
within that sequence from its initial PC. -/
theorem traceAll_pc_offset : ∀ (is : List Instr) (s : M0Crypto.Armv6M.State),
    is.all Instr.falls = true → ∀ e ∈ traceAll is s,
      ∃ off < seqSize is, e.pc = s.pc + BitVec.ofNat 32 off
  | [], _, _, e, he => by cases he
  | i :: is, s, hf, e, he => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [traceAll, List.mem_cons] at he
    rcases he with rfl | he
    · refine ⟨0, ?_, by simp⟩
      simp only [seqSize, List.map_cons, List.sum_cons]
      have := instr_size_pos i
      omega
    · obtain ⟨off, hoff, hpc⟩ := traceAll_pc_offset is (i.next s) hf.2 e he
      refine ⟨i.size + off, ?_, ?_⟩
      · simp only [seqSize, List.map_cons, List.sum_cons] at *
        omega
      · have hn : (i.next s).pc = s.pc + BitVec.ofNat 32 i.size := by
          have h := execAll_pc [i] s (by simpa using hf.1)
          simpa [execAll, seqSize] using h
        rw [hpc, hn, ofNat_add_assoc]

theorem seqAt_eq_scan (bytes : List (BitVec 8)) : ∀ (is : List Instr) (off : Nat),
    seqAt bytes off is = seqScan (bytes.drop off) is
  | [], _ => rfl
  | i :: is, off => by
    have hpos := instr_size_pos i
    have hlen : decide (off + i.size ≤ bytes.length) =
        decide (i.size ≤ (bytes.drop off).length) := by
      rw [List.length_drop]
      apply decide_eq_decide.mpr
      omega
    simp only [seqAt, seqScan, instrAt_drop, hlen, List.drop_drop]
    rw [seqAt_eq_scan bytes is (off + i.size)]

end M0Crypto.Thumb
