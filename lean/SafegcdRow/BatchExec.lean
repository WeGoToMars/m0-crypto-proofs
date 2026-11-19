import M0Crypto.Thumb.Branch
import SafegcdRow.BatchCode

namespace SafegcdRow.BatchCode

open M0Crypto.Armv6M (State LowReg Mem slot read32 write32)
open M0Crypto.Thumb
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

def stackAddr (s : State) (o : Nat) : Word := s.sp + BitVec.ofNat 32 o
def stackWord (s : State) (o : Nat) : Word := read32 s.mem (stackAddr s o)

theorem matrix_arguments (i : Fin 3) (s : State) :
    let t := execAll (prepareMatrix (phases i)) s
    let f := (phases i).f
    t.regs 0 = stackWord s f ||| (stackWord s (f + 4) <<< 16) ∧
    t.regs 1 = stackWord s bankG ||| (stackWord s (bankG + 4) <<< 16) ∧
    t.regs 2 = stackWord s deltaAt ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  rcases phase_cases i with rfl | rfl | rfl <;>
    unfold prepareMatrix loadSp imm stackWord stackAddr <;>
    row_simps <;> exact ⟨rfl, rfl, rfl⟩

theorem matrix_saved (s : State) :
    let t := execAll saveMatrix s
    t.mem = storeWords (write32 s.mem (stackAddr s deltaAt) (s.regs 2))
      (stackAddr s matrixAt) [s.regs 3, s.regs 4, s.regs 5, s.regs 6] ∧ t.sp = s.sp := by
  unfold saveMatrix storeSp withSp imm stackAddr
  row_simps
  rfl

private theorem imm_value (o : Nat) (h : o % 4 = 0 ∧ o < 1024) :
    (imm o).toNat * 4 = o := by
  simp only [imm, BitVec.toNat_ofNat]
  omega

theorem row_arguments (r : RowCall) (s : State)
    (hd : r.dst % 4 = 0 ∧ r.dst < 1024) (hx : r.x % 4 = 0 ∧ r.x < 1024)
    (hy : r.y % 4 = 0 ∧ r.y < 1024) (hc : r.coeff ≤ 2) :
    let t := execAll (prepareRow r) s
    t.regs 0 = stackAddr s r.dst ∧ t.regs 1 = stackAddr s r.x ∧ t.regs 2 = stackAddr s r.y ∧
    t.regs 3 = stackWord s (matrixAt + 4 * r.coeff) ∧
    t.regs 4 = stackWord s (matrixAt + 4 * (r.coeff + 1)) ∧
    t.mem = s.mem ∧ t.sp = s.sp := by
  have hm : matrixAt = 352 := rfl
  have hc₁ : (matrixAt + 4 * r.coeff) % 4 = 0 ∧ matrixAt + 4*r.coeff < 1024 := by omega
  have hc₂ : (matrixAt + 4 * (r.coeff+1)) % 4 = 0 ∧ matrixAt + 4*(r.coeff+1) < 1024 := by omega
  unfold prepareRow loadSp withSp stackWord stackAddr
  row_simps
  simp only [Nat.mul_comm r.coeff 4, Nat.mul_comm (r.coeff + 1) 4,
    imm_value _ hd, imm_value _ hx, imm_value _ hy, imm_value _ hc₁, imm_value _ hc₂,
    BitVec.ofNat_add, and_self]

def literalAddress (s : State) (lit : BitVec 8) : Word :=
  ((s.pc + BitVec.ofNat 32 (seqSize correctionPrefix + 4)) &&& ~~~3#32) + BitVec.ofNat 32 (4 * lit.toNat)

theorem correction_argument (s : State) (lit : BitVec 8) :
    let t := execAll (prepareCorrection lit) s
    let n := s.regs 3 * read32 s.mem (s.regs 1) + s.regs 4 * read32 s.mem (s.regs 2)
    let k := read32 s.mem (literalAddress s lit)
    t.regs 5 = ((n*k) <<< 18) >>> 18 ∧ t.regs 0 = s.regs 0 ∧ t.regs 1 = s.regs 1 ∧
      t.regs 2 = s.regs 2 ∧ t.regs 3 = s.regs 3 ∧ t.regs 4 = s.regs 4 ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  unfold prepareCorrection literalAddress correctionPrefix
  row_simps
  simp only [seqSize, Instr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.mul_comm lit.toNat 4]
  congr 2
  exact BitVec.mul_comm _ _

theorem call_at {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (ho' : off + 4 < 2^23) (hd : dest < 2^23)
    (hat : seqAt code off [callTo off dest] = true) :
    let lr := (base + BitVec.ofNat 32 (off + 4)) ||| 1#32
    let t := (s.setReg 14 lr).setReg 15 (base + BitVec.ofNat 32 dest)
    stepH code base s = .ok (t, ⟨s.pc, callTo off dest, []⟩) := by
  obtain ⟨⟨hi, hs⟩, _⟩ := (by simpa only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hat :
    (instrAt code off = some (callTo off dest) ∧ off + (callTo off dest).size ≤ code.length) ∧ True)
  apply stepH_of_instr hb hlen hpc ho hi hs (by rfl)
  dsimp only [callTo, Instr.exec]
  have hret : base + BitVec.ofNat 32 off + 4#32 = base + BitVec.ofNat 32 (off + 4) := by
    rw [ofNat_add_assoc]
  have hcall : base + BitVec.ofNat 32 off + 4#32 +
      (BitVec.ofInt 25 ((dest : Int) - (off + 4))).signExtend 32 =
      base + BitVec.ofNat 32 dest := by
    calc
      _ = base + ((BitVec.ofNat 32 off + 4#32) +
          (BitVec.ofInt 25 ((dest : Int) - (off + 4))).signExtend 32) := by
        simp only [BitVec.add_assoc]
      _ = _ := by rw [bl_target off dest ho' hd]
  rw [hpc, hcall, hret]

def entered (base : Word) (off dest : Nat) (s : State) : State :=
  (s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15 (base + BitVec.ofNat 32 dest)

theorem run_call {code : List (BitVec 8)} {base : Word} {off dest n : Nat} {s t : State}
    {trace : List Event} (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (ho' : off + 4 < 2^23) (hd : dest < 2^23)
    (hat : seqAt code off [callTo off dest] = true)
    (h : runH code base n (entered base off dest s) = .ok (t, trace)) :
    runH code base (n+1) s = .ok (t, ⟨s.pc, callTo off dest, []⟩ :: trace) := by
  rw [runH_one_step n (call_at hb hlen hpc ho ho' hd hat)]
  change (match runH code base n (entered base off dest s) with
    | .error e => Except.error e
    | .ok (u, tr) => .ok (u, _ :: tr)) = _
  rw [h]

theorem execute_pre {code : List (BitVec 8)} {base : Word} {off : Nat} {is : List Instr}
    {s : State} (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt code off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) :
    runH code base is.length s = .ok (execAll is s, traceAll is s) ∧
      (execAll is s).pc = base + BitVec.ofNat 32 (off + seqSize is) := by
  refine ⟨?_, ?_⟩
  · rw [runH_seq hb hlen is off s hpc ho hat hf, runSeq_eq _ _ hf ha]
  · rw [execAll_pc _ _ hf, hpc, ofNat_add_assoc]

theorem correction_aligned (s : State) (lit : BitVec 8)
    (hx : (s.regs 1).toNat % 4 = 0) (hy : (s.regs 2).toNat % 4 = 0) :
    alignedAll (prepareCorrection lit) s = true := by
  have hl : (literalAddress s lit).toNat % 4 = 0 := by
    simp only [literalAddress, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_and]
    have he : ∀ n : Nat, (n &&& 4294967292) % 4 = 0 := by
      intro n
      rw [← Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.and_assoc]
      first | rfl | simp
    have hm := he ((s.pc.toNat + seqSize correctionPrefix + 4) % 4294967296)
    simp only [seqSize, correctionPrefix, Instr.size, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_assoc, Nat.reduceAdd, Nat.reducePow, BitVec.toNat_not,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceSub] at hm ⊢
    omega
  unfold prepareCorrection correctionPrefix
  simp only [List.cons_append, List.nil_append, alignedAll]
  row_simps
  simp only [Access.aligned, hx, hy, beq_self_eq_true, Bool.and_self, Bool.and_true, Bool.true_and]
  have he : ((s.regs 15 + 14#32 &&& 4294967292#32) + BitVec.ofNat 32 (lit.toNat * 4)) =
      literalAddress s lit := by
    simp only [literalAddress, State.pc, Nat.mul_comm 4]
    rfl
  simp [he, hl]

end SafegcdRow.BatchCode
