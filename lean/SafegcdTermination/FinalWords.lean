import SafegcdTermination.FinalCode
import SafegcdTermination.Packing
import M0Crypto.Release.Field25519CRLoop

namespace SafegcdTermination.FinalWords

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.FinalCode
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.Bank
open SafegcdTermination.Packing
open SafegcdTermination.FoldRefine (vec value)
open M0Crypto.Armv6M (State Mem read32 write32)
open M0Crypto.Thumb

set_option maxRecDepth 8000
set_option maxHeartbeats 450000
set_option linter.unusedSimpArgs false

theorem pack_column (s : State) (i : Nat) (hi : i < 8) :
    let t := execAll (packColumn i) s
    t.sp = s.sp ∧ t.mem = write32 s.mem (addr s.sp (bankF+4*i))
      (halfPair (stackWord s (bankF+8*i)) (stackWord s (bankF+8*i+4))) := by
  have eL : (8*i) / 4 % 256 * 4 = 8*i := by omega
  have eH : ((8*i)/4+1) % 256 * 4 = 8*i+4 := by omega
  have eO : i % 256 * 4 = 4*i := by omega
  unfold packColumn loadSp storeSp imm addr stackWord stackAddr halfPair bankF
  row_simps
  simp only [← Nat.mul_comm 4 i, ← Nat.mul_comm 8 i, eL, eH, eO, BitVec.ofNat_add, BitVec.add_assoc]

theorem sub_args (s : State) :
    let t := execAll subArgs s
    t.regs 0 = addr s.sp bankE ∧ t.regs 1 = addr s.sp bankG ∧ t.regs 2 = s.sp ∧
      t.mem = s.mem ∧ t.sp = s.sp := by
  unfold subArgs withSp imm addr
  row_simps

theorem select_args (s : State) :
    let t := execAll selectArgs s
    t.regs 3 = (stackWord s (temp+vectorBytes-4)).sshiftRight 31 ∧
      t.regs 0 = stackWord s outputAt ∧ t.regs 1 = s.sp ∧ t.regs 2 = addr s.sp bankE ∧
      t.mem = s.mem ∧ t.sp = s.sp := by
  unfold selectArgs loadSp withSp imm stackWord stackAddr addr
  row_simps
  exact ⟨rfl, rfl⟩

theorem top_sign (m : Mem) (a : Word) (hl : Vectors.LowLimbs m a) :
    (vec m a 16).toInt < 0 ↔ value m a < 0 := by
  rw [Vectors.field_top m a hl]
  have hp : 0 < radix ^ 16 := by decide +kernel
  rw [Int.ediv_lt_iff_lt_mul hp, Int.zero_mul]

theorem top_zero (m : Mem) (a : Word) (hl : Vectors.LowLimbs m a)
    (h : 0 ≤ value m a ∧ value m a < foldRadix) : vec m a 16 = 0#32 := by
  have hp : 0 < radix^16 := by decide +kernel
  have hR : foldRadix ≤ radix^16 := by decide +kernel
  have e := Vectors.field_top m a hl
  rw [Int.ediv_eq_zero_of_lt h.1 (Int.lt_of_lt_of_le h.2 hR)] at e
  apply BitVec.eq_of_toInt_eq
  exact e

open M0Crypto.Armv6M (slot)
open M0Crypto.Release.Frame (read32_congr slot_byte_ne' read32_storeWords_same)
open M0Crypto.Release.Field25519Routines (feVal)

def packedWords (s : State) (n : Nat) : List Word :=
  (List.range n).map fun i => halfPair (vec s.mem s.sp (2*i)) (vec s.mem s.sp (2*i+1))

theorem packed_next (s : State) (n : Nat) :
    packedWords s (n+1) = packedWords s n ++ [halfPair (vec s.mem s.sp (2*n)) (vec s.mem s.sp (2*n+1))] := by
  simp [packedWords, List.range_succ]

theorem packed_read_old (s : State) (n j : Nat) (hn : n ≤ j) (hj : j < 16) :
    vec (storeWords s.mem s.sp (packedWords s n)) s.sp j = vec s.mem s.sp j := by
  apply read32_congr
  intro k hk
  apply storeWords_other
  intro i b hi hb
  have hlen : (packedWords s n).length = n := by simp [packedWords]
  rw [hlen] at hi
  exact slot_byte_ne' s.sp j i k b (by omega) (by omega) hk hb (by omega)

theorem pack_exec (s : State) (n : Nat) (hn : n ≤ 8) :
    let t := execAll ((List.range n).flatMap packColumn) s
    t.sp = s.sp ∧ t.mem = storeWords s.mem s.sp (packedWords s n) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h := ih (by omega)
    dsimp only at h ⊢
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, execAll_append]
    let u := execAll ((List.range n).flatMap packColumn) s
    obtain ⟨hSp,hMem⟩ := pack_column u n (by omega)
    have hUsp : u.sp = s.sp := h.1
    have hUmem : u.mem = storeWords s.mem s.sp (packedWords s n) := h.2
    have hRead (j : Nat) (hj : n ≤ j) (h16 : j < 16) :
        stackWord u (4*j) = vec s.mem s.sp j := by
      change read32 u.mem (addr u.sp (4*j)) = _
      rw [hUsp,hUmem]
      exact packed_read_old s n j hj h16
    have hL : stackWord u (bankF+8*n) = vec s.mem s.sp (2*n) := by
      rw [show bankF+8*n = 4*(2*n) by unfold bankF; omega]
      exact hRead _ (by omega) (by omega)
    have hH : stackWord u (bankF+8*n+4) = vec s.mem s.sp (2*n+1) := by
      rw [show bankF+8*n+4 = 4*(2*n+1) by unfold bankF; omega]
      exact hRead _ (by omega) (by omega)
    refine ⟨hSp.trans h.1, ?_⟩
    rw [hMem,hL,hH,hUsp,hUmem,packed_next,
      M0Crypto.Release.Field25519CR.storeWords_snoc]
    simp [addr, bankF, packedWords]

theorem packed_value (s : State) (h : VecWellFormed (vec s.mem s.sp)) (hTop : vec s.mem s.sp 16 = 0#32) :
    value s.mem s.sp = (feVal (storeWords s.mem s.sp (packedWords s 8)) s.sp : Int) := by
  apply vector_packed _ _ _ _ hTop
  intro i hi
  have hLen : i < (packedWords s 8).length := by simpa [packedWords] using hi
  have hRead := read32_storeWords_same s.mem s.sp (packedWords s 8) i hLen (by simp [packedWords])
  simp only [packedWords, List.getElem_map, List.getElem_range] at hRead
  have hv : vec (storeWords s.mem s.sp (packedWords s 8)) s.sp i =
      halfPair (vec s.mem s.sp (2*i)) (vec s.mem s.sp (2*i+1)) := hRead
  rw [hv]
  exact halfPair_value _ _ (h.1 _ (by omega)) (h.1 _ (by omega))

theorem pack_value (s : State) (h : VecWellFormed (vec s.mem s.sp)) (hTop : vec s.mem s.sp 16 = 0#32) :
    (feVal (execAll pack s).mem s.sp : Int) = value s.mem s.sp := by
  have hExec := (pack_exec s 8 (by decide)).2
  exact (congrArg (fun m => (feVal m s.sp : Int)) hExec).trans (packed_value s h hTop).symm

end SafegcdTermination.FinalWords
