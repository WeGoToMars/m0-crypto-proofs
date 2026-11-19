import SafegcdTermination.InitCode
import SafegcdTermination.Bank
import SafegcdTermination.Packing

namespace SafegcdTermination.InitWords

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.InitCode
open SafegcdTermination.LoopCounter (initialCount)
open SafegcdTermination.Bank
open M0Crypto.Armv6M (State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

theorem save_arguments (s : State) :
    let t := execAll saveAndCall s
    t.regs 0 = addr s.sp temp ∧ t.regs 1 = s.regs 1 ∧ t.sp = s.sp ∧
      t.mem = write32 (write32 s.mem (addr s.sp returnAt) (s.regs 14)) (addr s.sp outputAt) (s.regs 0) := by
  unfold saveAndCall storeSp withSp imm addr returnAt frameBytes outputAt temp vectorBytes
  row_simps

theorem initial_words (s : State) :
    let t := execAll putInitialWords s
    t.sp = s.sp ∧ t.mem =
      write32 (write32 (write32 s.mem (addr s.sp bankE) 1) (addr s.sp deltaAt) 1)
        (addr s.sp counterAt) (BitVec.ofNat 32 initialCount) := by
  unfold putInitialWords storeSp imm addr bankE deltaAt outputAt counterAt vectorBytes initialCount LoopCounter.triplets batchCount
  row_simps
  rfl

theorem split_column (s : State) (i : Nat) (hi : i < 8) :
    let t := execAll (splitColumn i) s
    let v := stackWord s (temp+4*i)
    t.sp = s.sp ∧ t.mem =
      write32 (write32 s.mem (addr s.sp (bankG+8*i)) (low v))
        (addr s.sp (bankG+8*i+4)) (v >>> 16) := by
  have he (x : Nat) (h : x = temp+4*i ∨ x = bankG+8*i ∨ x = bankG+8*i+4) :
      x / 4 % 256 * 4 = x := by
    have hT : temp = 272 := rfl
    have hG : bankG = 68 := rfl
    rcases h with rfl | rfl | rfl <;> omega
  have eT := he (temp+4*i) (.inl rfl)
  have eL := he (bankG+8*i) (.inr (.inl rfl))
  have eH := he (bankG+8*i+4) (.inr (.inr rfl))
  unfold splitColumn loadSp storeSp imm addr stackWord stackAddr
  row_simps
  have h : ((bankG + 8*i) / 4 + 1) % 256 * 4 = bankG+8*i+4 := by omega
  simp only [← Nat.mul_comm 4 i, ← Nat.mul_comm 8 i, eT, eL, h, BitVec.ofNat_add, BitVec.add_assoc]

def primeWords : List Word := [65517] ++ List.replicate 14 65535 ++ [32767]

open M0Crypto.Sym M0Crypto.Release.BlockEffect

def primeExpr (i : Nat) : SExpr :=
  let mask := SExpr.uxth (.not (.const 0))
  if i = 0 then .awc mask (.const (~~~18#32)) (.const true)
  else if i = 15 then .lsr mask 1 else mask

def storeExprWords (a : SExpr) (m : SMem) : List SExpr → SMem
  | [] => m
  | v :: vs => storeExprWords (.add a (.const 4)) (.w32 m a v) vs

theorem denote_storeExprWords (s : State) (a : SExpr) (m : SMem) (xs : List SExpr) :
    (storeExprWords a m xs).denote s = storeWords (m.denote s) (a.denote s) (xs.map (·.denote s)) := by
  induction xs generalizing a m with
  | nil => rfl
  | cons x xs ih =>
    simp only [storeExprWords, ih, SMem.denote, SExpr.denote, List.map_cons, storeWords]
    rfl

def primeExprWords : List SExpr := (List.range 16).map primeExpr

def primeEffect : Eff :=
  { clob := [0,1,2,3,7], mem := some (storeExprWords (.reg0 13) .mem0 primeExprWords) }

theorem prime_effect : effOk putPrime primeEffect = true := by decide +kernel

theorem put_prime (s : State) :
    let t := execAll putPrime s
    t.sp = s.sp ∧ t.mem = storeWords s.mem s.sp primeWords := by
  have h := eff_run prime_effect s
  refine ⟨h.reg 13 (by decide) (by decide), ?_⟩
  have hmem := h.mem _ rfl
  rw [denote_storeExprWords] at hmem
  have scalar (i : Nat) : (primeExpr i).denote s = if i = 0 then 65517 else if i = 15 then 32767 else 65535 := by
    unfold primeExpr
    split
    · simp only [SExpr.denote, SBool.denote]; decide +kernel
    · split <;> simp only [SExpr.denote] <;> decide +kernel
  have e : primeExprWords.map (·.denote s) = primeWords := by
    simp only [primeExprWords, List.map_map, Function.comp_def, scalar]
    decide +kernel
  rw [e] at hmem
  exact hmem

end SafegcdTermination.InitWords
