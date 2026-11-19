import SafegcdTermination.Canon
import SafegcdTermination.FrameWords

namespace SafegcdTermination.StackCopy

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.InitCode (copyWords)
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open M0Crypto.Armv6M (State)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def addresses (dst src : Nat) : List Instr := [withSp 0 dst, withSp 1 src]

def code (dst src : Nat) : List Instr := addresses dst src ++ copyWords

private theorem arguments (s : State) (dst src : Nat)
    (hd : dst % 4 = 0 ∧ dst < 1024) (hs : src % 4 = 0 ∧ src < 1024) :
    let a := execAll (addresses dst src) s
    a.regs 0 = addr s.sp dst ∧ a.regs 1 = addr s.sp src ∧ a.mem = s.mem ∧ a.sp = s.sp := by
  have h1 : dst/4 % 256*4 = dst := by omega
  have h2 : src/4 % 256*4 = src := by omega
  unfold addresses withSp imm addr
  row_simps
  simp [h1,h2]

/-- Copy between aligned, disjoint field slots in the caller's frame. -/
theorem exec (s : State) (dst src : Nat)
    (hd : dst % 4 = 0 ∧ dst < 1024) (hs : src % 4 = 0 ∧ src < 1024)
    (h : Disj (addr s.sp dst) 32 (addr s.sp src) 32) :
    let t := execAll (code dst src) s
    t.sp = s.sp ∧ feVal t.mem (addr s.sp dst) = feVal s.mem (addr s.sp src) ∧
      WritesOnly s.mem t.mem (addr s.sp dst) 32 := by
  let a := execAll (addresses dst src) s
  obtain ⟨a0,a1,aM,aS⟩ := arguments s dst src hd hs
  have hsep : Disj (a.regs 0) 32 (a.regs 1) 32 := by rw [a0,a1]; exact h
  obtain ⟨_,hSp,hMem⟩ := Canon.copy_words a hsep.1 hsep.2.1 hsep.2.2
  simp only [code,execAll_append]
  refine ⟨hSp.trans aS,?_,?_⟩
  · have hEq := Canon.copy_value a
    rw [← hMem,a0,a1,aM] at hEq
    exact hEq
  · rw [hMem,a0,aM]
    intro y hy
    apply storeWords_other
    intro i j hi hj
    simp only [Canon.sourceWords,List.length_map,List.length_range] at hi
    rw [ofNat_add_assoc]
    exact hy _ (by omega)

end SafegcdTermination.StackCopy
