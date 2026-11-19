import M0Crypto.Release.X25519SafegcdFrame

namespace M0Crypto.Release.X25519SafegcdSave

open M0Crypto.Armv6M (State Word)
open M0Crypto.Release.X25519Layout M0Crypto.Release.X25519SafegcdCode M0Crypto.Release.X25519SafegcdFrame
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Thumb
open SafegcdRow.BatchCode (withSp imm)
open SafegcdTermination.Bank (addr WritesOnly)
open SafegcdTermination.FrameWords (keep_field)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def shareArgs : List Instr := [withSp 0 sZ2,.movHi 1 0,.subSp (BitVec.ofNat 7 (borrowed/4))]

def raiseSp : List Instr := [.addSp (BitVec.ofNat 7 (borrowed/4))]

theorem park_code : before = SafegcdTermination.StackCopy.code parked sX2 ++ shareArgs := rfl

theorem restore_code : after = raiseSp ++ SafegcdTermination.StackCopy.code sX2 parked := rfl

private theorem args (s : State) :
    let t := execAll shareArgs s
    t.regs 0 = addr s.sp sZ2 ∧ t.regs 1 = addr s.sp sZ2 ∧ t.sp = workSp s.sp ∧ t.mem = s.mem := by
  unfold shareArgs workSp withSp imm addr
  row_simps

private theorem raise (s : State) (sp : Word) (hSp : s.sp = workSp sp) :
    let t := execAll raiseSp s
    t.sp = sp ∧ t.mem = s.mem := by
  dsimp only
  have h : (execAll raiseSp s).sp = s.sp + BitVec.ofNat 32 borrowed := by
    unfold raiseSp
    row_simps
  rw [h,hSp]
  unfold workSp
  constructor
  · bv_omega
  · rfl

structure Saved (root t : State) : Prop where
  sp : t.sp = workSp root.sp
  out : t.regs 0 = addr root.sp sZ2
  src : t.regs 1 = addr root.sp sZ2
  value : feVal t.mem (addr root.sp sZ2) = feVal root.mem (addr root.sp sZ2)
  park : feVal t.mem (addr root.sp parked) = feVal root.mem (addr root.sp sX2)
  outside : WritesOnly root.mem t.mem (addr root.sp parked) 32

theorem save (s : State) (hs : Space s.sp) : Saved s (execAll before s) := by
  let a := execAll (SafegcdTermination.StackCopy.code parked sX2) s
  obtain ⟨hS,hVal,hW⟩ := SafegcdTermination.StackCopy.exec s parked sX2 (by decide) (by decide) (copy_disj hs)
  have hIn := keep_field (off := sZ2) hS hW (by decide) (by decide) (.inl (by decide))
  obtain ⟨h0,h1,h2,hM⟩ := args a
  rw [park_code,execAll_append]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [h2,hS]
  · rw [h0,hS]
  · rw [h1,hS]
  · rw [hS] at hIn
    rw [hM]
    exact hIn
  · rw [hM,hVal]
  · rw [hM]
    exact hW

theorem restore (s : State) (sp : Word) (hs : Space sp) (hSp : s.sp = workSp sp) :
    let t := execAll after s
    t.sp = sp ∧ feVal t.mem (addr sp sX2) = feVal s.mem (addr sp parked) ∧
      feVal t.mem (addr sp sZ2) = feVal s.mem (addr sp sZ2) ∧ WritesOnly s.mem t.mem (addr sp sX2) 32 := by
  let a := execAll raiseSp s
  obtain ⟨aS,aM⟩ := raise s sp hSp
  have h : Disj (addr a.sp sX2) 32 (addr a.sp parked) 32 := by
    rw [aS]
    obtain ⟨h1,h2,h3⟩ := copy_disj hs
    exact ⟨h2,h1,h3.symm⟩
  obtain ⟨tS,hVal,hW⟩ := SafegcdTermination.StackCopy.exec a sX2 parked (by decide) (by decide) h
  have hIn := keep_field (off := sZ2) tS hW (by decide) (by decide) (.inr (by decide))
  rw [tS,aS,aM] at hIn
  rw [aS,aM] at hVal hW
  rw [restore_code,execAll_append]
  exact ⟨tS.trans aS,hVal,hIn,hW⟩

end M0Crypto.Release.X25519SafegcdSave
