import M0Crypto.Release.X25519Layout
import SafegcdTermination.StackCopy

namespace M0Crypto.Release.X25519SafegcdCode

open M0Crypto.Release.X25519Layout
open M0Crypto.Thumb
open SafegcdRow.BatchCode (frameBytes callTo withSp)
open SafegcdTermination.StackCopy

/-- Preserve `X2` in the dead clamped scalar slot, above the inversion frame. -/
def parked : Nat := sK

def borrowed : Nat := frameBytes-parked

def before : List Instr := code parked sX2 ++
  [withSp 0 sZ2,.movHi 1 0,.subSp (BitVec.ofNat 7 (borrowed/4))]

def after : List Instr := .addSp (BitVec.ofNat 7 (borrowed/4)) :: code sX2 parked

def callSite (off : Nat) : Nat := off+seqSize before

def afterSite (off : Nat) : Nat := callSite off+4

def body (off target : Nat) : List Instr := before ++ [callTo (callSite off) target] ++ after

structure Linked (bytes : List (BitVec 8)) (off dst : Nat) : Prop where
  pre : seqAt bytes off before = true
  call : seqAt bytes (callSite off) [callTo (callSite off) dst] = true
  post : seqAt bytes (afterSite off) after = true

theorem linked_of_body {bytes : List (BitVec 8)} {off dst : Nat}
    (h : seqAt bytes off (body off dst) = true) : Linked bytes off dst := by
  simp only [body,seqAt_append,Bool.and_eq_true, seqSize_append] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

end M0Crypto.Release.X25519SafegcdCode
