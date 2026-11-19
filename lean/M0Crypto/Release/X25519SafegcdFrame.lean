import M0Crypto.Release.X25519SafegcdCode
import SafegcdTermination.LinkedInversion

namespace M0Crypto.Release.X25519SafegcdFrame

open M0Crypto.Armv6M (State Word)
open M0Crypto.Release.X25519Layout M0Crypto.Release.X25519SafegcdCode
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)
open SafegcdRow.BatchCode (frameBytes vectorBytes bankE temp outputAt)
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.Bank (addr FrameOk)
open SafegcdTermination.FinalSelect (OutputOk)
open SafegcdTermination.RunInit (SourceOk)

set_option linter.unusedSimpArgs false

def workSp (sp : Word) : Word := sp - BitVec.ofNat 32 borrowed

structure Space (sp : Word) : Prop where
  align : sp.toNat % 4 = 0
  below : borrowed ≤ sp.toNat
  above : sp.toNat + LFRAME ≤ 2^32

theorem numbers : parked = 288 ∧ borrowed = 88 ∧ frameBytes = 376 := by decide

theorem work_toNat {sp : Word} (hs : Space sp) : (workSp sp).toNat = sp.toNat - borrowed := by
  have hn := hs.below
  simp only [workSp, BitVec.toNat_sub]
  have h : (BitVec.ofNat 32 borrowed).toNat = borrowed := by decide
  rw [h]
  have hBound := sp.isLt
  omega

theorem frame_ok {sp : Word} (hs : Space sp) : FrameOk (workSp sp) := by
  obtain ⟨hb,hc,hd⟩ := numbers
  have hh := hs.above
  have hl := hs.below
  have ha := hs.align
  simp only [FrameOk,work_toNat hs,hc,hd,LFRAME] at *
  constructor <;> omega

private theorem addr_nat {sp : Word} (hs : Space sp) (o : Nat) (ho : o < LFRAME) :
    (addr sp o).toNat = sp.toNat+o := by
  have h := hs.above
  exact toNat_add_ofNat _ _ (by omega)

private theorem work_addr_nat {sp : Word} (hs : Space sp) (o : Nat) (ho : o < frameBytes) :
    (addr (workSp sp) o).toNat = sp.toNat-borrowed+o := by
  rw [SafegcdTermination.Bank.addr_nat (frame_ok hs) o ho,work_toNat hs]

theorem copy_disj {sp : Word} (hs : Space sp) : Disj (addr sp parked) 32 (addr sp sX2) 32 := by
  unfold Disj
  rw [addr_nat hs _ (by decide),addr_nat hs _ (by decide)]
  have ha := hs.above
  simp only [numbers.1,sX2,LFRAME] at *
  omega

theorem source_ok {old : Word} {s : State} (hs : Space old) (hSp : s.sp = workSp old)
    (hSrc : s.regs 1 = addr old sZ2) : SourceOk s := by
  have hAlign := hs.align
  have hBound := hs.above
  have hLo := hs.below
  have hTmp := work_addr_nat hs temp (by decide)
  have hOut := work_addr_nat hs outputAt (by decide)
  have hRet := work_addr_nat hs returnAt (by decide)
  have hDst := addr_nat hs sZ2 (by decide)
  refine ⟨by rw [hSrc,hDst]; simp [sZ2,Nat.add_mod,hAlign],?_,?_,?_⟩ <;>
    simp only [hSp,hSrc,Disj,hTmp,hOut,hRet,hDst,numbers.2.1,temp,vectorBytes,
      LFRAME,outputAt,returnAt,numbers.2.2,sZ2] at * <;> omega

theorem output_ok {sp : Word} (hs : Space sp) : OutputOk (workSp sp) (addr sp sZ2) := by
  have hAlign := hs.align
  have hBound := hs.above
  have hLo := hs.below
  have hE := work_addr_nat hs bankE (by decide)
  have hRet := work_addr_nat hs returnAt (by decide)
  have hDst := addr_nat hs sZ2 (by decide)
  refine ⟨by rw [hDst]; simp [sZ2,Nat.add_mod,hAlign],.inr ?_,.inr ?_,?_⟩ <;>
    simp only [Disj,work_toNat hs,hE,hRet,hDst,numbers.2.1,bankE,vectorBytes,
      LFRAME,returnAt,numbers.2.2,sZ2] at * <;> omega

/-- Span that can change, including the parked `X2` but ending before the output pointer. -/
def span : Nat := borrowed+lvOut

theorem rebase (sp : Word) (o : Nat) : addr sp o = addr (workSp sp) (borrowed+o) := by
  unfold addr workSp
  rw [BitVec.ofNat_add]
  bv_omega

theorem cut {base sp : Word} {n o len : Nat} (h : Disj base n (workSp sp) span)
    (hLen : 0 < len) (ho : o+len ≤ span) : Disj base n (addr (workSp sp) o) len := by
  have hb := h.1
  have hs := h.2.1
  have hAt := toNat_add_ofNat (workSp sp) o (by omega)
  refine ⟨hb,?_,?_⟩
  · show (addr (workSp sp) o).toNat + len ≤ 2^32
    rw [addr,hAt]
    omega
  · show base.toNat+n ≤ (addr (workSp sp) o).toNat ∨ (addr (workSp sp) o).toNat+len ≤ base.toNat
    rw [addr,hAt]
    rcases h.2.2 with hleft | hright
    · left; omega
    · right; omega

end M0Crypto.Release.X25519SafegcdFrame
