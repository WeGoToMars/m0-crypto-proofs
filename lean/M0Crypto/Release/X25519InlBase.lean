import M0Crypto.Release.X25519MulcFacts
import M0Crypto.Release.X25519Sites
import M0Crypto.Release.Field25519AddSubChain

set_option linter.unusedSimpArgs false

/-!
The four straight-line bodies that `m0c_x25519` instantiates inline (generator
`tools/gen_x25519.py`: `fe_add_body`, `fe_sub_body`, `select_words`, `canon_body`) as
instruction lists, a check of each list against the release bytes at a real site of the
entry, and the facts the four run lemmas share (`X25519InlAdd`, `X25519InlSub`,
`X25519InlSel`, `X25519InlCanon`).

A site is found, not written down: `siteOf is` is the offset of the first instruction of the
entry (`X25519Code.entryCode`) where the decoded instructions start with `is`. The `*_at`
checks then evaluate `seqAt` there, so a wrong list or a missing site fails the check.

Shared facts: the 8-word output frame (`Field25519Frame.FrameOk`) seen through `feVal`
(`feVal_of_frame`), the bytes outside `Region dst 32` (`mem_of_frame`), and the reads of an
input that is `dst` or disjoint from it (`read_in`).
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region)
open M0Crypto.Release.Frame (Disj InFrame toNat_add_ofNat sub_ofNat_toNat)
open M0Crypto.Release.Field25519Frame (FrameOk upd)
open M0Crypto.Release.Field25519Facts (psum psum_lt psum_congr feVal_psum)
open M0Crypto.Release.Field25519AddSubChain

/-! ## Sites in the entry -/

/-- Offset of the first instruction of the entry where the decoded instructions begin with
`is`; `0` if none (the `*_at` checks below then fail). -/
def siteOf (is : List Instr) : Nat :=
  go X25519Code.entryCode
where
  go : List (Nat × Instr) → Nat
    | [] => 0
    | l@((o, _) :: rest) => if is.isPrefixOf (l.map Prod.snd) then o else go rest

/-- A site of `is` in the entry: `seqAt` holds at `siteOf is`, inside the entry. -/
def SiteOk (is : List Instr) : Prop :=
  Artifacts.Release.x25519 ≤ siteOf is ∧ seqAt B (siteOf is) is = true

/-! ## Accesses -/

theorem ldm_acc {Wr : Word → Prop} (s : State) (n : LowReg) (l : BitVec 8)
    (h : (s.reg n).toNat % 4 = 0) : ∀ a ∈ (Instr.ldm n l).accesses s, Field25519Block.AccOk Wr a :=
  Field25519Block.wordAccesses_ok h (fun e => by cases e)

theorem stm_acc {Wr : Word → Prop} (s : State) (n : LowReg) (l : BitVec 8)
    (h : (s.reg n).toNat % 4 = 0)
    (hw : ∀ i < bitCount l, ∀ q < 4, Wr (s.reg n + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    ∀ a ∈ (Instr.stm n l).accesses s, Field25519Block.AccOk Wr a :=
  Field25519Block.wordAccesses_ok h (fun _ => hw)

theorem ld34_acc {Wr : Word → Prop} (s : State) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : Field25519Block.AccAll (Field25519Block.AccOk Wr) ld34 s := by
  refine Field25519Block.accAll_cons (ldm_acc s 1 _ h1) (Field25519Block.accAll_cons (ldm_acc _ 2 _ ?_)
    (Field25519Block.accAll_nil _ _))
  have : ((Instr.ldm 1 0x18).next s).regs 2 = s.regs 2 := by
    simp (config := {decide := true}) only [Field25519Mem.regs_ldm, listRegs_18, List.map,
      Field25519Mem.toReg3, Field25519Mem.toReg4, Field25519Mem.toReg1, List.mem_cons, List.not_mem_nil,
      ite_false, or_self]
  show (((Instr.ldm 1 0x18).next s).regs (LowReg.toReg 2)).toNat % 4 = 0
  rw [Field25519Mem.toReg2, this]; exact h2

/-- The bytes `j < 32` of `dst` are the bytes of its 8 words. -/
theorem wr_words {Wr : Word → Prop} {dst : Word} (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j))
    {k n : Nat} (hk : k + n ≤ 8) :
    ∀ i < n, ∀ q < 4, Wr (slot dst k + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q) := by
  intro i hi q hq
  rw [slot, ofNat_add_assoc, ofNat_add_assoc]
  exact hW _ (by omega)

end M0Crypto.Release.X25519Inl
