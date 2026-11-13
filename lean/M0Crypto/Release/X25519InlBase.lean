import M0Crypto.Release.X25519MulcFacts
import M0Crypto.Release.X25519Sites

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

Shared facts: the 8-word output frame (`X25519Frame.FrameOk`) seen through `feVal`
(`feVal_of_frame`), the bytes outside `Region dst 32` (`mem_of_frame`), and the reads of an
input that is `dst` or disjoint from it (`read_in`).
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region)
open M0Crypto.Release.Frame (Disj InFrame toNat_add_ofNat sub_ofNat_toNat)
open M0Crypto.Release.X25519Frame (FrameOk upd)
open M0Crypto.Release.X25519MulcChain (psum psum_lt psum_congr)
open M0Crypto.Release.X25519MulcFacts (feVal_psum)

/-! ## Instruction lists -/

/-- `ldm r1!, {r3, r4}; ldm r2!, {r5, r6}`. -/
def ld34 : List Instr := [.ldm 1 0x18, .ldm 2 0x60]

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

/-! ## Register lists -/

theorem listRegs_18 : listRegs 0x18 = [3, 4] := by decide
theorem listRegs_60 : listRegs 0x60 = [5, 6] := by decide
theorem listRegs_06 : listRegs 0x06 = [1, 2] := by decide
theorem listRegs_7e : listRegs 0x7e = [1, 2, 3, 4, 5, 6] := by decide
theorem bitCount_18 : bitCount 0x18 = 2 := by decide
theorem bitCount_60 : bitCount 0x60 = 2 := by decide
theorem bitCount_06 : bitCount 0x06 = 2 := by decide
theorem bitCount_7e : bitCount 0x7e = 6 := by decide

/-! ## Single instructions not covered elsewhere -/

theorem regs_ands (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .ands d m).next s).regs r = if r = d.toReg then s.reg d &&& s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_orrs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .orrs d m).next s).regs r = if r = d.toReg then s.reg d ||| s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem c_ands (s : State) (d m : LowReg) : ((Instr.dp .ands d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem c_orrs (s : State) (d m : LowReg) : ((Instr.dp .orrs d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

/-! ## Pointers -/

theorem slot_slot (p : Word) (k j : Nat) : slot (slot p k) j = slot p (k + j) := by
  simp only [slot, ofNat_add_assoc, Nat.mul_add]

theorem slot_zero (p : Word) : slot p 0 = p := by simp [slot]

theorem slot_al {p : Word} (h : p.toNat % 4 = 0) (k : Nat) : (slot p k).toNat % 4 = 0 := by
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- `ldm r1!, {r3, r4}; ldm r2!, {r5, r6}`: two words through each pointer. -/
theorem ld34_exec (s : State) :
    let t := execAll ld34 s
    t.regs 3 = read32 s.mem (slot (s.regs 1) 0) ∧ t.regs 4 = read32 s.mem (slot (s.regs 1) 1) ∧
      t.regs 5 = read32 s.mem (slot (s.regs 2) 0) ∧ t.regs 6 = read32 s.mem (slot (s.regs 2) 1) ∧
      t.regs 1 = slot (s.regs 1) 2 ∧ t.regs 2 = slot (s.regs 2) 2 ∧ t.mem = s.mem ∧ t.c = s.c ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t
  have hm : t.mem = s.mem := execAll_mem _ _ (by decide)
  have hc : t.c = s.c := by
    simp only [t, ld34, execAll, X25519Mem.c_ldm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm, hc, ?_⟩
  rotate_left 6
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    simp (config := {decide := true}) only [t, ld34, execAll, X25519Mem.regs_ldm _ _ _ _ h15,
      listRegs_18, listRegs_60, List.map, X25519Mem.toReg1, X25519Mem.toReg2, X25519Mem.toReg3,
      X25519Mem.toReg4, X25519Mem.toReg5, X25519Mem.toReg6, List.mem_cons, List.not_mem_nil,
      h1, h2, h3, h4, h5, h6, or_self, ite_false]
  all_goals
    simp (config := {decide := true}) only [t, ld34, execAll, X25519Mem.regs_ldm, X25519Mem.mem_ldm,
      listRegs_18, listRegs_60, bitCount_18, bitCount_60, List.map, X25519Mem.toReg1,
      X25519Mem.toReg2, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5, X25519Mem.toReg6,
      ite_true, ite_false, List.mem_cons, List.idxOf, State.reg, ne_eq]
    first | rfl | (simp only [slot, ofNat_add_assoc]; done) | skip

/-! ## Accesses -/

theorem ldm_acc {Wr : Word → Prop} (s : State) (n : LowReg) (l : BitVec 8)
    (h : (s.reg n).toNat % 4 = 0) : ∀ a ∈ (Instr.ldm n l).accesses s, X25519Block.AccOk Wr a :=
  X25519Block.wordAccesses_ok h (fun e => by cases e)

theorem stm_acc {Wr : Word → Prop} (s : State) (n : LowReg) (l : BitVec 8)
    (h : (s.reg n).toNat % 4 = 0)
    (hw : ∀ i < bitCount l, ∀ q < 4, Wr (s.reg n + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    ∀ a ∈ (Instr.stm n l).accesses s, X25519Block.AccOk Wr a :=
  X25519Block.wordAccesses_ok h (fun _ => hw)

theorem ld34_acc {Wr : Word → Prop} (s : State) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : X25519Block.AccAll (X25519Block.AccOk Wr) ld34 s := by
  refine X25519Block.accAll_cons (ldm_acc s 1 _ h1) (X25519Block.accAll_cons (ldm_acc _ 2 _ ?_)
    (X25519Block.accAll_nil _ _))
  have : ((Instr.ldm 1 0x18).next s).regs 2 = s.regs 2 := by
    simp (config := {decide := true}) only [X25519Mem.regs_ldm, listRegs_18, List.map,
      X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg1, List.mem_cons, List.not_mem_nil,
      ite_false, or_self]
  show (((Instr.ldm 1 0x18).next s).regs (LowReg.toReg 2)).toNat % 4 = 0
  rw [X25519Mem.toReg2, this]; exact h2

/-! ## The 8-word output -/

/-- The output buffer before any store. -/
theorem frame_init (m : Mem) {dst : Word} (h : dst.toNat + 32 ≤ 2 ^ 32) :
    FrameOk dst 8 m (fun i => read32 m (slot dst i)) m :=
  ⟨by omega, fun _ _ => rfl, fun _ _ => rfl⟩

theorem feVal_frame {dst : Word} {m0 m : Mem} {F : Nat → Word} (h : FrameOk dst 8 m0 F m) :
    X25519Routines.feVal m dst = psum (fun i => (F i).toNat) 8 := by
  rw [feVal_psum]; exact psum_congr fun i hi => by rw [h.slots i hi]

/-- Bytes outside `Region dst 32` are as in `m0`. -/
theorem frame_out {dst : Word} {m0 m : Mem} {F : Nat → Word} (h : FrameOk dst 8 m0 F m) (y : Word)
    (hy : ¬ Region dst 32 y) : m y = m0 y :=
  h.out y fun ⟨o, ho, e⟩ => hy (by
    subst e
    show (dst + BitVec.ofNat 32 o - dst).toNat < 32
    rw [sub_ofNat_toNat _ _ (by omega)]; omega)

/-- Word `i` of an input that is `dst` or disjoint from it, read while the words of `dst`
from `j` on are not yet written. -/
theorem read_in {dst p : Word} {m0 m : Mem} {F : Nat → Word} {j i : Nat}
    (h : FrameOk dst 8 m0 F m) (hF : ∀ i, j ≤ i → i < 8 → F i = read32 m0 (slot dst i))
    (hp : p = dst ∨ Disj p 32 dst 32) (hji : j ≤ i) (hi : i < 8) :
    read32 m (slot p i) = read32 m0 (slot p i) := by
  rcases hp with rfl | hd
  · rw [h.slots i hi, hF i hji hi]
  · exact h.read_disj hd (by omega)

/-- The bytes `j < 32` of `dst` are the bytes of its 8 words. -/
theorem wr_words {Wr : Word → Prop} {dst : Word} (hW : ∀ j < 32, Wr (dst + BitVec.ofNat 32 j))
    {k n : Nat} (hk : k + n ≤ 8) :
    ∀ i < n, ∀ q < 4, Wr (slot dst k + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q) := by
  intro i hi q hq
  rw [slot, ofNat_add_assoc, ofNat_add_assoc]
  exact hW _ (by omega)

end M0Crypto.Release.X25519Inl
