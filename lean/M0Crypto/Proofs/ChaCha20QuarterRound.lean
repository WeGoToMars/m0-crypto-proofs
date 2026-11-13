import M0Crypto.Spec.ChaCha20
import M0Crypto.Spec.ChaCha20Vectors
import M0Crypto.Armv6M.StraightLine
import M0Crypto.Proofs.ChaCha20Common
import M0Crypto.Artifacts.ChaCha20QuarterRound

/-!
Refinement proof for the linked bytes of `m0c_chacha20_qr_frag`
(fixtures/chacha20_qr.S, extracted into `M0Crypto.Artifacts.ChaCha20QuarterRound`).

Main results, for every starting state whose PC is the fragment's link address:
* `run_eq`: exactly 16 steps execute without fault.
* `trace_independent`: the executed trace does not depend on registers, flags
  or memory (data-independent control flow and instruction sequence).
* `qr_correct`: r0-r3 hold RFC 8439 `quarterRound` of the initial r0-r3.
* `qr_frame`: PC advances by 32; r5-r14 and memory are unchanged.
  r4 and N/Z/C/V are clobbered and unspecified.
-/

namespace M0Crypto.Proofs.ChaCha20QuarterRound

open M0Crypto.Armv6M
open M0Crypto.Spec.ChaCha20 (quarterRound)
open M0Crypto.Proofs (rorC_eq_rotl addWithCarry_fst)

/-- The linked code region of the fragment. -/
def code : Code := ⟨Artifacts.ChaCha20QuarterRound.base, Artifacts.ChaCha20QuarterRound.bytes⟩

/-- The instruction sequence the bytes must decode to. Checked by `decodes`, not trusted. -/
def instrs : List Instr :=
  [ .movsImm 4 16, .addsReg 0 0 1, .eorsReg 3 0, .rorsReg 3 4,
    .addsReg 2 2 3, .eorsReg 1 2, .movsImm 4 20, .rorsReg 1 4,
    .addsReg 0 0 1, .eorsReg 3 0, .movsImm 4 24, .rorsReg 3 4,
    .addsReg 2 2 3, .eorsReg 1 2, .movsImm 4 25, .rorsReg 1 4 ]

theorem code_length : code.bytes.length = 32 := by decide

/-- The extracted bytes decode exactly to `instrs` from the link address. -/
theorem decodes : decodesAt code code.base instrs = true := by decide

theorem noMem : ∀ i ∈ instrs, i.isMem = false := by decide

/-- Starting at the link address, 16 steps run without fault. -/
theorem run_eq (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base) :
    run code 16 s = .ok (execAll instrs s, execTrace instrs s) := by
  have htn : s.pc.toNat = code.base := by rw [hpc]; decide
  exact run_straight code instrs s (by rw [htn]; exact decodes)
    (alignedAll_noMem instrs s noMem) (by rw [htn]; decide)

/-- Constant-time property at the trace level: any two starting states at the link
address execute the same instructions at the same addresses, with no data accesses. -/
theorem trace_independent (s₁ s₂ : State)
    (h₁ : s₁.pc = BitVec.ofNat 32 code.base) (h₂ : s₂.pc = BitVec.ofNat 32 code.base) :
    (run code 16 s₁).map Prod.snd = (run code 16 s₂).map Prod.snd := by
  rw [run_eq s₁ h₁, run_eq s₂ h₂]
  simp only [Except.map, execTrace_congr_noMem instrs s₁ s₂ noMem (h₁.trans h₂.symm)]

theorem exec_all_regs (s : State) :
    let s' := execAll instrs s
    (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
      quarterRound (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) := by
  simp only [execAll, instrs, exec, State.setReg, State.setNZ, State.reg, State.pc,
    LowReg.toReg, quarterRound]
  simp (config := { decide := true }) only [addWithCarry_fst, rorC_eq_rotl, Fin.isValue,
    ite_true, ite_false, Prod.mk.injEq]
  -- Remaining differences are `⟨↑(3 : Fin 8), _⟩` versus `(3 : Fin 16)`, equal by definition.
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Frame: PC advances past the fragment; r5-r14 and memory are unchanged. -/
theorem exec_all_frame (s : State) :
    let s' := execAll instrs s
    s'.pc = s.pc + 32#32 ∧
    (∀ r : Reg, 5 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) ∧
    s'.mem = s.mem := by
  refine ⟨by rw [execAll_pc]; rfl, ?_, execAll_mem instrs s (by decide)⟩
  intro r h5 h14
  apply execAll_regs_other instrs s r (by omega)
  have hdst : ∀ i ∈ instrs, i.dst ≤ 4 := by decide
  intro i hi
  have := hdst i hi
  omega

/-- Combined contract for the linked fragment. Started at its link address with
`a, b, c, d` in r0-r3, the bytes execute 16 instructions without fault, along a
trace fixed independently of all data, and finish with RFC 8439
`quarterRound a b c d` in r0-r3, PC at the end of the fragment, and r5-r14 and
memory unchanged. -/
theorem qr_spec (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base) :
    ∃ s', run code 16 s = .ok (s', execTrace instrs s) ∧
      (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
        quarterRound (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) ∧
      s'.pc = BitVec.ofNat 32 (code.base + 32) ∧
      (∀ r : Reg, 5 ≤ r.val → r.val ≤ 14 → s'.regs r = s.regs r) ∧
      s'.mem = s.mem := by
  obtain ⟨hpc', hregs, hmem⟩ := exec_all_frame s
  refine ⟨execAll instrs s, run_eq s hpc, exec_all_regs s, ?_, hregs, hmem⟩
  rw [hpc', hpc]
  decide

/-- End-to-end check of the theorem against the RFC 8439 §2.1.1 vector. -/
example (s : State) (hpc : s.pc = BitVec.ofNat 32 code.base)
    (h0 : s.regs 0 = 0x11111111#32) (h1 : s.regs 1 = 0x01020304#32)
    (h2 : s.regs 2 = 0x9b8d6f43#32) (h3 : s.regs 3 = 0x01234567#32) :
    ∃ s', run code 16 s = .ok (s', execTrace instrs s) ∧
      (s'.regs 0, s'.regs 1, s'.regs 2, s'.regs 3) =
        (0xea2a92f4#32, 0xcb1cf8ce#32, 0x4581472e#32, 0x5881c4bb#32) := by
  obtain ⟨s', hrun, hqr, -⟩ := qr_spec s hpc
  exact ⟨s', hrun, by rw [hqr, h0, h1, h2, h3]; exact Spec.ChaCha20.quarterRound_rfc8439_2_1_1⟩

end M0Crypto.Proofs.ChaCha20QuarterRound
