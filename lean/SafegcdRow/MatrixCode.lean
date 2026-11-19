import SafegcdRow.Trace
import SafegcdRow.MatrixArtifact

namespace SafegcdRow.MatrixCode
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

def rounds : Nat := 14

def setup : List Instr := [.movImm 3 1, .movImm 4 1, .lslImm 4 4 16]

def iteration : List Instr :=
  [.dp .rsbs 5 2, .asrImm 5 5 31, .lslImm 7 1 31, .asrImm 7 7 31,
   .movHi 6 0, .dp .eors 6 5, .subReg 6 6 5, .dp .ands 6 7, .addReg 1 1 6,
   .movHi 6 3, .dp .eors 6 5, .subReg 6 6 5, .dp .ands 6 7, .addReg 4 4 6,
   .dp .ands 5 7, .movHi 6 1, .dp .ands 6 5, .addReg 0 0 6,
   .movHi 6 4, .dp .ands 6 5, .addReg 3 3 6, .dp .eors 2 5, .subReg 2 2 5, .addImm8 2 2,
   .asrImm 1 1 1, .lslImm 3 3 1]

def unpack : List Instr :=
  [.sxth 5 4, .subReg 6 4 5, .asrImm 6 6 16,
   .sxth 7 3, .subReg 4 3 7, .asrImm 4 4 16, .movHi 3 7]

def copies : Nat → List Instr
  | 0 => []
  | n+1 => copies n ++ iteration

def body : List Instr := setup ++ copies rounds ++ unpack

theorem body_at : seqAt MatrixArtifact.bytes 0 (body ++ [.bx 14]) = true := by
  decide +kernel

theorem body_falls : body.all Instr.falls = true := by decide +kernel

structure Words where
  f : Word
  g : Word
  delta : Word
  top : Word
  bot : Word

def capture (s : State) : Words := ⟨s.regs 0, s.regs 1, s.regs 2, s.regs 3, s.regs 4⟩

def init (f g delta : Word) : Words := ⟨f, g, delta, 1, 65536⟩

def advance (s : Words) : Words :=
  let dmask := (-s.delta).sshiftRight 31
  let omask := (s.g <<< 31).sshiftRight 31
  let g := s.g + (((s.f ^^^ dmask) - dmask) &&& omask)
  let bot := s.bot + (((s.top ^^^ dmask) - dmask) &&& omask)
  let swap := dmask &&& omask
  ⟨s.f + (g &&& swap), g.sshiftRight 1, (s.delta ^^^ swap) - swap + 2,
   (s.top + (bot &&& swap)) <<< 1, bot⟩

def run (s : Words) : Nat → Words
  | 0 => s
  | n+1 => advance (run s n)

theorem setup_effect (s : State) :
    capture (execAll setup s) = init (s.regs 0) (s.regs 1) (s.regs 2) := by
  unfold setup capture init
  row_simps

theorem iteration_effect (s : State) : capture (execAll iteration s) = advance (capture s) := by
  unfold iteration capture advance
  row_simps
  exact ⟨rfl, rfl⟩

theorem copies_effect (s : State) (n : Nat) :
    capture (execAll (copies n) s) = run (capture s) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copies, execAll_append, iteration_effect, ih]; rfl

def lowSigned (x : Word) : Word := (x <<< 16).sshiftRight 16
def highSigned (x : Word) : Word := (x - lowSigned x).sshiftRight 16

def output (s : State) : Word × Word × Word × Word × Word :=
  (s.regs 2, s.regs 3, s.regs 4, s.regs 5, s.regs 6)

def unpackWords (s : Words) : Word × Word × Word × Word × Word :=
  (s.delta, lowSigned s.top, highSigned s.top, lowSigned s.bot, highSigned s.bot)

theorem unpack_effect (s : State) :
    output (execAll unpack s) = unpackWords (capture s) := by
  unfold unpack output unpackWords capture lowSigned highSigned
  row_simps
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem body_effect (s : State) :
    output (execAll body s) = unpackWords (run (init (s.regs 0) (s.regs 1) (s.regs 2)) rounds) := by
  rw [body, execAll_append, unpack_effect, execAll_append, copies_effect, setup_effect]

private theorem output_set_pc (s : State) (a : Word) : output (s.setReg 15 a) = output s := by
  simp [output, State.setReg]

private theorem sp_set_pc (s : State) (a : Word) : (s.setReg 15 a).sp = s.regs 13 := by
  simp [State.sp, State.setReg]

private theorem pc_set_pc (s : State) (a : Word) : (s.setReg 15 a).pc = a := by
  simp [State.pc, State.setReg]

private theorem mem_set_pc (s : State) (a : Word) : (s.setReg 15 a).mem = s.mem := rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 3000000 in
theorem run_matrix {bytes : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : bytes.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt bytes off (body ++ [.bx 14]) = true)
    (hr : (s.regs 14).getLsbD 0 = true) :
    ∃ t, runH bytes base (body.length + 1) s =
      .ok (t, annotate s.pc body [] ++ [⟨nextPC s.pc body, .bx 14, []⟩]) ∧
      output t = unpackWords (run (init (s.regs 0) (s.regs 1) (s.regs 2)) rounds) ∧
      t.mem = s.mem ∧ t.sp = s.sp ∧ t.pc = (s.regs 14 &&& ~~~1#32) := by
  let u := execAll body s
  have keeps (r : M0Crypto.Armv6M.Reg) (h : r = 13 ∨ r = 14) : u.regs r = s.regs r := by
    rcases h with rfl | rfl <;> exact execAll_regs_other _ _ _ (by decide) (by decide)
  have hall : alignedAll body s = true := by
    have hall (is : List Instr) (v : State) (h : is.all quiet = true) : alignedAll is v = true := by
      induction is generalizing v with
      | nil => rfl
      | cons i is ih =>
        simp only [List.all_cons, Bool.and_eq_true] at h
        have ha : i.accesses v = [] := by cases i <;> simp_all [quiet, Instr.accesses]
        simp [alignedAll, ha, ih _ h.2]
    exact hall _ _ (by decide)
  have he : (off + seqSize body) % 2 = 0 := by
    have hz : seqSize body % 2 = 0 := by decide +kernel
    omega
  have hR : (u.regs 14).getLsbD 0 = true := by rw [keeps 14 (.inr rfl), hr]
  have hrun := runH_leaf hb hlen hpc ho hat body_falls hall he hR
  dsimp only at hrun
  rw [quiet_trace _ _ body_falls (by decide), execAll_pc _ _ body_falls] at hrun
  let ret := u.regs 14 &&& ~~~1#32
  refine ⟨u.setReg 15 ret, hrun, ?_, ?_, ?_, ?_⟩
  · exact (output_set_pc u ret).trans (body_effect s)
  · exact (mem_set_pc u ret).trans (execAll_mem _ _ (by decide))
  · exact (sp_set_pc u ret).trans (keeps 13 (.inl rfl))
  · exact (pc_set_pc u ret).trans (congrArg (fun x => x &&& ~~~1#32) (keeps 14 (.inr rfl)))

end SafegcdRow.MatrixCode
