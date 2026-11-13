import M0Crypto.Release.Blake2sUpdateBytes
import M0Crypto.Release.ReachPc
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_update`: entry, loop invariant and helper facts -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2sInit (disj_ne)
open M0Crypto.Release.Blake2sCode (SiteAt)

abbrev SState := M0Crypto.Spec.Blake2s.State

/-- The entry state of `m0c_blake2s_update(c = r0, p = r1, n = r2)`: a context holding stream `st`. -/
structure UpdateEntry (base : Word) (s : State) (st : SState) : Prop where
  base4 : base.toNat % 4 = 0
  pc : s.pc = base + BitVec.ofNat 32 uStart
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : STREAM_FRAME ≤ (s.regs 13).toNat
  c4 : (s.regs 0).toNat % 4 = 0
  lr : (s.regs 14).getLsbD 0 = true
  ctx : Ctx s.mem (s.regs 0) st
  cnt : st.count + st.pending.length + (s.regs 2).toNat < 2 ^ 64
  codeC : Disj base Artifacts.Release.size (s.regs 0) 112
  codeF : Disj base Artifacts.Release.size (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME
  cF : Disj (s.regs 0) 112 (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME
  pC : Disj (s.regs 1) (s.regs 2).toNat (s.regs 0) 112
  pF : Disj (s.regs 1) (s.regs 2).toNat (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME

/-- Everything `update` may write: the context and its own frame together with the callee frames. -/
def WrU (s : State) : Word → Prop := fun y =>
  (∃ o < STREAM_FRAME, y = s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 o) ∨ (∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o)

theorem wr_frame (s : State) (o : Nat) (h : o < STREAM_FRAME) : WrU s (s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 o) :=
  Or.inl ⟨o, h, rfl⟩
theorem wr_ctx (s : State) (o : Nat) (h : o < 112) : WrU s (s.regs 0 + BitVec.ofNat 32 o) :=
  Or.inr ⟨o, h, rfl⟩

/-- The context bytes. -/
def CtxR (s : State) : Word → Prop := fun y => ∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o

/-- The write bound of `update` by program counter: the context or the frame, and the context alone
at the untracked store sites (so that those stores never touch the frame). -/
def WU (base : Word) (s : State) (pc y : Word) : Prop :=
  WrU s y ∧ (SiteAt base pc → CtxR s y)

theorem wu_ctx {base : Word} (s : State) {pc : Word} (o : Nat) (h : o < 112) :
    WU base s pc (s.regs 0 + BitVec.ofNat 32 o) :=
  ⟨wr_ctx s o h, fun _ => ⟨o, h, rfl⟩⟩

theorem wu_frame {base : Word} (s : State) {pc : Word} (hns : ¬ SiteAt base pc) (o : Nat) (h : o < STREAM_FRAME) :
    WU base s pc (s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 o) :=
  ⟨wr_frame s o h, fun hs => absurd hs hns⟩

theorem WU.wrU {base : Word} {s : State} {pc y : Word} (h : WU base s pc y) : WrU s y := h.1

def nn (s : State) : Nat := (s.regs 2).toNat
/-- The bytes of the input. -/
def LL (s : State) : List (BitVec 8) := bytesAt s.mem (s.regs 1) (nn s)
def fb (s : State) : Word := s.regs 13 - STREAM_FRAME_W

/-- The bytes `update` may read through its caller's pointers: the 112-byte context window at `r0`
and the `n` input bytes at `r1`. -/
def UR (s : State) (y : Word) : Prop :=
  (∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o) ∨ (∃ o < nn s, y = s.regs 1 + BitVec.ofNat 32 o)

theorem UR.ctx_at {s : State} {a : Word} {c k : Nat} (h : a = s.regs 0 + BitVec.ofNat 32 c)
    (hk : c + k < 112) : UR s (a + BitVec.ofNat 32 k) :=
  Or.inl ⟨c + k, hk, by rw [h, ofNat_add_assoc]⟩

theorem UR.data_at {s : State} {a : Word} {c k : Nat} (h : a = s.regs 1 + BitVec.ofNat 32 c)
    (hk : c + k < nn s) : UR s (a + BitVec.ofNat 32 k) :=
  Or.inr ⟨c + k, hk, by rw [h, ofNat_add_assoc]⟩

/-- Memory right after `push {r4-r7,lr}` (the entry state's stack with the five saved words). -/
def pm (s : State) : Mem :=
  M0Crypto.Thumb.storeWords s.mem (s.regs 13 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14]

/-- Memory outside the context and the loop's part of the frame is as the prologue left it. -/
def Ag (s t : State) : Prop :=
  ∀ y, (∀ o < 112, y ≠ s.regs 0 + BitVec.ofNat 32 o) → (∀ o < STREAM_LOCALS, y ≠ fb s + BitVec.ofNat 32 o) →
    t.mem y = pm s y

theorem pm_eq (s : State) (y : Word) (h : ∀ o < STREAM_FRAME, y ≠ fb s + BitVec.ofNat 32 o) : pm s y = s.mem y := by
  unfold pm
  apply M0Crypto.Thumb.storeWords_other
  intro i k hi hk heq
  simp at hi
  have h20 : s.regs 13 - 20#32 = fb s + BitVec.ofNat 32 STREAM_LOCALS := by unfold fb; bv_omega
  rw [h20, ofNat_add_assoc, ofNat_add_assoc] at heq
  exact h (STREAM_LOCALS + 4 * i + k) (by omega) (by rw [heq, Nat.add_assoc])

theorem Ag.eq {s t : State} (h : Ag s t) {y : Word} (h1 : ∀ o < 112, y ≠ s.regs 0 + BitVec.ofNat 32 o)
    (h2 : ∀ o < STREAM_FRAME, y ≠ fb s + BitVec.ofNat 32 o) : t.mem y = s.mem y :=
  (h y h1 (fun o ho => h2 o (by omega))).trans (pm_eq s y h2)

theorem Ag.trans {s t u : State} (h : Ag s t)
    (h2 : ∀ y, (∀ o < 112, y ≠ s.regs 0 + BitVec.ofNat 32 o) → (∀ o < STREAM_LOCALS, y ≠ fb s + BitVec.ofNat 32 o) →
      u.mem y = t.mem y) : Ag s u :=
  fun y h1 h3 => (h2 y h1 h3).trans (h y h1 h3)

theorem code_ag {base : Word} {s t : State} (hc : CodeAt s.mem base B) (h : Ag s t)
    (hC : Disj base Artifacts.Release.size (s.regs 0) 112)
    (hF : Disj base Artifacts.Release.size (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME) : CodeAt t.mem base B := by
  intro i hi
  rw [h.eq (fun o ho he => disj_ne hC (by rwa [B_len] at hi) ho he)
    (fun o ho he => disj_ne hF (by rwa [B_len] at hi) ho he)]
  exact hc i hi

theorem src_ag {s t : State} (h : Ag s t) (pC : Disj (s.regs 1) (nn s) (s.regs 0) 112)
    (pF : Disj (s.regs 1) (nn s) (s.regs 13 - STREAM_FRAME_W) STREAM_FRAME) {i : Nat} (hi : i < nn s) :
    t.mem (s.regs 1 + BitVec.ofNat 32 i) = s.mem (s.regs 1 + BitVec.ofNat 32 i) :=
  h.eq (fun o ho he => disj_ne pC hi ho he) (fun o ho he => disj_ne pF hi ho he)

theorem ctx_cnt {m : Mem} {c : Word} {st : SState} (h : CtxNU m c st) :
    (read32 m (c + 32#32)).toNat + 2 ^ 32 * (read32 m (c + 36#32)).toNat = st.count := by
  rw [h.clo, h.chi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := h.cnt
  omega

theorem lohi_of_tot (lo hi : Word) (N : Nat) (hN : N < 2 ^ 64) (h : lo.toNat + 2 ^ 32 * hi.toNat = N) :
    lo = BitVec.ofNat 32 N ∧ hi = BitVec.ofNat 32 (N / 2 ^ 32) := by
  have hl := lo.isLt
  have hh := hi.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega

/-- The loop invariant, with `k` input bytes consumed and `st` the stream the context now holds. -/
structure Inv (s : State) (st0 : SState) (t : State) (k : Nat) (st : SState) : Prop where
  r4 : t.regs 4 = s.regs 0
  r5 : t.regs 5 = s.regs 1 + BitVec.ofNat 32 k
  r6 : t.regs 6 = BitVec.ofNat 32 (nn s - k)
  r7 : t.regs 7 = BitVec.ofNat 32 st.pending.length
  r13 : t.regs 13 = s.regs 13 - 24#32
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → t.regs r = s.regs r
  kn : k ≤ nn s
  ctx : CtxNU t.mem (s.regs 0) st
  ag : Ag s t
  tot : st.count + st.pending.length + (nn s - k) = st0.count + st0.pending.length + nn s
  ab : M0Crypto.Spec.Blake2s.absorb st ((LL s).drop k) = M0Crypto.Spec.Blake2s.absorb st0 (LL s)

/-- A context byte at a constant offset `a + k` from a register equal to the context pointer. -/
theorem wu_ctx_w {base : Word} (s : State) {pc : Word} (c a : Word) (k : Nat) (hc : c = s.regs 0)
    (h : a.toNat + k < 112) : WU base s pc (c + a + BitVec.ofNat 32 k) := by
  have : c + a + BitVec.ofNat 32 k = s.regs 0 + BitVec.ofNat 32 (a.toNat + k) := by
    subst hc; bv_omega
  rw [this]; exact wu_ctx s _ h

/-- A frame byte at a constant offset from a register that equals `fb s + d`. -/
theorem wu_frame_w {base : Word} (s : State) {pc : Word} (hns : ¬ SiteAt base pc) (c a : Word) (d k : Nat)
    (hc : c + a = fb s + BitVec.ofNat 32 d) (h : d + k < STREAM_FRAME) :
    WU base s pc (c + a + BitVec.ofNat 32 k) := by
  have : c + a + BitVec.ofNat 32 k = s.regs 13 - STREAM_FRAME_W + BitVec.ofNat 32 (d + k) := by
    rw [hc]; unfold fb; bv_omega
  rw [this]; exact wu_frame s hns _ h

theorem wu_of_ctxR {base : Word} {s : State} {pc y : Word} (h : CtxR s y) : WU base s pc y := by
  obtain ⟨o, ho, rfl⟩ := h
  exact wu_ctx s o ho

/-- The bound of a call to compress, from the state `t` where the chain is the context and the
compression frame (136 bytes) sits at the loop's frame. -/
theorem wu_of_cwu {base : Word} {s t : State} {pc y : Word} (hfr : t.regs 13 - COMPRESS_FRAME_W = s.regs 13 - STREAM_FRAME_W)
    (r4 : t.regs 4 = s.regs 0) (h : ((∃ i < COMPRESS_FRAME, y = t.regs 13 - COMPRESS_FRAME_W + BitVec.ofNat 32 i) ∨
      (∃ i < 32, y = t.regs 4 + BitVec.ofNat 32 i)) ∧
      (SiteAt base pc → ∃ i < 32, y = t.regs 4 + BitVec.ofNat 32 i)) : WU base s pc y := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hs => ?_⟩
  · rcases h1 with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [hfr]; exact Or.inl ⟨i, by omega, rfl⟩
    · rw [r4]; exact Or.inr ⟨i, by omega, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := h2 hs
    rw [r4]; exact ⟨i, by omega, rfl⟩

end M0Crypto.Release.Blake2sUpdate
