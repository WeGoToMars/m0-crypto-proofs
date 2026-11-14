import M0Crypto.Release.Blake2sUpdateBytes
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false

/-!
# `update`: what the call leaves in its stack window

Below its own five saved words, `update` lends 140 bytes to its callees: `compress`'s frame (100
bytes of locals, then `r8`-`r11`, then `r4`-`r7` and `lr`), and the stacked `f0` slot above it.
`copy` uses only the 20 bytes of `r4`-`r7` and `lr`. What the window holds at return depends on
which calls happened, which the public inputs decide. `UG` records it: whether `compress` ran
(`cmp`) and the five words the last callee saved (`last`). `winW` turns a `UG` into the 35 window
words (`none`: as at entry), and `WinSem` says memory holds them.

`Fut a k u g` is the record at return, computed from the loop state (`k` input bytes consumed, `u`
pending) and the record now, in closed form from the public inputs `a` only. The loop keeps
`Fut a k u g` constant (`fut_flush`, `fut_direct`, `fut_take`), and at the end
(`fut_done`) it is the record itself, so the record at return is `Fut a 0 used0 UG.init`.
-/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStream (bytesAt bytesAt_length)
open M0Crypto.Release.Frame (read32_congr)
open M0Crypto.Release.Blake2sFinal (byteOf)

def nn (s : State) : Nat := (s.regs 2).toNat
def fb (s : State) : Word := s.regs 13 - STREAM_FRAME_W

/-- The link base of a call entered at `update`'s first instruction. -/
def baseOf (s : State) : Word := s.regs 15 - BitVec.ofNat 32 uStart

/-- The public inputs that decide the window: base, context, input pointer and length. -/
structure UArgs where
  base : Word
  ctx : Word
  inp : Word
  n : Nat

/-- The public inputs, from the entry registers. -/
def uargsR (R : Reg → Word) : UArgs := ⟨R 15 - BitVec.ofNat 32 uStart, R 0, R 1, (R 2).toNat⟩

def uargs (s : State) : UArgs := uargsR s.regs

/-- The return address a `bl` at `off` leaves in `lr`. -/
def retAt (base : Word) (off : Nat) : Word := (base + BitVec.ofNat 32 (off + 4)) ||| 1#32

/-- The five words a callee's `push {r4-r7, lr}` saves: context, input position, bytes left,
pending count, and the return address after the `bl` at `off`. -/
def rec5 (a : UArgs) (k left used off : Nat) : List Word :=
  [a.ctx, a.inp + BitVec.ofNat 32 k, BitVec.ofNat 32 left, BitVec.ofNat 32 used, retAt a.base off]

/-- What the calls so far left in the window. -/
structure UG where
  cmp : Bool
  last : Option (List Word)

def UG.init : UG := ⟨false, none⟩

/-- Pending bytes after the input is absorbed, when the total exceeds a block. -/
def lastLen (k u n : Nat) : Nat := (u + (n - k) - 1) % 64 + 1

/-- Where the buffer is next empty: now if it is empty or full, else after it fills. -/
def k0 (k u : Nat) : Nat := if u = 0 ∨ u = 64 then k else k + (64 - u)

/-- Whether whole blocks are compressed straight from the input once the buffer is empty. -/
def Dir (a : UArgs) (k u : Nat) : Prop := 64 < a.n - k0 k u ∧ (a.inp.toNat + k0 k u) % 4 = 0

instance (a : UArgs) (k u : Nat) : Decidable (Dir a k u) := by unfold Dir; infer_instance

/-- The words the last callee saves, when more than a block remains. -/
def lastRec (a : UArgs) (k u : Nat) : List Word :=
  if 8 ≤ lastLen k u a.n then rec5 a a.n 0 (lastLen k u a.n) oCopyBl
  else if Dir a k u then rec5 a (a.n - lastLen k u a.n - 64) (lastLen k u a.n + 64) 0 oDirectBl
  else rec5 a (a.n - lastLen k u a.n) (lastLen k u a.n) 64 oFlushBl

/-- The record at return, from `k` bytes consumed and `u` pending, with record `g` now. -/
def Fut (a : UArgs) (k u : Nat) (g : UG) : UG :=
  if a.n ≤ k then g
  else if u + (a.n - k) ≤ 64 then
    (if 8 ≤ a.n - k then { g with last := some (rec5 a a.n 0 (u + (a.n - k)) oCopyBl) } else g)
  else ⟨true, some (lastRec a k u)⟩

theorem fut_done {a : UArgs} {k u : Nat} (g : UG) (h : a.n ≤ k) : Fut a k u g = g := by
  simp [Fut, h]

theorem rec5_congr {a : UArgs} {k left used off k' left' used' : Nat} (h1 : k = k') (h2 : left = left')
    (h3 : used = used') : rec5 a k left used off = rec5 a k' left' used' off := by
  subst h1; subst h2; subst h3; rfl

/-- A flush: the full buffer is compressed with input remaining. -/
theorem fut_flush {a : UArgs} {k : Nat} (g : UG) (hk : k < a.n) :
    Fut a k 64 g = Fut a k 0 ⟨true, some (rec5 a k (a.n - k) 64 oFlushBl)⟩ := by
  have hL : lastLen k 64 a.n = lastLen k 0 a.n ∨ a.n - k ≤ 64 := by
    unfold lastLen; omega
  unfold Fut
  simp only [show ¬ a.n ≤ k by omega, ite_false, show ¬ 64 + (a.n - k) ≤ 64 by omega]
  by_cases hs : 0 + (a.n - k) ≤ 64
  · have hU : lastLen k 64 a.n = a.n - k := by unfold lastLen; omega
    simp only [hs, ite_true]
    unfold lastRec
    by_cases h8 : 8 ≤ a.n - k
    · simp only [h8, ite_true, hU]
      exact congrArg _ (congrArg _ (rec5_congr rfl rfl (by omega)))
    · have hD : ¬ Dir a k 64 := by unfold Dir k0; simp; omega
      simp only [h8, ite_false, hU, hD]
      exact congrArg _ (congrArg _ (rec5_congr (by omega) rfl rfl))
  · have hU : lastLen k 64 a.n = lastLen k 0 a.n := by unfold lastLen; omega
    simp only [hs, ite_false]
    unfold lastRec
    have hD : Dir a k 64 ↔ Dir a k 0 := by unfold Dir k0; simp
    rw [hU]
    by_cases h8 : 8 ≤ lastLen k 0 a.n
    · simp only [h8, ite_true]
    · by_cases hd : Dir a k 0
      · simp only [h8, ite_false, hd, hD.mpr hd, ite_true]
      · simp only [h8, ite_false, hd, mt hD.mp hd]

/-- A block compressed straight from the input. -/
theorem fut_direct {a : UArgs} {k : Nat} (g : UG) (hk : 64 < a.n - k) (hal : (a.inp.toNat + k) % 4 = 0) :
    Fut a k 0 g = Fut a (k + 64) 0 ⟨true, some (rec5 a k (a.n - k) 0 oDirectBl)⟩ := by
  unfold Fut
  simp only [show ¬ a.n ≤ k by omega, ite_false, show ¬ 0 + (a.n - k) ≤ 64 by omega]
  have hDk : Dir a k 0 := by unfold Dir k0; simp; omega
  by_cases hs : 0 + (a.n - (k + 64)) ≤ 64
  · have hU : lastLen k 0 a.n = a.n - (k + 64) := by unfold lastLen; omega
    simp only [show ¬ a.n ≤ k + 64 by omega, hs, ite_true, ite_false]
    unfold lastRec
    by_cases h8 : 8 ≤ a.n - (k + 64)
    · simp only [h8, ite_true, hU]
      exact congrArg _ (congrArg _ (rec5_congr rfl rfl (by omega)))
    · simp only [h8, ite_false, hU, hDk, ite_true]
      exact congrArg _ (congrArg _ (rec5_congr (by omega) (by omega) rfl))
  · have hU : lastLen (k + 64) 0 a.n = lastLen k 0 a.n := by unfold lastLen; omega
    simp only [show ¬ a.n ≤ k + 64 by omega, hs, ite_false]
    unfold lastRec
    have hD : Dir a (k + 64) 0 := by unfold Dir k0; simp; omega
    rw [hU]
    by_cases h8 : 8 ≤ lastLen k 0 a.n
    · simp only [h8, ite_true]
    · simp only [h8, ite_false, hD, hDk, ite_true]

/-- One chunk of `tk` bytes appended to the buffer: `copy` (8 bytes or more) leaves its frame. -/
def TakeStep (a : UArgs) (k u tk : Nat) (g : UG) : UG :=
  if 8 ≤ tk then { g with last := some (rec5 a (k + tk) (a.n - (k + tk)) (u + tk) oCopyBl) } else g

theorem TakeStep.cmp (a : UArgs) (k u tk : Nat) (g : UG) : (TakeStep a k u tk g).cmp = g.cmp := by
  unfold TakeStep; split <;> rfl

/-- One chunk taken into the buffer, `tk` bytes, at the buffer step of the loop. -/
theorem fut_take {a : UArgs} {k u tk : Nat} (g : UG) (hu : u < 64) (hk : k < a.n)
    (hnd : ¬ (u = 0 ∧ 64 < a.n - k ∧ (a.inp.toNat + k) % 4 = 0))
    (h1 : 1 ≤ tk) (h2 : tk ≤ a.n - k) (h3 : u + tk ≤ 64) (h4 : tk = a.n - k ∨ u + tk = 64) :
    Fut a k u g = Fut a (k + tk) (u + tk) (TakeStep a k u tk g) := by
  unfold Fut TakeStep
  simp only [show ¬ a.n ≤ k by omega, ite_false]
  by_cases hs : u + (a.n - k) ≤ 64
  · have htk : tk = a.n - k := by omega
    subst htk
    simp only [hs, ite_true, show a.n ≤ k + (a.n - k) by omega]
    by_cases h8 : 8 ≤ a.n - k
    · simp only [h8, ite_true]
      exact congrArg _ (congrArg _ (rec5_congr (by omega) (by omega) rfl))
    · simp only [h8, ite_false]
  · have htk : u + tk = 64 := by omega
    have hU : lastLen (k + tk) (u + tk) a.n = lastLen k u a.n := by unfold lastLen; omega
    have hk0 : k0 (k + tk) (u + tk) = k0 k u ∨ (u = 0 ∧ ¬ (64 < a.n - k ∧ (a.inp.toNat + k) % 4 = 0)) := by
      unfold k0; by_cases h0 : u = 0
      · right; exact ⟨h0, fun h => hnd ⟨h0, h⟩⟩
      · left; simp [htk, h0, show u ≠ 64 by omega]; omega
    have hD : Dir a (k + tk) (u + tk) ↔ Dir a k u := by
      rcases hk0 with e | ⟨h0, hn⟩
      · unfold Dir; rw [e]
      · subst h0
        unfold Dir k0
        simp only [Nat.zero_add] at htk
        subst htk
        simp
        constructor
        · intro ⟨x, y⟩; exact absurd ⟨by omega, by omega⟩ hn
        · intro ⟨x, y⟩; exact absurd ⟨x, y⟩ hn
    simp only [hs, ite_false, show ¬ a.n ≤ k + tk by omega, show ¬ u + tk + (a.n - (k + tk)) ≤ 64 by omega]
    unfold lastRec
    rw [hU]
    by_cases h8 : 8 ≤ lastLen k u a.n
    · simp only [h8, ite_true]
    · by_cases hd : Dir a k u
      · simp only [h8, ite_false, hd, hD.mpr hd, ite_true]
      · simp only [h8, ite_false, hd, mt hD.mp hd]

/-! ## The window -/

/-- Word `i` of the 35 window words from `fb`: what the calls left there, or `none` (as at
entry). `pad` is the value of the stacked `f0` after a compression. -/
def winW (r8 r9 r10 r11 pad : Word) (g : UG) (i : Nat) : Option Word :=
  if i < LOCALS_WORDS then (if g.cmp then some 0#32 else none)
  else if i < LOCALS_WORDS + 4 then (if g.cmp then some ([r8, r9, r10, r11][i - LOCALS_WORDS]!) else none)
  else if i < LOCALS_WORDS + 9 then g.last.map (·[i - (LOCALS_WORDS + 4)]!)
  else if g.cmp then some pad else none

/-- Memory `m` holds window word `i` from `F` as `w` says, against entry memory `m0`. -/
def SlotOK (F : Word) (m0 m : Mem) (i : Nat) : Option Word → Prop
  | none => ∀ j < 4, m (F + BitVec.ofNat 32 (4 * i + j)) = m0 (F + BitVec.ofNat 32 (4 * i + j))
  | some v => read32 m (F + BitVec.ofNat 32 (4 * i)) = v

/-- The 35 window words below the saved registers hold what `g` says. -/
def WinSem (s : State) (pad : Word) (m : Mem) (g : UG) : Prop :=
  ∀ i < STREAM_LOCALS / 4, SlotOK (fb s) s.mem m i (winW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad g i)

/-- The window's bytes at return: the 35 words of `winW` (entry bytes `eb` where `none`), then
the five words `hiW` the function saved itself. -/
def resBytes (eb : List (BitVec 8)) (hiW : List Word) (r8 r9 r10 r11 pad : Word) (g : UG) :
    List (BitVec 8) :=
  (List.range STREAM_FRAME).map fun o =>
    if o / 4 < STREAM_LOCALS / 4 then
      match winW r8 r9 r10 r11 pad g (o / 4) with
      | none => eb[o]!
      | some w => byteOf w (o % 4)
    else byteOf (hiW[o / 4 - STREAM_LOCALS / 4]!) (o % 4)

theorem bytesAt_get (m : Mem) (p : Word) (n o : Nat) (h : o < n) :
    (bytesAt m p n)[o]! = m (p + BitVec.ofNat 32 o) := by
  unfold bytesAt
  rw [getElem!_pos _ o (by simpa using h)]
  simp

/-- Memory that holds the window words of `g` and the five saved words has the bytes of
`resBytes`. -/
theorem bytes_of_win {s : State} {pad : Word} {m : Mem} {g : UG} {hiW : List Word} (hw : WinSem s pad m g)
    (hhi : ∀ i < 5, read32 m (fb s + BitVec.ofNat 32 (STREAM_LOCALS + 4 * i)) = hiW[i]!) :
    bytesAt m (fb s) STREAM_FRAME =
      resBytes (bytesAt s.mem (fb s) STREAM_FRAME) hiW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad g := by
  unfold resBytes bytesAt
  apply List.map_congr_left
  intro o ho
  simp only [List.mem_range] at ho
  have ho4 : o = 4 * (o / 4) + o % 4 := by omega
  have hj : o % 4 < 4 := Nat.mod_lt _ (by decide)
  have hword : ∀ (w : Word), read32 m (fb s + BitVec.ofNat 32 (4 * (o / 4))) = w →
      m (fb s + BitVec.ofNat 32 o) = byteOf w (o % 4) := by
    intro w h
    rw [← h, byteOf, M0Crypto.Release.Blake2sCopy.read32_byte _ _ _ hj, BitVec.add_assoc, ← BitVec.ofNat_add,
      ← ho4]
  split
  · rename_i hlt
    have hs := hw (o / 4) hlt
    revert hs
    cases winW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad g (o / 4) with
    | none =>
      intro hs
      simp only [SlotOK] at hs
      have := hs (o % 4) hj
      rw [← ho4] at this
      rw [this]
      simp only
      rw [show (List.map (fun i => s.mem (fb s + BitVec.ofNat 32 i)) (List.range STREAM_FRAME))[o]! =
        (bytesAt s.mem (fb s) STREAM_FRAME)[o]! from rfl, bytesAt_get _ _ _ _ ho]
    | some w =>
      intro hs
      exact hword w hs
  · rename_i hge
    have hi : o / 4 - STREAM_LOCALS / 4 < 5 := by omega
    apply hword
    have := hhi (o / 4 - STREAM_LOCALS / 4) hi
    rw [show STREAM_LOCALS + 4 * (o / 4 - STREAM_LOCALS / 4) = 4 * (o / 4) by omega] at this
    exact this

/-- The window bytes and `r12` at return, from the entry registers `R`, the pending count `u0` and
the window bytes at entry `eb`. -/
def updWin (R : Reg → Word) (u0 : Nat) (eb : List (BitVec 8)) : List (BitVec 8) × Word :=
  let g := Fut (uargsR R) 0 u0 UG.init
  (resBytes eb [R 4, R 5, R 6, R 7, R 14] (R 8) (R 9) (R 10) (R 11) 0#32 g, if g.cmp then 0#32 else R 12)

/-! ## Window steps -/

theorem slotOK_congr {F : Word} {m0 m m' : Mem} {i : Nat} {w : Option Word} (h : SlotOK F m0 m i w)
    (hm : ∀ j < 4, m' (F + BitVec.ofNat 32 (4 * i + j)) = m (F + BitVec.ofNat 32 (4 * i + j))) :
    SlotOK F m0 m' i w := by
  cases w with
  | none =>
    simp only [SlotOK] at h ⊢
    intro j hj; rw [hm j hj]; exact h j hj
  | some v =>
    simp only [SlotOK] at h ⊢
    rw [← h]
    apply read32_congr
    intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm j hj

/-- Memory that agrees on the window keeps it. -/
theorem win_congr {s : State} {pad : Word} {m m' : Mem} {g : UG} (h : WinSem s pad m g)
    (hm : ∀ o < STREAM_LOCALS, m' (fb s + BitVec.ofNat 32 o) = m (fb s + BitVec.ofNat 32 o)) :
    WinSem s pad m' g :=
  fun i hi => slotOK_congr (h i hi) (fun j hj => hm _ (by omega))

/-- A call to `copy` replaces the five words of its frame. -/
theorem win_last {s : State} {pad : Word} {m m' : Mem} {g : UG} {L : List Word} (h : WinSem s pad m g)
    (hm : ∀ o < STREAM_LOCALS, (o < 4 * (LOCALS_WORDS + 4) ∨ 4 * (LOCALS_WORDS + 9) ≤ o) →
      m' (fb s + BitVec.ofNat 32 o) = m (fb s + BitVec.ofNat 32 o))
    (hL : ∀ i < 5, read32 m' (fb s + BitVec.ofNat 32 (4 * (LOCALS_WORDS + 4 + i))) = L[i]!) :
    WinSem s pad m' { g with last := some L } := by
  intro i hi
  by_cases hr : i < LOCALS_WORDS + 4 ∨ LOCALS_WORDS + 9 ≤ i
  · have he : winW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad { g with last := some L } i =
        winW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad g i := by
      unfold winW
      rcases hr with hr | hr
      · by_cases h25 : i < LOCALS_WORDS <;> simp [h25, hr]
      · simp [show ¬ i < LOCALS_WORDS by omega, show ¬ i < LOCALS_WORDS + 4 by omega,
          show ¬ i < LOCALS_WORDS + 9 by omega]
    rw [he]
    exact slotOK_congr (h i hi) (fun j hj => hm _ (by omega) (by omega))
  · have he : winW (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) pad { g with last := some L } i =
        some L[i - (LOCALS_WORDS + 4)]! := by
      unfold winW
      simp [show ¬ i < LOCALS_WORDS by omega, show ¬ i < LOCALS_WORDS + 4 by omega,
        show i < LOCALS_WORDS + 9 by omega]
    rw [he]
    have := hL (i - (LOCALS_WORDS + 4)) (by omega)
    rw [show LOCALS_WORDS + 4 + (i - (LOCALS_WORDS + 4)) = i by omega] at this
    exact this

/-- A call to `compress` from the loop (`sp` 24 bytes below entry) fills the whole window: zeroed
locals, the caller's `r8`-`r11`, the callee-saved words and a zero `f0`. -/
theorem win_nf {base : Word} {s t v : State} {o : Nat} (h13 : t.regs 13 = s.regs 13 - 24#32)
    (hhi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → t.regs r = s.regs r) (hv : NfPost base o t v) :
    WinSem s 0#32 v.mem ⟨true, some [t.regs 4, t.regs 5, t.regs 6, t.regs 7, retAt base o]⟩ := by
  have hF : ∀ n, M0Crypto.Armv6M.slot (t.regs 13 - COMPRESS_FRAME_W) n = fb s + BitVec.ofNat 32 (4 * n) := by
    intro n; unfold M0Crypto.Armv6M.slot fb; rw [h13]; congr 1; bv_omega
  have hw := hv.wipe
  have hsv := hv.saved
  have hlr := hv.savedLr
  simp only [hF] at hw hsv hlr
  have hpd : read32 v.mem (fb s + BitVec.ofNat 32 (4 * (LOCALS_WORDS + 9))) = 0#32 := by
    rw [← hv.pad, h13]; unfold fb; congr 1; bv_omega
  intro i hi
  by_cases h25 : i < LOCALS_WORDS
  · simp only [winW, h25, ite_true, SlotOK]
    exact hw i h25
  · have : i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsv 0 (by decide)).trans (hhi 8 (by decide) (by decide))
    · exact (hsv 1 (by decide)).trans (hhi 9 (by decide) (by decide))
    · exact (hsv 2 (by decide)).trans (hhi 10 (by decide) (by decide))
    · exact (hsv 3 (by decide)).trans (hhi 11 (by decide) (by decide))
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
    · exact hsv 6 (by decide)
    · exact hsv 7 (by decide)
    · exact hlr
    · exact hpd

/-! ## The loop's ghost -/

/-- Not the direct-block path: the buffer holds bytes, at most a block remains, or the input
position is not word-aligned. -/
def NoDir (s : State) (k u : Nat) : Prop := ¬ (u = 0 ∧ 64 < nn s - k ∧ ((s.regs 1).toNat + k) % 4 = 0)

/-- The window part of the loop invariant, with `u0` bytes pending at entry, `k` consumed and `u`
pending now: some record `g` is in memory and `r12`, and its future is the record at return. -/
def GI (s : State) (u0 : Nat) (t : State) (k u : Nat) : Prop :=
  ∃ g, WinSem s 0#32 t.mem g ∧ t.regs 12 = (if g.cmp then 0#32 else s.regs 12) ∧
    Fut (uargs s) k u g = Fut (uargs s) 0 u0 UG.init

theorem GI.of {s t v : State} {u0 k u : Nat} (h : GI s u0 t k u) (h12 : v.regs 12 = t.regs 12)
    (hm : v.mem = t.mem) : GI s u0 v k u := by
  obtain ⟨g, h1, h2, h3⟩ := h
  exact ⟨g, by rw [hm]; exact h1, by rw [h12]; exact h2, h3⟩

end M0Crypto.Release.Blake2sUpdate
