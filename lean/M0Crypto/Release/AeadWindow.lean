import M0Crypto.Release.AeadCompose
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The AEAD stack window at return

The 320 bytes `[sp0 - 320, sp0)` from `X = A - 176` (`A = sp0 - 144`), as 80 words: the callee
frames (words 0-34) zero, the nine words a callee saved last (35-43), the nonce pointer and counter
(44, 45), `CTX`/`BLK` (46-69) zero, the saved arguments `out`, `tag`, `in`, `len` (70-73), the
alignment word (74, unchanged from entry) and the caller's r4-r7 and LR (75-79). `window_eq` turns
these word facts into the byte list `winBytes`; `encWindow` and `decWindow` are the windows of the
two functions, from the entry registers, the nonce pointer and (decrypt) the verdict.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-- Byte `j` of the little-endian word `w`. -/
def byteOf (w : Word) (j : Nat) : BitVec 8 := w.extractLsb' (8 * j) 8

/-- Word `i` of the window from the entry registers `R`, the nonce pointer, the counter word and
the nine words `low9` at indices 35-43. Word 74 is taken from the entry bytes (`winBytes`). -/
def winWord (R : Reg → Word) (nonce ctr : Word) (low9 : List Word) (i : Nat) : Word :=
  if i < 35 then 0#32
  else if i < 44 then low9.getD (i - 35) 0#32
  else if i = 44 then nonce
  else if i = 45 then ctr
  else if i < 70 then 0#32
  else [R 0, R 1, R 2, R 3, 0#32, R 4, R 5, R 6, R 7, R 14].getD (i - 70) 0#32

/-- The window bytes; `b` is the window at entry, used only for word 74. -/
def winBytes (R : Reg → Word) (nonce ctr : Word) (low9 : List Word) (b : List (BitVec 8)) :
    List (BitVec 8) :=
  (List.range 320).map fun o =>
    if o / 4 = 74 then b.getD o 0#8 else byteOf (winWord R nonce ctr low9 (o / 4)) (o % 4)

/-- Words 35-43 after encryption: the caller's r8-r11 (pushed by the last `blocks` call), then
what `finish` pushed: r4 at the last partial ciphertext block, `len`, `len % 16`, the caller's r7
and the return address. -/
def encLow9 (R : Reg → Word) : List Word :=
  [R 8, R 9, R 10, R 11,
    if (R 3).toNat % 16 = 0 then R 0 else R 0 + BitVec.ofNat 32 (16 * ((R 3).toNat / 16)),
    R 3, BitVec.ofNat 32 ((R 3).toNat % 16), R 7,
    (R 15 - BitVec.ofNat 32 encOff + BitVec.ofNat 32 (encFinEAt + seqSize (finArgs false) + blSize)) ||| 1#32]

/-- Words 35-43 after decryption. Rejected: as `encLow9`, over `in`. Accepted: what the ChaCha20
call pushed, the compare loop's final index 16, 0, `len % 16`, r7 and its return address. -/
def decLow9 (R : Reg → Word) (ok : Bool) : List Word :=
  if ok then
    [R 8, R 9, R 10, R 11, 16#32, 0#32, BitVec.ofNat 32 ((R 3).toNat % 16), R 7,
      (R 15 - BitVec.ofNat 32 decOff + BitVec.ofNat 32 (decCryptAt + cryptEnd)) ||| 1#32]
  else
    [R 8, R 9, R 10, R 11,
      if (R 3).toNat % 16 = 0 then R 2 else R 2 + BitVec.ofNat 32 (16 * ((R 3).toNat / 16)),
      R 3, BitVec.ofNat 32 ((R 3).toNat % 16), R 7,
      (R 15 - BitVec.ofNat 32 decOff + BitVec.ofNat 32 (decFinDAt + seqSize (finArgs true) + blSize)) ||| 1#32]

def encWindow (R : Reg → Word) (nonce : Word) (b : List (BitVec 8)) : List (BitVec 8) :=
  winBytes R nonce 1#32 (encLow9 R) b

def decWindow (R : Reg → Word) (nonce : Word) (ok : Bool) (b : List (BitVec 8)) : List (BitVec 8) :=
  winBytes R nonce (if ok then 1#32 else 0#32) (decLow9 R ok) b

/-- The window words a path sets below `A` and at `A`, `A + 4`: the zero callee frames, the
nine words `low9`, the nonce pointer and the counter word. -/
structure LowWin (c : ACall) (ctr : Word) (low9 : List Word) (m : Mem) : Prop where
  low : ∀ o < 140, m (c.A - 176#32 + BitVec.ofNat 32 o) = 0#8
  saved : ∀ i < 9, read32 m (c.A - 176#32 + BitVec.ofNat 32 (140 + 4 * i)) = low9.getD i 0#32
  nonce : read32 m c.A = c.nonce
  ctr : read32 m (c.A + 4#32) = ctr

/-! ## Bytes and words -/

theorem byte_split (m : Mem) (a : Word) (o : Nat) :
    m (a + BitVec.ofNat 32 o) = byteOf (read32 m (a + BitVec.ofNat 32 (4 * (o / 4)))) (o % 4) := by
  have e : a + BitVec.ofNat 32 o = a + BitVec.ofNat 32 (4 * (o / 4)) + BitVec.ofNat 32 (o % 4) := by
    rw [ofNat_add_assoc]; congr 2; omega
  rw [e, Frame.byte_of_read32 m _ _ (Nat.mod_lt _ (by decide))]; rfl

theorem read32_zero {m : Mem} {a : Word} (h : ∀ k < 4, m (a + BitVec.ofNat 32 k) = 0#8) :
    read32 m a = 0#32 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide)
  have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  rw [show a + BitVec.ofNat 32 0 = a from BitVec.add_zero a] at h0
  simp only [read32]
  rw [show a + 3#32 = a + BitVec.ofNat 32 3 from rfl, show a + 2#32 = a + BitVec.ofNat 32 2 from rfl,
    show a + 1#32 = a + BitVec.ofNat 32 1 from rfl, h0, h1, h2, h3]
  rfl

theorem bytesAt_map (m : Mem) (a : Word) (n : Nat) :
    Ctx.bytesAt m a n = (List.range n).map fun o => m (a + BitVec.ofNat 32 o) := by
  apply List.ext_getElem?
  intro o
  by_cases ho : o < n
  · rw [Frame.bytesAt_get _ _ _ _ ho, List.getElem?_map, List.getElem?_range ho]; rfl
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega), List.getElem?_eq_none (by simp; omega)]

theorem X_eq (c : ACall) : c.sp0 - 320#32 = c.A - 176#32 := by
  simp only [ACall.A]; bv_omega

theorem X_A (A : Word) (k : Nat) : A - 176#32 + BitVec.ofNat 32 (176 + k) = A + BitVec.ofNat 32 k := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem X_64 (A : Word) (k : Nat) : A - 176#32 + BitVec.ofNat 32 (112 + k) = A - 64#32 + BitVec.ofNat 32 k := by
  bv_omega

theorem X_slot64 (A : Word) (j : Nat) :
    A - 176#32 + BitVec.ofNat 32 (140 + 4 * j) = slot (A - 64#32) (7 + j) := by
  simp only [slot]; bv_omega

theorem X_slot20 (A : Word) (j : Nat) :
    A - 176#32 + BitVec.ofNat 32 (140 + 4 * (4 + j)) = slot (A - 20#32) j := by
  simp only [slot]; bv_omega

/-! ## Window offsets missing the phases' writes -/

section
variable {c : ACall} (hv : AValid c)
include hv

theorem clearWr_X (o : Nat) (h : o < 184 ∨ (280 ≤ o ∧ o < 320)) :
    ¬ ClearWr c.A (c.A - 176#32 + BitVec.ofNat 32 o) := by
  have := hv.A_lo; have := hv.A_hi
  rintro ⟨q, hq, e⟩
  bv_omega

theorem macWr_X (o : Nat) (h : o < 112 ∨ (176 ≤ o ∧ o < 184)) :
    ¬ MacWr c.A (c.A - 176#32 + BitVec.ofNat 32 o) := by
  have := hv.A_lo; have := hv.A_hi
  rintro (⟨q, hq, e⟩ | ⟨q, hq, e⟩ | ⟨q, hq, e⟩) <;> bv_omega

theorem finishWr_X (hb : ABuf c) (dec : Bool) (o : Nat) (h : o < 156 ∨ (176 ≤ o ∧ o < 184)) :
    ¬ FinishWr c.A (if dec then c.A + 72#32 else c.tag) (c.A - 176#32 + BitVec.ofNat 32 o) := by
  have := hv.A_lo; have := hv.A_hi
  rintro (⟨q, hq, e⟩ | ⟨q, hq, e⟩)
  · bv_omega
  · cases dec
    · have hd := hb.tagS
      rw [X_eq] at hd
      exact ne_of_disj hd.1 hd.2.1 hd.2.2 hq (show o < 336 by omega) (by simpa using e.symm)
    · simp only [ite_true] at e
      bv_omega

/-- The window, from the facts each phase leaves: `m'` before `CLEAR_FRAME`, `m` after it. -/
theorem window_eq {e : Nat} {s0 : State} (he : AEntry c e s0) {m m' : Mem} (ctr : Word) (low9 : List Word)
    (hf : ∀ y, ¬ ClearWr c.A y → m y = m' y) (hz : ∀ o < 96, m (c.A + BitVec.ofNat 32 (8 + o)) = 0#8)
    (hlow : ∀ o < 140, m' (c.A - 176#32 + BitVec.ofNat 32 o) = 0#8)
    (hsv : ∀ i < 9, read32 m' (c.A - 176#32 + BitVec.ofNat 32 (140 + 4 * i)) = low9.getD i 0#32)
    (hn : read32 m' c.A = c.nonce) (hc : read32 m' (c.A + 4#32) = ctr) (hh : Hi c m') :
    Ctx.bytesAt m (c.sp0 - 320#32) 320 =
      winBytes c.regs0 c.nonce ctr low9 (Ctx.bytesAt c.m0 (c.sp0 - 320#32) 320) := by
  have hA := hv.A_lo; have hA' := hv.A_hi
  rw [X_eq]
  generalize hX : c.A - 176#32 = X at hlow hsv
  have XA : ∀ k, X + BitVec.ofNat 32 (176 + k) = c.A + BitVec.ofNat 32 k := fun k => by rw [← hX]; exact X_A c.A k
  have hfX : ∀ o, (o < 184 ∨ (280 ≤ o ∧ o < 320)) → m (X + BitVec.ofNat 32 o) = m' (X + BitVec.ofNat 32 o) :=
    fun o ho => hf _ (by rw [← hX]; exact clearWr_X hv o ho)
  -- reads of `m` agree with `m'` outside `CLEAR_FRAME`
  have rX : ∀ w, (w < 46 ∨ (70 ≤ w ∧ w < 80)) →
      read32 m (X + BitVec.ofNat 32 (4 * w)) = read32 m' (X + BitVec.ofNat 32 (4 * w)) := fun w hw =>
    read32_congr (fun k hk => by rw [ofNat_add_assoc, hfX _ (by omega)])
  have word : ∀ w < 80, w ≠ 74 → read32 m (X + BitVec.ofNat 32 (4 * w)) = winWord c.regs0 c.nonce ctr low9 w := by
    intro w hw h74
    by_cases w35 : w < 35
    · rw [rX w (by omega), read32_zero (fun k hk => by rw [ofNat_add_assoc]; exact hlow _ (by omega))]
      simp [winWord, w35]
    by_cases w44 : w < 44
    · rw [rX w (by omega), show 4 * w = 140 + 4 * (w - 35) by omega, hsv _ (by omega)]
      simp [winWord, w35, w44]
    by_cases w45 : w < 46
    · rw [rX w (by omega)]
      rcases (by omega : w = 44 ∨ w = 45) with rfl | rfl
      · rw [show 4 * 44 = 176 + 0 by rfl, XA, BitVec.add_zero, hn]; simp [winWord]
      · rw [show 4 * 45 = 176 + 4 by rfl, XA, hc]; simp [winWord]
    by_cases w70 : w < 70
    · rw [read32_zero (fun k hk => by
        rw [ofNat_add_assoc, show 4 * w + k = 176 + (8 + (4 * w + k - 184)) by omega, XA]
        exact hz _ (by omega))]
      have h44 : w ≠ 44 := by omega
      have h45 : w ≠ 45 := by omega
      simp [winWord, w35, w44, w70, h44, h45]
    rw [rX w (by omega), show 4 * w = 176 + (4 * w - 176) by omega, XA]
    have hs := hh.saved
    simp only [ACall.saved] at hs
    rcases (by omega : w = 70 ∨ w = 71 ∨ w = 72 ∨ w = 73 ∨ w = 75 ∨ w = 76 ∨ w = 77 ∨ w = 78 ∨ w = 79) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show 4 * 70 - 176 = 104 by rfl]; simp [winWord, hh.out, he.r0]
    · rw [show 4 * 71 - 176 = 108 by rfl]; simp [winWord, hh.tag, he.r1]
    · rw [show 4 * 72 - 176 = 112 by rfl]; simp [winWord, hh.inp, he.r2]
    · rw [show 4 * 73 - 176 = 116 by rfl]; simp [winWord, hh.len, he.r3]
    · have := hs 0 (by decide); simp at this; simp [winWord, this]
    · have := hs 1 (by decide); simp at this; simp [winWord, this]
    · have := hs 2 (by decide); simp at this; simp [winWord, this]
    · have := hs 3 (by decide); simp at this; simp [winWord, this]
    · have := hs 4 (by decide); simp at this; simp [winWord, this]
  have gap : ∀ o, o / 4 = 74 →
      read32 m (X + BitVec.ofNat 32 (4 * (o / 4))) = read32 c.m0 (X + BitVec.ofNat 32 (4 * (o / 4))) := by
    intro o h
    rw [h, rX 74 (by omega), show 4 * 74 = 176 + 120 by rfl, XA]; exact hh.gap
  rw [bytesAt_map, bytesAt_map, winBytes]
  apply List.map_congr_left
  intro o ho
  simp only [List.mem_range] at ho
  rw [byte_split m X o]
  split
  · rename_i h
    rw [gap o h, ← byte_split c.m0 X o]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ho]; rfl
  · rename_i h
    rw [word _ (by omega) h]

end

end M0Crypto.Release.Aead
