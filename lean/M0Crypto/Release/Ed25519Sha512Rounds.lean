import M0Crypto.Release.Ed25519Sha512Pairs

/-!
The message schedule and the rounds of `m0c_sha512_block` (`emit_block` in
`bench/ed25519/gen_sha512.py`) against FIPS 180-4 section 6.4.2 (`Spec.Sha512.compress`), on
64-bit words. `Ed25519Sha512Pairs` relates each 64-bit operation to the code's 32-bit pairs.

* `Wt`: the recurrence of step 1 as a function; `schedule_get`: the specification's array.
* The schedule is a 16-word circular buffer `buf`. `Window W p buf`: it holds `W_t` at
  `t mod 16` for the sixteen `t < p`. `schedStep_window`: one iteration `j = p mod 16` of macro
  `schedule`, `W[j] + σ0(W[j+1]) + W[j+9] + σ1(W[j+14])` (indices mod 16, the generator's
  addition order), moves the window from `p` to `p + 1`. `schedRun_window`: sixteen of them.
  `sched_index`, `group_index`: the masked byte offsets `(8j + 8a) & 0x78` and `(g << 6) & 64`.
* `slot r x`: the frame slot of variable `x` (`a = 0`, …, `h = 7`) in round `r` of a group,
  `(x − r) mod 8` as `round_body` renames them. `codeRound`: `round_body` (`T1` in the code's
  order, `e' = d + T1` into `d`'s slot, `a' = T2 + T1` into `h`'s slot). `codeRound_eq`: one
  code round is one specification round, read through the slots of the next round.
* `codeGroup`: one group of eight rounds; `codeGroup_eq`. `codeGroups`: the group loop with
  the schedule refreshed before groups 2, 4, 6, 8. `codeGroups_eq`: ten groups are the eighty
  rounds of `compress`, and `compress_code` adds `H`.
-/

namespace M0Crypto.Release.Ed25519Sha512Rounds

open M0Crypto.Spec.Sha512
open M0Crypto.Release.Ed25519Sha512Pairs (sched_order T1_order a_order)

/-! ## The schedule recurrence -/

/-- `W_t` of step 1 for the message words `M`. -/
def Wt (M : Nat → Word) (t : Nat) : Word :=
  if t < 16 then M t
  else sigma1 (Wt M (t - 2)) + Wt M (t - 7) + sigma0 (Wt M (t - 15)) + Wt M (t - 16)
termination_by t
decreasing_by all_goals omega

theorem Wt_ge (M : Nat → Word) {t : Nat} (ht : 16 ≤ t) :
    Wt M t = sigma1 (Wt M (t - 2)) + Wt M (t - 7) + sigma0 (Wt M (t - 15)) + Wt M (t - 16) := by
  rw [Wt, ite_eq_right (by omega)]

theorem get_push (A : Array Word) (x : Word) {t : Nat} (ht : t ≤ A.size) :
    (A.push x)[t]! = if t < A.size then A[t]! else x := by
  rw [getElem!_pos (A.push x) t (by simp; omega), Array.getElem_push]
  split
  · rename_i h; rw [getElem!_pos A t h]
  · rfl

/-- The specification's schedule holds `W_t` at every `t < 80`. -/
theorem schedule_get {M : Array Word} (hM : M.size = 16) {t : Nat} (ht : t < 80) :
    (schedule M)[t]! = Wt (fun i => M[i]!) t := by
  have key : ∀ m, m ≤ 64 →
      let A := (List.range' 16 m).foldl
        (fun W t => W.push (sigma1 W[t - 2]! + W[t - 7]! + sigma0 W[t - 15]! + W[t - 16]!)) M
      A.size = 16 + m ∧ ∀ t, t < 16 + m → A[t]! = Wt (fun i => M[i]!) t := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hM, fun t ht => ?_⟩
      rw [Wt, ite_eq_left (by omega)]; rfl
    | succ m ih =>
      intro hm
      obtain ⟨hs, hg⟩ := ih (by omega)
      simp only [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil] at hs hg ⊢
      refine ⟨by simp [hs]; omega, fun t ht => ?_⟩
      rw [get_push _ _ (by omega), hs]
      split
      · exact hg t (by omega)
      · rw [hg _ (by omega), hg _ (by omega), hg _ (by omega), hg _ (by omega),
          Wt_ge _ (show 16 ≤ t by omega), show 16 + 1 * m = t by omega]
  exact (key 64 (Nat.le_refl _)).2 t ht

/-! ## The circular buffer -/

/-- `f` with `x` at `i`. -/
def upd (f : Nat → Word) (i : Nat) (x : Word) : Nat → Word := fun j => if j = i then x else f j

/-- The buffer holds `W_t` at `t mod 16` for the sixteen `t < p`. -/
def Window (W : Nat → Word) (p : Nat) (buf : Nat → Word) : Prop :=
  ∀ t, t < p → p ≤ t + 16 → buf (t % 16) = W t

/-- Iteration `j` of the loop of macro `schedule`: `W[j] + σ0(W[j+1]) + W[j+9] + σ1(W[j+14])`
(indices mod 16), summed in this order and stored at `W[j]`. -/
def schedStep (buf : Nat → Word) (j : Nat) : Nat → Word :=
  upd buf j (buf j + sigma0 (buf ((j + 1) % 16)) + buf ((j + 9) % 16) + sigma1 (buf ((j + 14) % 16)))

/-- One schedule step computes `W_p` in place of `W_{p−16}`. -/
theorem schedStep_window (M : Nat → Word) {p : Nat} (hp : 16 ≤ p) {buf : Nat → Word}
    (hw : Window (Wt M) p buf) : Window (Wt M) (p + 1) (schedStep buf (p % 16)) := by
  intro t ht1 ht2
  unfold schedStep upd
  by_cases htp : t = p
  · subst htp
    rw [ite_eq_left rfl, show (t % 16 + 1) % 16 = (t - 15) % 16 by omega,
      show (t % 16 + 9) % 16 = (t - 7) % 16 by omega, show (t % 16 + 14) % 16 = (t - 2) % 16 by omega,
      show t % 16 = (t - 16) % 16 by omega, hw (t - 16) (by omega) (by omega),
      hw (t - 15) (by omega) (by omega), hw (t - 7) (by omega) (by omega),
      hw (t - 2) (by omega) (by omega), sched_order, Wt_ge M hp]
  · rw [ite_eq_right (by omega)]
    exact hw t (by omega) (by omega)

/-- Iterations `0 … m − 1` of the loop. -/
def schedRun (buf : Nat → Word) : Nat → Nat → Word
  | 0 => buf
  | m + 1 => schedStep (schedRun buf m) m

/-- The sixteen iterations of macro `schedule` move the window by sixteen. -/
theorem schedRun_window (M : Nat → Word) {p : Nat} (hp : 16 ≤ p) (h16 : p % 16 = 0)
    {buf : Nat → Word} (hw : Window (Wt M) p buf) : Window (Wt M) (p + 16) (schedRun buf 16) := by
  have : ∀ m, m ≤ 16 → Window (Wt M) (p + m) (schedRun buf m) := by
    intro m
    induction m with
    | zero => intro _; exact hw
    | succ m ih =>
      intro hm
      have := schedStep_window M (show 16 ≤ p + m by omega) (ih (by omega))
      rwa [show (p + m) % 16 = m by omega] at this
  exact this 16 (Nat.le_refl _)

/-- `mov r5, r7; adds r5, #8a; movs r4, #0x78; ands r5, r4` with `r7 = 8j`: the byte offset of
`W[(j + a) mod 16]` (`a = 1, 9, 14`; `a = 0` is `movs r5, #0x78; ands r5, r7`). -/
theorem sched_index (j a : Nat) (hj : j < 16) (ha : a < 16) :
    (BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (8 * a)) &&& 0x78#32 = BitVec.ofNat 32 (8 * ((j + a) % 16)) := by
  have h : ∀ x y : Fin 16, (BitVec.ofNat 32 (8 * x.val) + BitVec.ofNat 32 (8 * y.val)) &&& 0x78#32 =
      BitVec.ofNat 32 (8 * ((x.val + y.val) % 16)) := by decide +kernel
  exact h ⟨j, hj⟩ ⟨a, ha⟩

/-- `lsls r0, r0, #6; movs r1, #64; ands r0, r1` with `r0 = g`: the group's half of the buffer,
`64 (g mod 2)` bytes from its start. -/
theorem group_index (g : Nat) (hg : g < 10) :
    (BitVec.ofNat 32 g <<< 6) &&& 64#32 = BitVec.ofNat 32 (64 * (g % 2)) := by
  have h : ∀ x : Fin 10, (BitVec.ofNat 32 x.val <<< 6) &&& 64#32 = BitVec.ofNat 32 (64 * (x.val % 2)) := by
    decide +kernel
  exact h ⟨g, hg⟩

/-! ## Rounds -/

/-- The slot of variable `x` (`a = 0`, …, `h = 7`) in round `r` of a group: `(x − r) mod 8`. -/
def slot (r x : Nat) : Nat := (x + 8 - r % 8) % 8

/-- The working variables as round `r` reads them from the slots. -/
def vars (r : Nat) (S : Nat → Word) : Vars :=
  ⟨S (slot r 0), S (slot r 1), S (slot r 2), S (slot r 3), S (slot r 4), S (slot r 5), S (slot r 6),
    S (slot r 7)⟩

/-- `round_body r` with `K_t = k` and `W_t = w`: `T1 = Σ1(e) + Ch + h + k + w`, then
`e' = d + T1` into `d`'s slot, then `a' = Σ0(a) + Maj + T1` into `h`'s slot. -/
def codeRound (r : Nat) (k w : Word) (S : Nat → Word) : Nat → Word :=
  let e := S (slot r 4)
  let t1 := Sigma1 e + Ch e (S (slot r 5)) (S (slot r 6)) + S (slot r 7) + k + w
  let S := upd S (slot r 3) (S (slot r 3) + t1)
  let a := S (slot r 0)
  upd S (slot r 7) (Sigma0 a + Maj a (S (slot r 1)) (S (slot r 2)) + t1)

/-- One code round is round `t` of the specification, read through the next round's slots. -/
theorem codeRound_eq (A : Array Word) (r t : Nat) (S : Nat → Word) :
    vars (r + 1) (codeRound r K[t]! A[t]! S) = round A (vars r S) t := by
  have s0 : slot (r + 1) 0 = slot r 7 := by unfold slot; omega
  have s1 : slot (r + 1) 1 = slot r 0 := by unfold slot; omega
  have s2 : slot (r + 1) 2 = slot r 1 := by unfold slot; omega
  have s3 : slot (r + 1) 3 = slot r 2 := by unfold slot; omega
  have s4 : slot (r + 1) 4 = slot r 3 := by unfold slot; omega
  have s5 : slot (r + 1) 5 = slot r 4 := by unfold slot; omega
  have s6 : slot (r + 1) 6 = slot r 5 := by unfold slot; omega
  have s7 : slot (r + 1) 7 = slot r 6 := by unfold slot; omega
  simp only [vars, codeRound, round, upd, s0, s1, s2, s3, s4, s5, s6, s7, ↓reduceIte]
  simp (disch := (unfold slot; omega)) only [ite_eq_right]
  rw [T1_order, a_order]

/-- Rounds `t0, …, t0 + m − 1` of the specification from `v`. -/
def roundsFrom (A : Array Word) (v : Vars) (t0 : Nat) : Nat → Vars
  | 0 => v
  | m + 1 => round A (roundsFrom A v t0 m) (t0 + m)

theorem roundsFrom_add (A : Array Word) (v : Vars) (t0 a b : Nat) :
    roundsFrom A v t0 (a + b) = roundsFrom A (roundsFrom A v t0 a) (t0 + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, roundsFrom, ih, roundsFrom, Nat.add_assoc]

theorem roundsFrom_foldl (A : Array Word) (v : Vars) (n : Nat) :
    roundsFrom A v 0 n = (List.range n).foldl (round A) v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [roundsFrom, ih, List.range_succ, List.foldl_append, Nat.zero_add]; rfl

/-- Rounds `0 … m − 1` of a group, `K_r = k r`, `W_r = w r`. -/
def codeRuns (k w : Nat → Word) : Nat → (Nat → Word) → Nat → Word
  | 0, S => S
  | m + 1, S => codeRound m (k m) (w m) (codeRuns k w m S)

/-- The eight unrolled rounds of group `g`: `K_{8g+r}`, and `W` from the half `8 (g mod 2)` of the
buffer. -/
def codeGroup (g : Nat) (buf S : Nat → Word) : Nat → Word :=
  codeRuns (fun r => K[8 * g + r]!) (fun r => buf (8 * (g % 2) + r)) 8 S

/-- A group is eight specification rounds when the buffer half holds `W_{8g}, …, W_{8g+7}`. -/
theorem codeGroup_eq (A : Array Word) (g : Nat) {buf : Nat → Word}
    (hw : ∀ r, r < 8 → buf (8 * (g % 2) + r) = A[8 * g + r]!) (S : Nat → Word) :
    vars 0 (codeGroup g buf S) = roundsFrom A (vars 0 S) (8 * g) 8 := by
  have : ∀ m, m ≤ 8 → vars m (codeRuns (fun r => K[8 * g + r]!) (fun r => buf (8 * (g % 2) + r)) m S) =
      roundsFrom A (vars 0 S) (8 * g) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [codeRuns, hw m (by omega), codeRound_eq, ih (by omega), roundsFrom]
  exact this 8 (Nat.le_refl _)

/-! ## The block -/

/-- Groups `0 … g − 1` of `m0c_sha512_block` from the loaded words `M` and the working
variables `S`: (buffer, slots). Groups 2, 4, 6 and 8 first refresh the schedule
(`cmp r0, #2; blo; lsrs r1, r0, #1; bcs`). -/
def codeGroups (M S : Nat → Word) : Nat → (Nat → Word) × (Nat → Word)
  | 0 => (M, S)
  | g + 1 =>
    let st := codeGroups M S g
    let buf := if 2 ≤ g ∧ g % 2 = 0 then schedRun st.1 16 else st.1
    (buf, codeGroup g buf st.2)

/-- Ten groups are the eighty rounds of `compress` over the specification's schedule. -/
theorem codeGroups_eq {M : Array Word} (hM : M.size = 16) (S : Nat → Word) :
    vars 0 (codeGroups (fun i => M[i]!) S 10).2 = (List.range 80).foldl (round (schedule M)) (vars 0 S) := by
  let W := Wt (fun i => M[i]!)
  have inv : ∀ g, g ≤ 10 →
      Window W (max 16 (16 * ((g + 1) / 2))) (codeGroups (fun i => M[i]!) S g).1 ∧
      vars 0 (codeGroups (fun i => M[i]!) S g).2 = roundsFrom (schedule M) (vars 0 S) 0 (8 * g) := by
    intro g
    induction g with
    | zero =>
      intro _
      refine ⟨fun t ht _ => ?_, rfl⟩
      simp only [codeGroups, W]
      rw [Nat.mod_eq_of_lt (by omega), Wt, ite_eq_left (by omega)]
    | succ g ih =>
      intro hg
      obtain ⟨hw, hv⟩ := ih (by omega)
      simp only [codeGroups]
      generalize codeGroups (fun i => M[i]!) S g = st at hw hv ⊢
      have hw' : Window W (max 16 (16 * ((g + 2) / 2)))
          (if 2 ≤ g ∧ g % 2 = 0 then schedRun st.1 16 else st.1) := by
        split
        · have := schedRun_window (fun i => M[i]!) (show 16 ≤ max 16 (16 * ((g + 1) / 2)) by omega)
            (by omega) hw
          rwa [show max 16 (16 * ((g + 1) / 2)) + 16 = max 16 (16 * ((g + 2) / 2)) by omega] at this
        · rwa [show max 16 (16 * ((g + 2) / 2)) = max 16 (16 * ((g + 1) / 2)) by omega]
      refine ⟨by rwa [show g + 1 + 1 = g + 2 by omega], ?_⟩
      rw [codeGroup_eq (schedule M) g (fun r hr => ?_), hv, show 8 * (g + 1) = 8 * g + 8 by omega,
        roundsFrom_add, Nat.zero_add]
      rw [schedule_get hM (by omega), show 8 * (g % 2) + r = (8 * g + r) % 16 by omega]
      exact hw' _ (by omega) (by omega)
  rw [(inv 10 (Nat.le_refl _)).2, roundsFrom_foldl]

/-- `compress` of a block as `m0c_sha512_block` computes it: the ten groups from `V = H` over the
parsed words, then `H += V`. -/
theorem compress_code (H : Array Word) (block : List Byte) :
    compress H block =
      let v := vars 0 (codeGroups (fun i => (parse block)[i]!) (fun i => H[i]!) 10).2
      #[v.a + H[0]!, v.b + H[1]!, v.c + H[2]!, v.d + H[3]!,
        v.e + H[4]!, v.f + H[5]!, v.g + H[6]!, v.h + H[7]!] := by
  rw [codeGroups_eq (by simp [parse])]
  rfl

end M0Crypto.Release.Ed25519Sha512Rounds
