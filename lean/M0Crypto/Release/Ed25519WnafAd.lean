import M0Crypto.Release.Ed25519ScWnaf
import M0Crypto.Release.Ed25519CallProgStitch
import M0Crypto.Release.Ed25519VerifyVal

/-!
# `m0c_sc_wnaf` as a stitched-site callee

`sc_wnaf`'s trace depends on its scalar (`Ed25519ScWnaf.wnPub`), so at `m0c_ed25519_verify`'s
`sc_wnaf` calls it is an `AdX`: its public values are `r0`, `r1`, `r2`, `sp` and the scalar's 8
words at `r1` (`xpW`), which are the words of the scalar's input value (`xpvW`).

* `wordsAt`, `wordsOf`, `bytesOfW`: the words at an address, the words of a byte list, the bytes
  of words; `wordsAt_eq` and `bytes_words` relate them;
* `wn_teX b w`: `sc_wnaf_te` re-published at the callee's public values (`gW_pub`) and pinned at
  `r2 = w` (`wnP`), so that the result records the digit width;
* `wnafAd b Rs w`: the adapter of `vaS (.wnaf w)` for `2 ≤ w ≤ 8`; its values are `wnafV w`.
-/

namespace M0Crypto.Release.Ed25519WnafAd

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (Rgn Has bytesAt)
open M0Crypto.Release.Routine (codeR pubOf)
open M0Crypto.Release.StackEffect (EffT)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519VerifyProg (vaS ioWnaf)
open M0Crypto.Release.Ed25519ScWnaf (wnR wnPub wnE sc_wnaf_te O)
open M0Crypto.Release.Ed25519VerifyVal (wnafV wnaf_bytes)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519 (Build)

/-! ## Words of bytes -/

/-- The `n` words at `a`. -/
def wordsAt (m : Mem) (a : Word) (n : Nat) : List Word :=
  (List.range n).map fun i => read32 m (a + BitVec.ofNat 32 (4 * i))

/-- The `n` little-endian words of the bytes `l`. -/
def wordsOf (l : List (BitVec 8)) (n : Nat) : List Word :=
  (List.range n).map fun i => l.getD (4 * i + 3) 0 ++ l.getD (4 * i + 2) 0 ++ l.getD (4 * i + 1) 0 ++ l.getD (4 * i) 0

/-- The `4 n` bytes of the words `w 0, …, w (n - 1)`. -/
def bytesOfW (w : Nat → Word) (n : Nat) : List (BitVec 8) :=
  (List.range (4 * n)).map fun j => (w (j / 4)).extractLsb' (8 * (j % 4)) 8

theorem bytesAt_getD {m : Mem} {a : Word} {n j : Nat} (h : j < n) :
    (bytesAt m a n).getD j 0 = m (a + BitVec.ofNat 32 j) := by
  simp [bytesAt, h]

theorem wordsAt_eq (m : Mem) (a : Word) (n : Nat) : wordsAt m a n = wordsOf (bytesAt m a (4 * n)) n := by
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [bytesAt_getD (by omega), bytesAt_getD (by omega), bytesAt_getD (by omega), bytesAt_getD (by omega)]
  simp only [read32, ofNat_add_assoc]

theorem read32_byte (m : Mem) (x : Word) (r : Nat) (hr : r < 4) :
    (read32 m x).extractLsb' (8 * r) 8 = m (x + BitVec.ofNat 32 r) := by
  ext i hi
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [read32, BitVec.getElem_extractLsb', BitVec.getLsbD_append, BitVec.add_zero] <;>
    repeat' split
  all_goals first | omega | (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega)

theorem bytes_words (m : Mem) (a : Word) (n : Nat) :
    bytesOfW (fun i => (wordsAt m a n).getD i 0) n = bytesAt m a (4 * n) := by
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hq : j / 4 < n := by omega
  simp only [wordsAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq, Option.map_some,
    Option.getD_some]
  rw [read32_byte m _ (j % 4) (Nat.mod_lt _ (by decide)), ofNat_add_assoc]
  rw [show 4 * (j / 4) + j % 4 = j by omega]

/-! ## The adapter -/

/-- The extra public values: the scalar's 8 words at `r1`. -/
def xpW (st : State) : List Word := wordsAt st.mem (st.regs 1) 8

/-- The extra public values from the input value: the words of the scalar's bytes. -/
def xpvW : List V → List Word
  | [.b l] => wordsOf l 8
  | _ => []

/-- `wnPub` from the callee's public values: the four registers and the scalar of the 8 words. -/
def gW (p : Nat → Word) : (Nat → Word) × Nat :=
  (pubOf [p 0, p 1, p 2, p 3], decodeInt (bytesOfW (fun i => p (4 + i)) 8))

theorem pubX_wn (w : Nat) (st : State) :
    (vaS (.wnaf w)).pubX xpW st = pubOf ([st.regs 0, st.regs 1, st.regs 2, st.regs 13] ++ xpW st) := rfl

theorem gW_pub (w : Nat) (st : State) : gW ((vaS (.wnaf w)).pubX xpW st) = wnPub 0 st := by
  rw [pubX_wn]
  refine Prod.ext (by simp [gW, wnPub, pubOf]) ?_
  simp only [gW, wnPub]
  rw [show (32 : Nat) = 4 * 8 from rfl, ← bytes_words]
  congr 2
  funext i
  simp only [pubOf, xpW, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD]
  rw [show 4 + i = i + 1 + 1 + 1 + 1 by omega]
  simp only [List.getElem?_cons_succ]

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- `sc_wnaf`'s effect is the callee's. -/
theorem wn_eff (w : Nat) (base : Word) (p : Nat → Word) (tr : List Event) (h : wnE base (gW p) tr) :
    (vaS (.wnaf w)).Eff p base tr := by
  refine EffT.mono h (by show 40 ≤ stackOf O; decide +kernel) (fun y ⟨r, hr, hy⟩ => ⟨r, ?_, hy⟩)
    (fun y ⟨r, hr, hy⟩ => .inr ⟨_, .head _, ?_⟩) (fun y ⟨x, hx, hy⟩ => ⟨_, .head _, ?_⟩)
  · show r ∈ [codeR base, ⟨p 1 + BitVec.ofNat 32 0, 32⟩, ⟨p 0 + BitVec.ofNat 32 0, 256⟩]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp [gW, pubOf]
  · simp only [List.mem_singleton] at hr; subst hr
    show Region (p 1 + BitVec.ofNat 32 0) 32 y; rw [BitVec.add_zero]; obtain ⟨_, ho, e⟩ := hy; exact Region.mk ho e
  · simp only [vaS, calleeAt, ioWnaf, List.mem_singleton] at hx; subst hx
    have hy : Region (p 0 + BitVec.ofNat 32 0) 256 y := hy
    rw [BitVec.add_zero] at hy; exact Rgn.of_region hy
end

/-- The scalar's bytes and bound from the input value of verify's `sc_wnaf` call. -/
theorem wn_in {Rs : Rels} {c : Ctx} {sp : Word} {st : State} {vs : List V} (w : Nat)
    (hi : InsRel Rs c sp (vaS (.wnaf w)).io st vs) :
    ∃ l, vs = [.b l] ∧ bytesAt st.mem (st.regs 1) 32 = l ∧ decodeInt l < 2 ^ 255 := by
  rcases vs with _ | ⟨l | _ | _ | _ | _ | _, _ | _⟩ <;>
    simp only [InsRel, All2, vaS, calleeAt, ioWnaf, Rel, In.kd, and_true, and_false] at hi
  simp only [BitVec.add_zero] at hi
  exact ⟨l, rfl, hi.1, hi.2⟩

/-- `m0c_sc_wnaf` at `r2 = w`, over its unit's footprint. -/
def wnP (w : Nat) : Routine.Routine :=
  ⟨O, footprint O, wnR.stack, fun b s => wnR.Pre b s ∧ s.regs 2 = BitVec.ofNat 32 w, wnR.wr, wnR.rd,
    fun s m x => wnR.Post s m x ∧ s.regs 2 = BitVec.ofNat 32 w, wnR.clob⟩

/-- **`sc_wnaf`'s call lemma at the callee's public values**, with `r2 = w`. -/
noncomputable def wn_teX (b : Build) (w : Nat) : letI := b.codeBytes
    (wnP w).TE (fun _ st => (vaS (.wnaf w)).pubX xpW st)
      fun b p => wnE b (gW (setPub p 2 (BitVec.ofNat 32 w))) :=
  letI := b.codeBytes
  (((sc_wnaf_te b).code (footprint O) (by cases b <;> decide +kernel)).repub _ gW fun _ st => gW_pub w st).pin
    2 2 (BitVec.ofNat 32 w) (fun _ st => by rw [pubX_wn]; rfl) wnR.wr wnR.rd (fun _ _ => rfl) fun _ _ => rfl

/-- **`m0c_sc_wnaf`'s adapter at a stitched site** in build `b`, for `2 ≤ w ≤ 8`: the digit bytes
`wnafV w` of the scalar, its trace a function of `r0`, `r1`, `r2`, `sp` and the scalar's 8 words. -/
noncomputable def wnafAd (b : Build) (Rs : Rels) (w : Nat) (hw : 2 ≤ w) (hw8 : w ≤ 8) :
    AdX Rs (cb := b.codeBytes) (vaS (.wnaf w)) :=
  letI := b.codeBytes
  AdX.ofTE (wnP w) rfl rfl (by show 40 = stackOf O; decide +kernel) xpW xpvW
    (fun _ _ st vs hi => by
      obtain ⟨l, rfl, hl, -⟩ := wn_in w hi
      show wordsAt _ _ 8 = wordsOf l 8
      rw [wordsAt_eq, hl])
    (wn_teX b w) (fun _ => True) (fun base p tr _ h => wn_eff w base p tr h) (fun _ => True) (wnafV w)
    (fun _ _ _ st vs hg hv hi _ => by
      obtain ⟨l, rfl, hl, hk⟩ := wn_in w hi
      have h2 : st.regs 2 = BitVec.ofNat 32 w := hg.2.2 (2, w) (List.mem_singleton_self _)
      have hd : Frame.Disj (st.regs 0 + BitVec.ofNat 32 0) 256 (st.regs 1 + BitVec.ofNat 32 0) 32 :=
        hv.2.2 _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
      simp only [BitVec.add_zero] at hd
      have hw' : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
      exact ⟨⟨by rw [hl]; exact hk, by rw [h2, hw']; exact hw, by rw [h2, hw']; exact hw8,
        hg.1 0 (List.mem_singleton_self _), hd.2.2⟩, h2⟩)
    (fun st => by show ([⟨st.regs 0, 256⟩] : List Rgn) = [⟨st.regs 0 + 0#32, 256⟩]; rw [BitVec.add_zero])
    (fun st => by show ([⟨st.regs 1, 32⟩] : List Rgn) = [⟨st.regs 1 + 0#32, 32⟩]; rw [BitVec.add_zero])
    (fun _ _ st m _ vs _ hi _ hp => by
      obtain ⟨l, rfl, hl, -⟩ := wn_in w hi
      simp only [OutsRel, All2, vaS, calleeAt, ioWnaf, wnafV, Rel, BitVec.add_zero, and_true]
      refine wnaf_bytes fun i hi => ?_
      rw [hp.1 i hi, hp.2, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    fun _ _ _ _ _ _ _ _ => trivial

end M0Crypto.Release.Ed25519WnafAd
