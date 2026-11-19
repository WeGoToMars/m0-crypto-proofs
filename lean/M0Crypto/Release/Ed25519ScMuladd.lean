import M0Crypto.Release.Ed25519CallProgCallee
import M0Crypto.Release.Ed25519SignRun
import M0Crypto.Release.Ed25519MpMul

/-!
# `m0c_mp_mul` as a callee of `m0c_sc_muladd` and `m0c_sc_reduce`

`mpAd n` is `m0c_mp_mul`'s adapter with `r3 = n` pinned (`n = 8` in `m0c_sc_muladd`, `n = 9` in
`m0c_sc_reduce`), from lane B's `mp_mul_te`: the `8 n` bytes at `r0` become the product of the
`4 n` bytes at `r1` and at `r2`.
-/

namespace M0Crypto.Release.Ed25519ScMuladd

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb (Event)
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519ScalarChain (wv)
open M0Crypto.Artifacts.Ed25519Compact (mp_mul sc_muladd sc_reduce)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-! ## `mp_mul` of `n` words -/

/-- The `8 n` bytes at `r0` from the `4 n` bytes at `r1` and `r2`, apart from them; `r3 = n`. -/
def ioMp (n : Nat) : Iface :=
  { ins := [(1, 0, .raw (.k (4 * n))), (2, 0, .raw (.k (4 * n)))], outs := [(0, 0, .bytes (8 * n))],
    wr := [⟨0, 0, .k (8 * n)⟩], rd := [⟨0, 0, .k (8 * n)⟩, ⟨1, 0, .k (4 * n)⟩, ⟨2, 0, .k (4 * n)⟩],
    al := [0, 1, 2], kreq := [(3, n)],
    apt := [(⟨0, 0, .k (8 * n)⟩, ⟨1, 0, .k (4 * n)⟩), (⟨0, 0, .k (8 * n)⟩, ⟨2, 0, .k (4 * n)⟩)] }

def mpS (n : Nat) : CalleeS := calleeAt mp_mul (ioMp n) [0, 1, 2, 3]

/-- The `k` little-endian bytes of `x`. -/
def encK (k x : Nat) : List Byte := (List.range k).map fun i => BitVec.ofNat 8 (x / 2 ^ (8 * i))

theorem encK_decode {l : List Byte} {k : Nat} (h : l.length = k) : encK k (decodeInt l) = l := by
  subst h
  apply List.ext_getElem (by simp [encK])
  intro i h1 h2
  simp only [encK, List.getElem_map]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Ed25519Bytes.decodeInt_byte]; simp [List.getD_eq_getElem?_getD, h2]

/-- The product of `mp_mul`'s inputs as `8 n` bytes. -/
def mpV (n : Nat) : List V → List V
  | [.b a, .b b] => [.b (encK (8 * n) (decodeInt a * decodeInt b))]
  | _ => [.none]

/-- `m0c_mp_mul` with `r3 = n`. -/
noncomputable def mpN (b : Build) (n : Nat) (hn : 8 * n < 2 ^ 32) := letI := b.codeBytes
  ((Ed25519MpMul.mp_mul_te b).pin 3 3 (BitVec.ofNat 32 n) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 8 * n⟩])
    (fun s => [⟨s.regs 0, 8 * n⟩, ⟨s.regs 1, 4 * n⟩, ⟨s.regs 2, 4 * n⟩])
    (fun _ h => by simp [Ed25519MpMul.mpR, h, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)])
    fun _ h => by simp [Ed25519MpMul.mpR, h, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)]).code
      (footprint mp_mul) (show Routine.rangesSub Ed25519MpMul.mpR.code (footprint mp_mul) = true by decide +kernel)

theorem has_of_reg {a y : Word} {n : Nat} (h : Region a n y) : Rgn.Has ⟨a, n⟩ y :=
  ⟨(y - a).toNat, h, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩

theorem reg_of_has {a y : Word} {n : Nat} (h : Rgn.Has ⟨a, n⟩ y) : Region a n y :=
  let ⟨_, ho, e⟩ := h; e ▸ region_lt ho

/-- **`m0c_mp_mul`'s adapter** with `r3 = n` in build `b`. -/
noncomputable def mpAd (b : Build) (Rs : Rels) (n : Nat) (h0 : 0 < n) (hn : 8 * n < 2 ^ 32) :
    AdE Rs (cb := b.codeBytes) (mpS n) := by
  letI := b.codeBytes
  have hm : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h8 : 8 * n ≠ 0 := by omega
  have h4 : 4 * n ≠ 0 := by omega
  refine Ad.ofTSpec _ rfl rfl (by show Ed25519MpMul.D = stackOf mp_mul; decide) (mpN b n hn) (fun _ p _ h => ?_)
    (mpV n) (fun _ _ _ st _ hg hv _ => ?_) (fun _ => ?_) (fun _ => ?_) fun _ _ st m _ vs _ hi hp => ?_
  · simp only [Ed25519MpMul.mpE, setPub, Nat.reduceEqDiff, ↓reduceIte, hm] at h
    refine EffT.mono h (by show Ed25519MpMul.D ≤ stackOf mp_mul; decide) (fun y ⟨r, hr, hy⟩ => ⟨r, ?_, hy⟩) (fun y ⟨r, hr, hy⟩ => .inr ?_) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [rgnsC, SRgn.rgnC, ALen.val, mpS, calleeAt, ioMp, h8, h4, ↓reduceIte, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.cons_append, List.mem_cons, BitVec.add_zero]
      rcases hr with rfl | rfl | rfl <;> simp [CalleeS.reg, List.idxOf_cons]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(1, 0, .raw (.k (4 * n))), by simp [mpS, calleeAt, ioMp], by
          simpa [CalleeS.reg, CalleeS.iniIn, ALen.val, mpS, calleeAt, List.idxOf_cons] using
          reg_of_has hy⟩
      · exact ⟨(2, 0, .raw (.k (4 * n))), by simp [mpS, calleeAt, ioMp], by
          simpa [CalleeS.reg, CalleeS.iniIn, ALen.val, mpS, calleeAt, List.idxOf_cons] using
          reg_of_has hy⟩
    · obtain ⟨x, hx, hy⟩ := hy
      simp only [mpS, calleeAt, ioMp, List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_singleton_self _, has_of_reg (by simpa [CalleeS.reg, CalleeS.iniOut, Kd.sz, mpS, calleeAt] using hy)⟩
  · have h3 : st.regs 3 = BitVec.ofNat 32 n := hg.2.2 (3, n) (by simp [mpS, calleeAt, ioMp])
    have d1 := hv.2.2 _ (show (⟨0, 0, .k (8 * n)⟩, ⟨1, 0, .k (4 * n)⟩) ∈ (mpS n).io.apt by simp [mpS, calleeAt, ioMp])
    have d2 := hv.2.2 _ (show (⟨0, 0, .k (8 * n)⟩, ⟨2, 0, .k (4 * n)⟩) ∈ (mpS n).io.apt by simp [mpS, calleeAt, ioMp])
    simp only [rgnsC, SRgn.rgnC, ALen.val, h8, h4, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      BitVec.add_zero] at d1 d2
    refine ⟨⟨by rw [h3, hm]; exact h0, hg.1 0 (by simp [mpS, calleeAt, ioMp]), hg.1 1 (by simp [mpS, calleeAt, ioMp]),
      hg.1 2 (by simp [mpS, calleeAt, ioMp]), ?_, ?_⟩, h3⟩ <;> rw [h3, hm]
    · exact d1 _ List.mem_cons_self _ List.mem_cons_self
    · exact d2 _ List.mem_cons_self _ List.mem_cons_self
  · simp [rgnsC, SRgn.rgnC, ALen.val, mpS, calleeAt, ioMp, h8]
  · simp [rgnsC, SRgn.rgnC, ALen.val, mpS, calleeAt, ioMp, h8, h4]
  · rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩⟩ <;>
      simp only [InsRel, All2, mpS, calleeAt, ioMp, Rel, In.kd, ALen.val, and_true, and_false, false_and] at hi
    simp only [OutsRel, All2, mpS, calleeAt, ioMp, mpV, Rel, BitVec.add_zero, and_true] at hi ⊢
    rw [← encK_decode (bytesAt_length m (st.regs 0) (8 * n)), ← hi.1, ← hi.2, show 8 * n = 4 * (2 * n) by omega,
      decodeInt_words, decodeInt_words, decodeInt_words]
    have := hp.1; simp only [Ed25519MpMul.mpR, hp.2, hm] at this; exact congrArg _ this

end M0Crypto.Release.Ed25519ScMuladd
