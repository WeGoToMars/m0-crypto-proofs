import M0Crypto.Release.ConstantTime.InstructionCases
import M0Crypto.Release.ConstantTime.FunctionalWrites
import M0Crypto.Release.ConstantTime.BufferSeparation

/-!
# Store sites of a certificate

An entry whose stores are all `sp`-tracked needs no separation premise. The remaining stores
(single stores whose base the analysis does not track, and multiple stores with a non-`sp`
base) must lie at a short, named list of code offsets, the *sites*. `certSites` checks that
list; `bufferStoreOk_of_site` turns a per-site separation fact into the certificate's
`BufferStoreOk`; sites prove that fact with `buffer_subrange_separated`.
-/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Frame (Disj)

/-- The per-instruction store requirement at code offset `off`. -/
def siteOk (sites : List Nat) (off : Nat) (st : AbsState) : Thumb.Instr → Bool
  | .stm n l => (st.get n.val).isSp || (sites.contains off && decide (0 < bitCount l))
  | i => !untrackedStore st i || sites.contains off

/-- Walk a block, requiring every non-`sp` store to be at a listed site. -/
def walkSites (env : Env) (sites : List Nat) (ctx : Option Nat) : Nat → AbsState → List Thumb.Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    siteOk sites off st i &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out =>
      match out.succs with
      | [(_, next)] => walkSites env sites ctx (off + i.size) next is
      | _ => walkSites env sites ctx (off + i.size) st is

def certSites (env : Env) (sites : List Nat) (cert : Cert) : Bool :=
  cert.all fun b => walkSites env sites b.ctx b.off b.st b.code

theorem blockPoint_sites {env : Env} {sites : List Nat} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Thumb.Instr} (hc : walkSites env sites b.ctx b.off b.st b.code = true)
    (hp : BlockPoint env b off st code) : walkSites env sites b.ctx off st code = true := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkSites, Bool.and_eq_true, hx, hs] at ih
    exact ih.2

/-- At a checked position, the store requirement holds. -/
theorem certPoint_sites {env : Env} {sites : List Nat} {cert : Cert} {b : Blk} {off : Nat}
    {st : AbsState} {i : Thumb.Instr} {is : List Thumb.Instr}
    (hc : certSites env sites cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) : siteOk sites off st i = true := by
  have hw := blockPoint_sites (List.all_eq_true.mp hc b hm) hp
  simp only [walkSites, Bool.and_eq_true] at hw
  exact hw.1

/-- A certificate whose non-`sp` stores are at listed sites needs the separation premise
only at those sites. -/
theorem bufferStoreOk_of_site {env : Env} {sites : List Nat} {cert : Cert} {b : Blk} {off : Nat}
    {st : AbsState} {i : Thumb.Instr} {is : List Thumb.Instr} {p : Params} {bytes : List (BitVec 8)}
    {s : State} (hc : certSites env sites cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is))
    (hS : off ∈ sites → (∀ n l, i = .stm n l → 0 < bitCount l) → BufferStoreOk env p bytes st s i) :
    BufferStoreOk env p bytes st s i := by
  have h := certPoint_sites hc hm hp
  cases i with
  | memImm op t n imm =>
    intro hsp hop
    have hu : untrackedStore st (.memImm op t n imm) = true := by simp [untrackedStore, hop, hsp]
    simp only [siteOk, hu, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    exact hS h (fun _ _ h => nomatch h) hsp hop
  | memReg op t n m =>
    intro hsp hop
    have hu : untrackedStore st (.memReg op t n m) = true := by simp [untrackedStore, hop, hsp]
    simp only [siteOk, hu, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    exact hS h (fun _ _ h => nomatch h) hsp hop
  | stm n l =>
    intro hn
    have hns : (st.get n.val).isSp = false := by
      cases hg : st.get n.val <;> simp [AbsVal.isSp] <;> exact False.elim (hn _ _ hg)
    simp only [siteOk, hns, Bool.false_or, Bool.and_eq_true, List.contains_iff_mem,
      decide_eq_true_eq] at h
    exact hS h.1 (fun _ _ h' => by cases h'; exact h.2) hn
  | _ => trivial

/-- The event of the step at a checked position is the instruction's own event. -/
theorem certPoint_step_event {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s s₂ t : State} {e : Event} (i : Instr)
    (hc : certOk env bytes entry init cert = true)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (h : LowEq p bytes off st s s₂) (hstep : step s = .ok (t, e)) :
    e = ⟨s.pc, i, i.accesses s⟩ := by
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hd := decode_at h.code₁ off i hdecode hlen
  have heven := certPoint_pc_even p.base hbase ha hm hp
  have hpc := h.pc
  unfold step at hstep
  simp only [hpc] at hstep
  rw [heven, hd] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · cases hex : i.exec s <;> simp_all
  · simp at hstep

/-- Bytes of an access whose first and last byte lie in `[buf, buf+len)` are separated from every
region separated from that interval. -/
theorem disj_of_ends {r : Word} {m : Nat} {buf a : Word} {len w : Nat} (hw : 0 < w)
    (hd : Disj r m buf len) (hlen : len + w ≤ 2 ^ 32)
    (hf : ∃ o < len, a = buf + BitVec.ofNat 32 o)
    (hl : ∃ o < len, a + BitVec.ofNat 32 (w - 1) = buf + BitVec.ofNat 32 o) :
    Disj r m a w := by
  obtain ⟨o, ho, rfl⟩ := hf
  obtain ⟨o', ho', hl'⟩ := hl
  have hb : buf.toNat + len ≤ 2 ^ 32 := by
    obtain ⟨_, h, _⟩ := hd; exact h
  have h1 : (buf + BitVec.ofNat 32 o - buf).toNat = o := by
    have : buf + BitVec.ofNat 32 o - buf = BitVec.ofNat 32 o := by bv_omega
    rw [this, BitVec.toNat_ofNat]; omega
  have h2 : (buf + BitVec.ofNat 32 o + BitVec.ofNat 32 (w - 1) - buf).toNat < len := by
    rw [hl']
    have : buf + BitVec.ofNat 32 o' - buf = BitVec.ofNat 32 o' := by bv_omega
    rw [this, BitVec.toNat_ofNat]; omega
  have hr := buffer_range_of_endpoints buf (buf + BitVec.ofNat 32 o) len w hw hlen (by omega) h2
  rw [h1] at hr
  have hsub := disj_buffer_subrange hd hw hr
  exact hsub

end M0Crypto.Release.ConstantTime
