import M0Crypto.Release.X25519TraceRecord
import M0Crypto.Release.ConstantTime.X25519Holes
import SafegcdTermination.StackFootprint

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.TraceSpec (BelowEntry AtOrAboveSp WrittenSinceAllocated)
open M0Crypto.Release.StackEffect
open M0Crypto.Release.X25519Layout (E SAVED LFRAME sZ2)
open M0Crypto.Release.X25519SafegcdCode (borrowed)
open M0Crypto.Release.X25519SafegcdFrame (workSp rebase)
open M0Crypto.Release.X25519SafegcdLink (layout checked)
open SafegcdRow.BatchCode (frameBytes callTo)
open SafegcdTermination.Bank (addr)
open SafegcdTermination.TraceWrites (subregion)
open SafegcdTermination.LinkedInversion

set_option maxRecDepth 40000
set_option maxHeartbeats 1800000

private def source (c : X25519.Ctx) := addr (E c) sZ2

private def initial (c : X25519.Ctx) : Ef := ⟨workSp (E c),Region (source c) 32⟩

private theorem distance (c : X25519.Ctx) :
    (c.sp0 - workSp (E c)).toNat = SAVED+LFRAME+borrowed := by
  have he : c.sp0-workSp (E c) = BitVec.ofNat 32 (SAVED+LFRAME+borrowed) := by
    simp only [workSp,E,BitVec.ofNat_add]
    bv_omega
  rw [he]
  decide

private theorem above_frame (c : X25519.Ctx) {y : Word} (h : Region (workSp (E c)) frameBytes y) :
    AtOrAboveSp c.sp0 (workSp (E c)) y := by
  unfold AtOrAboveSp
  rw [distance]
  exact Nat.lt_of_lt_of_le h (by decide)

private theorem source_in_frame (c : X25519.Ctx) {y : Word} (h : Region (source c) 32 y) :
    Region (workSp (E c)) frameBytes y := by
  rw [source,rebase] at h
  exact subregion (by decide : borrowed+sZ2+32 ≤ frameBytes) h

private theorem literal_in_code {c : X25519.Ctx} {y : Word} (h : layout.literalRegion c.base y) :
    Region c.base Artifacts.Release.size y := by
  unfold Layout.literalRegion at h
  rw [ofNat_add_assoc] at h
  exact X25519Ev.band_code (by decide +kernel) h

/-- The exact trace needs the in-place source bytes initialized on entry. The
initialization of every other frame byte is part of the shared proof. -/
private theorem summary_good {c : X25519.Ctx} (hv : X25519.Valid c) :
    Good c.sp0 X25519.stackBytes (initial c) (x25519_trace c) := by
  let sp := workSp (E c)
  let a := source c
  let q := initial c
  let core := layout.trace c.base sp a a
  let first : Event := ⟨c.base+BitVec.ofNat 32 x25519CallSite,
    callTo x25519CallSite (layout.first+layout.start),[]⟩
  have hU : ∀ y, q.U y → AtOrAboveSp c.sp0 sp y := fun y hy =>
    above_frame c (source_in_frame c hy)
  have hA : ∀ y, layout.footprint c.base sp a a y → BelowEntry c.sp0 X25519.stackBytes y →
      AtOrAboveSp c.sp0 sp y := by
    rintro y (h | h | h | h) hb
    · exact above_frame c h
    · exact hU y h
    · exact hU y h
    · exact (not_region_of_disj hv.codeS (literal_in_code h) hb).elim
  have hR : ∀ y, layout.required c.base a y → BelowEntry c.sp0 X25519.stackBytes y → q.U y := by
    rintro y (h | h) hb
    · exact h
    · exact (not_region_of_disj hv.codeS (literal_in_code h) hb).elim
  have hG := stack_effect_aligned checked hv.base4 sp a a c.sp0 X25519.stackBytes q rfl
    (by rw [show sp = workSp (E c) from rfl,distance]; decide) (by decide) hU hA hR
  have hKeep : ∀ y, q.U y → (q.step c.sp0 first).U y := fun y hy => ⟨hU y hy,.inl hy⟩
  change Good c.sp0 X25519.stackBytes q (first :: core)
  refine ⟨⟨rfl,?_,?_⟩,(Good.mono (p := q) (q := q.step c.sp0 first) rfl hKeep hG.1).1⟩
  · rintro y (h | h) _
    · exact absurd h (reads_nil y)
    · exact absurd h (writes_nil y)
  · intro y h _
    exact absurd h (reads_nil y)

private theorem initialized_or_write (sp0 : Word) (q : Ef) (tr : List Event) (y : Word)
    (h : (q.run sp0 tr).U y) :
    q.U y ∨ ∃ ev ∈ tr, Writes ev.accesses y := by
  induction tr generalizing q with
  | nil => exact .inl h
  | cons ev tr ih =>
    rcases ih (q.step sp0 ev) h with h | ⟨f,hf,hw⟩
    · exact h.2.elim Or.inl (fun hw => .inr ⟨ev,List.mem_cons_self,hw⟩)
    · exact .inr ⟨f,List.mem_cons_of_mem _ hf,hw⟩

private def entryHole : HEnt := (x25519Holes.find x25519CallSite none).getD default
private def resumeHole : HEnt := (x25519Holes.find x25519CallRet none).getD default

private theorem hole_offsets :
    entryHole.o = x25519InversionCall.spOff ∧ resumeHole.o = entryHole.o ∧ resumeHole.h = entryHole.h := by
  decide +kernel

private theorem source_init :
    (List.range 32).all (fun j =>
      !entryHole.h.testBit (holeBit x25519Env.win.below (x25519InversionCall.srcOff+j))) = true := by
  decide +kernel

private theorem certificate_bands :
    x25519Cert.all (fun b => (decide (b.off+seqSize b.code ≤ Artifacts.Release.inv_canon)) &&
      (!b.ctx.isSome || decide (b.off+seqSize b.code ≤ Artifacts.Release.x25519))) = true := by
  decide +kernel

private theorem block_end {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hm : b ∈ x25519Cert) (hp : BlockPoint x25519Env b off st (i :: is)) :
    off < Artifacts.Release.inv_canon ∧ (Artifacts.Release.x25519 ≤ off → b.ctx = none) := by
  have he := (blockPoint_extent hp).2
  have hn : 0 < seqSize (i :: is) := by
    rw [show seqSize (i :: is) = i.size + seqSize is from rfl]
    have := instr_size_pos i
    omega
  have h := List.all_eq_true.mp certificate_bands b hm
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  refine ⟨by omega,fun hf => ?_⟩
  cases hctx : b.ctx with
  | none => rfl
  | some ctx => simp [hctx] at h; omega

private theorem cert_offset {c : X25519.Ctx} {s : State} {off target : Nat} {st : AbsState}
    (hp : LowEq (x25519Params c) B off st s s) (hAt : s.pc = c.base+BitVec.ofNat 32 target)
    (hx : off < Artifacts.Release.inv_canon) (ht : target < 2^32) : off = target := by
  have hsize : Artifacts.Release.inv_canon < 2^32 := by decide
  exact ofNat_inj_base (by omega) ht (hp.pc.symm.trans hAt)

private theorem outside_cert {c : X25519.Ctx} {u : State} {b : Blk} {off : Nat} {st : AbsState}
    {i : Instr} {is : List Instr} (hCore : X25519Ev.InvPc c.base u.pc)
    (hm : b ∈ x25519Cert) (hp : BlockPoint x25519Env b off st (i :: is))
    (hl : LowEq (x25519Params c) B off st u u) : False := by
  have h := (block_end hm hp).1
  have hSize : Artifacts.Release.size < 2^32 := by decide
  have hStart : Artifacts.Release.inv_canon ≤ Artifacts.Release.size := by decide
  rw [hl.pc] at hCore
  unfold X25519Ev.InvPc Region at hCore
  change (c.base + BitVec.ofNat 32 off -
    (c.base + BitVec.ofNat 32 Artifacts.Release.inv_canon)).toNat < _ at hCore
  bv_omega

private theorem transfer_written {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j k : Nat} {a b : State} {y : Word} (r : X25519CallRecord c states tr j a b)
    (hk : j ≤ k) (hend : k ≤ j+(x25519_trace c).length)
    (hw : WrittenSinceAllocated c.sp0 states tr j y)
    (ha : AtOrAboveSp c.sp0 (workSp (E c)) y) :
    WrittenSinceAllocated c.sp0 states tr k y := by
  obtain ⟨i,hi,hw,hs⟩ := hw
  refine ⟨i,by omega,hw,?_⟩
  intro p u hp hpk hu
  by_cases hj : p ≤ j
  · exact hs p u hp hj hu
  · have he : j+(p-j) = p := by omega
    rw [r.sp_at (i := p-j) (by omega) (by rwa [he])]
    exact ha

private theorem entry_written_at {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j k : Nat} {a b : State} {q : Int} (r : X25519CallRecord c states tr j a b)
    (hj : j < k) (hStart : a.pc ≠ c.ret)
    (hOld : EarlierHoles (env := x25519Env) (cert := x25519Cert) (p := x25519Params c) (bytes := B)
      x25519Holes states tr k) (hlo : entryHole.o ≤ q) (hhi : q < 0)
    (hbit : entryHole.h.testBit (holeBit x25519Env.win.below q) = false) :
    WrittenSinceAllocated c.sp0 states tr j (c.sp0+BitVec.ofInt 32 q) := by
  obtain ⟨blk,off,st,code,hm,hp,hn,hl⟩ := r.pre
  cases code with
  | nil => exact absurd rfl hn
  | cons i is =>
    have he := cert_offset hl r.invoc (block_end hm hp).1 (by decide)
    subst off
    have hc := (block_end hm hp).2 (by decide : Artifacts.Release.x25519 ≤ x25519CallSite)
    obtain ⟨out,hx⟩ := certPoint_xfer x25519_certOk hm hp
    obtain ⟨hol,hfind,_,_,_⟩ := posHoleOk_facts (certPoint_hole x25519_holes hm hp) hx
    have hF : x25519Holes.find x25519CallSite none = some hol := by
      simpa only [hc] using hfind
    have hh : hol = entryHole := by rw [entryHole,hF]; rfl
    subst hol
    exact hOld j hj a r.start hStart blk x25519CallSite st i is entryHole hm hp hl hfind q hlo hhi hbit

private theorem entry_written {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j k : Nat} {a b : State} {y : Word} (r : X25519CallRecord c states tr j a b)
    (hj : j < k) (hStart : a.pc ≠ c.ret)
    (hOld : EarlierHoles (env := x25519Env) (cert := x25519Cert) (p := x25519Params c) (bytes := B)
      x25519Holes states tr k) (hy : Region (source c) 32 y) :
    WrittenSinceAllocated c.sp0 states tr j y := by
  obtain ⟨i,hi,rfl⟩ := hy.exists
  have hb := List.all_eq_true.mp source_init i (List.mem_range.mpr hi)
  have hLo : x25519InversionCall.spOff ≤ x25519InversionCall.srcOff := by decide
  have hHi : x25519InversionCall.srcOff + 32 ≤ 0 := by decide
  have he : source c + BitVec.ofNat 32 i =
      c.sp0 + BitVec.ofInt 32 (x25519InversionCall.srcOff + i) := by
    rw [source,← summary_arg,BitVec.ofInt_add,BitVec.ofInt_natCast,BitVec.add_assoc]
    rfl
  rw [he]
  apply entry_written_at r hj hStart hOld
  · rw [hole_offsets.1]; omega
  · omega
  · simpa using hb

private theorem resumed_holes {c : X25519.Ctx} {states : List State} {tr : List Event}
    {j : Nat} {a b : State} (r : X25519CallRecord c states tr j a b) (hStart : a.pc ≠ c.ret)
    (hOld : EarlierHoles (env := x25519Env) (cert := x25519Cert) (p := x25519Params c) (bytes := B)
      x25519Holes states tr (j+(x25519_trace c).length)) :
    HoleInv x25519Env x25519Cert (x25519Params c) B x25519Holes states tr (j+(x25519_trace c).length) b := by
  intro blk off st i is e hm hp hl hfind q hq hq0 hbit
  have hOff := cert_offset hl r.resume (block_end hm hp).1 (by decide)
  subst off
  have hCtx := (block_end hm hp).2 (by decide : Artifacts.Release.x25519 ≤ x25519CallRet)
  have hF : x25519Holes.find x25519CallRet none = some e := by simpa only [hCtx] using hfind
  have hElt : e = resumeHole := by rw [resumeHole,hF]; rfl
  subst e
  obtain ⟨hE,hR,hBits⟩ := hole_offsets
  rw [hR] at hq
  rw [hBits] at hbit
  have hLen : 0 < (x25519_trace c).length := Nat.zero_lt_succ _
  have hw := entry_written_at r (by omega) hStart hOld hq hq0 hbit
  have hAbove := atOrAbove_of_off (sp0 := c.sp0) (below := x25519Env.win.below)
    (o := entryHole.o) (q := q) (by decide) (by decide) hq hq0
  rw [hE, show c.sp0 + BitVec.ofInt 32 x25519InversionCall.spOff = _ from summary_sp c] at hAbove
  exact transfer_written r (by omega) (Nat.le_refl _) hw hAbove

theorem x25519_fragment_discipline {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s)
    {states : List State} {tr : List Event} {j k : Nat} {a b u : State}
    (r : X25519CallRecord c states tr j a b) (hj : j < k)
    (hk : k < j+(x25519_trace c).length) (hu : states[k]? = some u) :
    FragmentDisciplineAt (env := x25519Env) (cert := x25519Cert) (p := x25519Params c) (bytes := B)
      x25519Holes states tr k u := by
  let i := k-j
  have hi : i < (x25519_trace c).length := by omega
  let ev := (x25519_trace c)[i]
  have hThis : (x25519_trace c)[i]? = some ev := List.getElem?_eq_getElem hi
  obtain ⟨he,v,hv,hObs⟩ := r.at_step i ev hThis
  have heq : j+i = k := by omega
  rw [heq,hu] at hv
  cases hv
  rw [heq] at he
  have hAbove : ∀ y, (Reads ev.accesses y ∨ Writes ev.accesses y) → BelowEntry c.sp0 X25519.stackBytes y →
      AtOrAboveSp c.sp0 (workSp (E c)) y := fun y h hb =>
    (hObs.footprint y h).elim (above_frame c)
      (fun h => (not_region_of_disj hp.valid.codeS h hb).elim)
  refine ⟨hObs.code,?_,?_⟩
  · intro other t hE _ y ha hb
    have he' := Option.some.inj (hE.symm.trans he)
    subst other
    exact .inl (hObs.sp.symm ▸ hAbove y ha hb)
  · intro hOld other hE y hy hyw
    have he' := Option.some.inj (hE.symm.trans he)
    subst other
    have hU := (good_at (summary_good hp.valid) hThis).2.2 y hy hyw
    have ha := hAbove y (.inl hy) hyw
    rcases initialized_or_write _ _ _ _ hU with hSource | ⟨e,hMem,hWr⟩
    · have hStart : a.pc ≠ c.ret := by
        rw [r.invoc]
        exact (x25519_ret_not_code hp _ (by decide)).symm
      exact transfer_written r (by omega) (by omega) (entry_written r hj hStart hOld hSource) ha
    · obtain ⟨m,hGet⟩ := List.mem_iff_getElem?.mp hMem
      have hm : m < i := by
        by_cases hn : m < i
        · exact hn
        · simp [List.getElem?_take,hn] at hGet
      have hLocal : (x25519_trace c)[m]? = some e := by simpa [List.getElem?_take,hm] using hGet
      have hGlobal := (r.at_step m e hLocal).1
      refine ⟨j+m,by omega,⟨e,hGlobal,hWr⟩,?_⟩
      intro p w hpw hpK hPW
      have hIndex : j+(p-j) = p := by omega
      have hSp := r.sp_at (i := p-j) (by omega) (by rwa [hIndex])
      rw [hSp]
      exact ha

theorem x25519_fragment_advance {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s)
    {fuel : Nat} {states : List State} {tr : List Event} {j k : Nat} {a b u : State}
    (hr : runStates c.ret fuel s = .ok (states,tr))
    (r : X25519CallRecord c states tr j a b) (hj : j < k)
    (hk : k ≤ j+(x25519_trace c).length) (hu : states[k]? = some u)
    (old : EarlierHoles (env := x25519Env) (cert := x25519Cert) (p := x25519Params c) (bytes := B)
      x25519Holes states tr k) :
    HoleInv x25519Env x25519Cert (x25519Params c) B x25519Holes states tr k u := by
  by_cases hEnd : k = j+(x25519_trace c).length
  · subst k
    rw [r.finish] at hu
    cases hu
    have hStart : a.pc ≠ c.ret := by
      rw [r.invoc]
      exact (x25519_ret_not_code hp _ (by decide)).symm
    exact resumed_holes r hStart old
  · have hCore := r.core_at hj (by omega) (fun ev he => by
      obtain ⟨v,t,hv,ht,hn,hs⟩ := (runStates_get hr).2.1 k ev he
      rw [hu] at hv
      cases hv
      exact ⟨t,hs⟩)
    intro blk off st i is e hm hpt hlow _ _ _ _ _
    exact (outside_cert hCore hm hpt hlow).elim

end M0Crypto.Release.ConstantTime
