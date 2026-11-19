import M0Crypto.Release.X25519Ev
import M0Crypto.Release.X25519SlotEnv
import M0Crypto.Release.X25519EntrySeg
import M0Crypto.Release.X25519SafegcdLink
import M0Crypto.Release.X25519SafegcdRun

namespace M0Crypto.Release.X25519SafegcdEntry

open M0Crypto.Armv6M (State Word)
open M0Crypto.Release (B B_len InRegion ReachW ReachS Region WritesTo stepsOk_events_iff writes_nil)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Ev (MidPc)
open M0Crypto.Release.X25519OpRun (slotAt)
open M0Crypto.Release.X25519Layout M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode M0Crypto.Release.X25519SlotEnv
open M0Crypto.Release.X25519SafegcdCode M0Crypto.Release.X25519SafegcdFrame
open M0Crypto.Release.X25519SafegcdRun M0Crypto.Release.X25519SafegcdLink
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Thumb M0Crypto.Sym
open SafegcdRow.BatchCode (frameBytes callTo)
open SafegcdTermination.Bank (addr)
open SafegcdTermination.PublicTrace (stackState)
open SafegcdTermination.TraceWrites (byCheck subregion)

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

theorem space {c : X25519.Ctx} (hv : X25519.Valid c) : Space (E c) := by
  have hLo := hv.spLo
  have hAlign := hv.sp4
  have hSp := c.sp0.isLt
  constructor <;> rw [E_toNat hv] <;>
    simp only [X25519.stackBytes,borrowed,SafegcdRow.BatchCode.frameBytes,parked,sK,SAVED,LFRAME] at * <;> omega

theorem work_region {c : X25519.Ctx} (hv : X25519.Valid c) {y : Word}
    (hy : Region (workSp (E c)) span y) : Region c.fp X25519.wipeBytes y := by
  have hLo := hv.spLo
  have hSp := c.sp0.isLt
  refine region_sub ?_ ?_ ?_ hy
  all_goals
    simp only [work_toNat (space hv),E_toNat hv,fp_toNat hv,span,borrowed,parked,sK,lvOut,
      frameBytes,X25519.wipeBytes,X25519.stackBytes,SAVED,LFRAME] at *
    omega

theorem pointer_outside {c : X25519.Ctx} {y : Word}
    (hy : Region (slotAt c lvOut) 4 y) : ¬ Region (workSp (E c)) span y := by
  rw [show slotAt c lvOut = addr (E c) lvOut from rfl,rebase] at hy
  rintro hx
  obtain ⟨i,hi,he⟩ := hy.exists
  obtain ⟨j,hj,he'⟩ := hx.exists
  rw [he,addr,ofNat_add_assoc] at he'
  have hf : span + 4 < 2^32 := by decide
  change j < borrowed+lvOut at hj
  change borrowed+lvOut+4 < 2^32 at hf
  bv_omega

theorem work_disj {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj c.base B.length (workSp (E c)) span := by
  rw [B_len]
  have hw := work_toNat (space hv)
  have hf := fp_toNat hv
  have he := E_toNat hv
  have hl := hv.spLo
  obtain ⟨ha,hb,h⟩ := hv.codeS
  refine ⟨ha,?_,?_⟩
  · simp only [hw,he,span,borrowed,parked,sK,lvOut,frameBytes,X25519.stackBytes,SAVED,LFRAME] at *
    omega
  · apply h.imp
    · intro hx
      simp only [hw,he,hf,borrowed,parked,sK,frameBytes,X25519.stackBytes,SAVED,LFRAME] at *
      omega
    · intro hx
      simp only [hw,he,hf,span,borrowed,parked,sK,lvOut,frameBytes,X25519.stackBytes,SAVED,LFRAME] at *
      omega

private theorem pre {c : X25519.Ctx} (hv : X25519.Valid c) {m : M0Crypto.Armv6M.Mem} {s : State}
    (hC : CodeAt m c.base B) (hPc : s.pc = c.base+BitVec.ofNat 32 oChain) (hB : Body c m s) :
    Pre B c.base oChain s := by
  have hs : s.sp = E c := hB.sp
  refine ⟨hPc,hv.base4,by decide,hB.code hv hC,hs ▸ space hv,?_⟩
  rw [hs]
  exact work_disj hv

private theorem middle (c : X25519.Ctx) {off n : Nat}
    (hlo : oLadder ≤ off) (hhi : off+n ≤ oStore) : InRegion (MidPc c) c.base off n := by
  have h := X25519Ev.bands
  intro i hi
  exact .inr (.inl (Field25519Facts.inReg ⟨hlo,by omega,by omega⟩ i hi))

private theorem block_pc (c : X25519.Ctx) {off : Nat} {l : List Instr} {sp : Word}
    (hf : l.all Instr.falls = true) (hlo : oLadder ≤ off) (hhi : off+seqSize l ≤ oStore)
    {e : Event} (he : e ∈ traceAll l (stackState (c.base+BitVec.ofNat 32 off) sp)) :
    MidPc c e.pc := by
  obtain ⟨i,hi,hp⟩ := traceAll_pc_offset l _ hf e he
  rw [hp]
  change MidPc c (c.base + BitVec.ofNat 32 off + BitVec.ofNat 32 i)
  rw [ofNat_add_assoc]
  exact middle c hlo hhi i hi

private theorem block_writes {sp pc : Word} {l : List Instr} {off : Nat}
    (hf : l.all Instr.falls = true) (hw : writeChk [(13,BitVec.ofNat 32 off,32)] l = true) :
    WritesTo (Region (addr sp off) 32) (traceAll l (stackState pc sp)) := by
  refine byCheck hf hw ?_
  intro p hp i hi
  rw [List.mem_singleton] at hp
  subst p
  exact Region.mk (o := i) hi rfl

private theorem events {c : X25519.Ctx} (hv : X25519.Valid c)
    (hc : CoreEvents layout c.base (E c)) :
    ∀ e ∈ trace layout c.base (E c) oChain,
      MidPc c e.pc ∧ ∀ y, Writes e.accesses y → X25519.WrOk c y := by
  intro e he
  simp only [trace,List.mem_append,List.mem_cons] at he
  rcases he with (h | h | h) | h
  · refine ⟨block_pc c (by decide) (by decide) (by decide) h,?_⟩
    intro y hy
    have hw := block_writes (off := parked) (by decide) (by decide +kernel) e h y hy
    rw [rebase] at hw
    exact .inl (Nat.lt_of_lt_of_le (work_region hv (subregion (by decide) hw)) (by decide))
  · subst e
    exact ⟨middle c (off := callSite oChain) (n := 1) (by decide) (by decide) 0 (by decide),
      fun y h => absurd h (writes_nil y)⟩
  · obtain ⟨hp,hw⟩ := hc e h
    exact ⟨.inr (.inr (Nat.lt_of_lt_of_le hp (by decide))),fun y hy =>
      .inl (Nat.lt_of_lt_of_le (work_region hv (Nat.lt_of_lt_of_le (hw y hy) (by decide))) (by decide))⟩
  · refine ⟨block_pc c (by decide) (by decide) (by decide) h,?_⟩
    intro y hy
    have hw := block_writes (off := borrowed+sX2) (by decide) (by decide +kernel) e h y hy
    exact .inl (Nat.lt_of_lt_of_le (work_region hv (subregion (by decide) hw)) (by decide))

/-- The linked inversion and its wrapper preserve the X25519 frame invariant and parked field value. -/
theorem inversion_w {c : X25519.Ctx} (hv : X25519.Valid c) {m : M0Crypto.Armv6M.Mem} {s : State}
    (hC : CodeAt m c.base B) (hPc : s.pc = c.base+BitVec.ofNat 32 oChain) (hB : Body c m s)
    {Q : State → Prop}
    (k : ∀ t, t.pc = c.base+BitVec.ofNat 32 oFinish → Body c m t →
      ModP (env c t.mem sZ2) (env c s.mem sZ2 ^ (2^255-21)) →
      env c t.mem sX2 = env c s.mem sX2 →
      (∀ y, Region (slotAt c lvOut) 4 y → t.mem y = s.mem y) →
      ReachW c.base (MidPc c) (X25519.WrOk c) t Q) :
    ReachW c.base (MidPc c) (X25519.WrOk c) s Q := by
  have hLink : Linked B oChain (layout.first+layout.start) := linked_of_body X25519EntrySeg.inversion_seg
  obtain ⟨t,hr,hpc,hDone,hEvents⟩ := run checked hLink (by decide +kernel) (pre hv hC hPc hB)
  have hs : s.sp = E c := hB.sp
  have he := events hv (hs ▸ hEvents)
  rw [← hs] at he
  refine ReachS.bind ⟨_,t,_,hr,(stepsOk_events_iff hr).mpr he,?_⟩
  refine k t hpc ⟨hDone.sp.trans hs,?_⟩ ?_ ?_ ?_
  · intro y hy
    rw [hDone.outside y (fun i hi h => hy (work_region hv (Region.mk hi (by simpa only [hs] using h))))]
    exact hB.keep y hy
  · have h := hDone.inv
    rwa [hs] at h
  · have h := hDone.x2
    rw [hs] at h
    exact congrArg (fun n : Nat => (n : Int)) h
  · intro y hy
    refine hDone.outside y fun i hi h => pointer_outside hy (Region.mk hi ?_)
    simpa only [hs] using h

end M0Crypto.Release.X25519SafegcdEntry
