import SafegcdTermination.TraceCoverage

namespace SafegcdTermination.InitStackEffect

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank (addr)
open SafegcdTermination.InitCode SafegcdTermination.RunInit SafegcdTermination.ClearLoop
open SafegcdTermination.Leaf (callTrace leafTrace)
open SafegcdTermination.PublicTrace (stackState publicState)
open SafegcdTermination.TraceWrites (subregion)
open M0Crypto.Armv6M (Reg State)
open M0Crypto.Thumb M0Crypto.Sym M0Crypto.Release M0Crypto.Release.TraceSpec
open M0Crypto.Release.StackEffect

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

/-- The caller's trace window bounds the accesses to these bytes at the
    inversion's working SP. -/
abbrev Above (sp0 : Word) (n : Nat) (sp : Word) (R : Word → Prop) :=
  ∀ y, R y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y

def SavedPtrs (sp : Word) (y : Word) : Prop :=
  Region (addr sp outputAt) 4 y ∨ Region (addr sp returnAt) 4 y

def CounterWords (sp : Word) (y : Word) : Prop :=
  Region (addr sp deltaAt) 4 y ∨ Region (addr sp counterAt) 4 y

abbrev InitialBanks (sp : Word) := Region sp (4 * vectorBytes)
abbrev CanonicalInput (sp : Word) := Region (addr sp temp) 32

/-- Bytes definitely initialized when control first reaches the batch loop. -/
def Initialized (sp : Word) (y : Word) : Prop :=
  SavedPtrs sp y ∨ CanonicalInput sp y ∨ InitialBanks sp y ∨ CounterWords sp y

variable {sp0 sp : Word} {n : Nat}

theorem no_region {s : State} {y : Word} (h : InR s [] y) : False := by
  obtain ⟨_,hr,_⟩ := h
  exact List.not_mem_nil hr

theorem quiet {e : Event} {X : Word → Prop}
    (hSp : (!(e.instr.dsts.contains 13)) = true) (hAcc : e.accesses = []) :
    Seg sp0 n sp X [e] (fun _ => False) := by
  obtain ⟨hs,hx⟩ := keep_sp hSp sp
  exact (ev_seg hx hs (fun _ hy _ => absurd (hAcc ▸ hy) acc_nil)
    (fun y hy _ => absurd (hAcc ▸ hy) (M0Crypto.Release.reads_nil y))).mono
      (fun _ h => h) (fun _ h => False.elim h)

/-- Resolve SP-relative symbolic ranges directly in the state that defines a
    public trace block. -/
theorem stack_regions {pc sp y : Word} {l : List (Nat × Nat)} :
    InR (stackState pc sp) (spRg l) y ↔ ∃ r ∈ l, Region (addr sp r.1) r.2 y := by
  constructor
  · rintro ⟨r,hr,o,ho,he⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact ⟨p,hp,Region.mk ho he⟩
  · rintro ⟨p,hp,hr⟩
    obtain ⟨o,ho,rfl⟩ := hr.exists
    exact ⟨_,List.mem_map.mpr ⟨p,hp,rfl⟩,o,ho,rfl⟩

theorem stack_region_bound {pc sp y : Word} {l : List (Nat × Nat)} {N : Nat}
    (hc : (l.all fun p => decide (p.1 + p.2 ≤ N)) = true)
    (h : InR (stackState pc sp) (spRg l) y) : Region sp N y := by
  obtain ⟨r,hr,hy⟩ := stack_regions.mp h
  exact subregion (of_decide_eq_true (List.all_eq_true.mp hc r hr)) hy

private theorem save (pc : Word) {X : Word → Prop}
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp X (traceAll saveAndCall (stackState pc sp)) (SavedPtrs sp) := by
  let rs := [(outputAt,4),(returnAt,4)]
  apply (blk_seg (ini := []) (wo := spRg rs) (fp := spRg rs) (by decide +kernel)
    (stackState pc sp) (X := X) (fun _ h => False.elim (no_region h))
    (fun y hy => hA y (stack_region_bound (by decide) hy))).mono (fun _ h => h)
  intro y hy
  rcases hy with h | h
  · exact stack_regions.mpr ⟨_,List.mem_cons_self,h⟩
  · exact stack_regions.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),h⟩

private theorem canon (base src : Word) (off dest : Nat)
    (hA : Above sp0 n sp (fun y => Region sp frameBytes y ∨ Region src 32 y)) :
    let s := publicState [(15,base+BitVec.ofNat 32 dest),(0,addr sp temp),(1,src)]
    Seg sp0 n sp (Region src 32) (callTrace canonBody base off dest s) (CanonicalInput sp) := by
  let pc := base+BitVec.ofNat 32 dest
  let s := publicState [(15,pc),(0,addr sp temp),(1,src)]
  have hOut : ∀ y, CanonicalInput sp y → InR s [(.reg0 0,32)] y :=
    fun _ h => inR_one h
  have hCore : Seg sp0 n sp (Region src 32) (traceAll canonBody s) (CanonicalInput sp) := by
    apply (blk_seg (ini := [(.reg0 1,32)]) (wo := [(.reg0 0,32)])
      (fp := [(.reg0 0,32),(.reg0 1,32)]) (by decide +kernel) s (X := Region src 32) ?_ ?_).mono
      (fun _ h => h) hOut
    · intro y ⟨r,hr,o,ho,he⟩
      have e := List.mem_singleton.mp hr
      subst r
      exact Region.mk ho he
    · intro y ⟨r,hr,o,ho,he⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hA y (.inl (subregion (by decide : temp+32 ≤ frameBytes) (Region.mk ho he)))
      · exact hA y (.inr (Region.mk ho he))
  have hCall : Seg sp0 n sp (Region src 32)
      [⟨base+BitVec.ofNat 32 off,callTo off dest,[]⟩] (fun _ => False) :=
    quiet (by rfl) rfl
  have hRet : Seg sp0 n sp (Region src 32)
      [⟨nextPC pc canonBody,.bx 14,[]⟩] (fun _ => False) :=
    quiet (by rfl) rfl
  exact (hCall.cat (hCore.cat hRet)).mono (fun _ h => h)
    (fun _ h => .inr (.inl h))

private theorem clear_step (base a : Word) (off : Nat) {X : Word → Prop}
    (hA : Above sp0 n sp (Region a 16)) :
    Seg sp0 n sp X (clearStepTrace base off a) (Region a 16) := by
  let s := publicState [(15,base+BitVec.ofNat 32 off),(0,a)]
  have hBlock : Seg sp0 n sp X (traceAll clearBlock s) (Region a 16) := by
    apply (blk_seg (ini := []) (wo := [(.reg0 0,16)]) (fp := [(.reg0 0,16)])
      (by decide +kernel) s (X := X) (fun _ h => False.elim (no_region h)) ?_).mono
      (fun _ h => h) (fun _ h => inR_one h)
    intro y ⟨r,hr,o,ho,he⟩
    have e := List.mem_singleton.mp hr
    subst r
    exact hA y (Region.mk ho he)
  exact (hBlock.cat (quiet (e := ⟨_,clearBranch,[]⟩) (by rfl) rfl)).mono
    (fun _ h => h) (fun _ h => .inl h)

private theorem clear (base a : Word) (off k : Nat) {X : Word → Prop}
    (hA : Above sp0 n sp (Region a (16*k))) :
    Seg sp0 n sp X (clearTrace base off a k) (Region a (16*k)) := by
  induction k generalizing a with
  | zero =>
    intro q hs hu _
    exact ⟨trivial, hs, fun _ h => h, fun y h => False.elim (by
      have h' : (y-a).toNat < 0 := h
      omega)⟩
  | succ k ih =>
    have hS := clear_step base a off (X := X) (fun y hy =>
      hA y (Nat.lt_of_lt_of_le hy (by omega : 16 ≤ 16*(k+1))))
    have hC := ih (a+16#32) (fun y hy =>
      hA y (subregion (by omega : 16+16*k ≤ 16*(k+1)) hy))
    exact (hS.cat hC).mono (fun _ h => h) (fun y hy => by
      have hE : 16*(k+1) = 16+16*k := by omega
      exact reg_split (hE ▸ hy))

private theorem tail_effect (pc : Word)
    (hA : Above sp0 n sp (Region sp frameBytes)) :
    Seg sp0 n sp (CanonicalInput sp) (traceAll InitCode.tail (stackState pc sp)) (CounterWords sp) := by
  let rs := [(deltaAt,4),(counterAt,4)]
  have hRead : ∀ y, InR (stackState pc sp) (spRg [(temp,32)]) y → CanonicalInput sp y := by
    intro y hy
    obtain ⟨p,h,hr⟩ := stack_regions.mp hy
    rw [List.mem_singleton] at h
    subst p
    exact hr
  have hWrite : ∀ y, CounterWords sp y → InR (stackState pc sp) (spRg rs) y := by
    intro y hy
    rcases hy with h | h
    · exact stack_regions.mpr ⟨_,List.mem_cons_self,h⟩
    · exact stack_regions.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),h⟩
  exact (blk_seg (ini := spRg [(temp,32)]) (wo := spRg rs) (fp := spRg [(0,frameBytes)])
    (by decide +kernel) (stackState pc sp) (X := CanonicalInput sp) hRead
    (fun y hy => hA y (stack_region_bound (by decide) hy))).mono (fun _ h => h) hWrite

theorem init (base src : Word) (start dest : Nat)
    (hA : Above sp0 n sp (fun y => Region sp frameBytes y ∨ Region src 32 y)) :
    Seg sp0 n sp (Region src 32) (initTrace base sp src start dest) (Initialized sp) := by
  have hF : Above sp0 n sp (Region sp frameBytes) := fun y h => hA y (.inl h)
  have hS := save (sp0 := sp0) (X := Region src 32) (base+BitVec.ofNat 32 start) hF
  have hCan := canon base src (canonSite start) dest hA
  let pc := base+BitVec.ofNat 32 (setupSite start)
  have hSetup : Seg sp0 n sp (Region src 32) (traceAll clearSetup (stackState pc sp))
      (fun _ => False) :=
    (blk_seg (ini := []) (wo := []) (fp := []) (by decide +kernel) (stackState pc sp)
      (X := Region src 32) (fun _ h => False.elim (no_region h))
      (fun _ h => False.elim (no_region h))).mono (fun _ h => h) (fun _ h => False.elim h)
  have hC := clear (sp0 := sp0) (X := Region src 32) base sp (clearSite start) clearIterations
    (fun y hy => hF y (Nat.lt_of_lt_of_le hy (by decide : 16*clearIterations ≤ frameBytes)))
  have hTail := tail_effect (base+BitVec.ofNat 32 (tailSite start)) hF
  exact ((((hS.cat hCan).cat hSetup).cat hC).append
    (hTail.mono (fun _ h => .inr (.inl (.inl (.inr h)))) (fun _ h => h))).mono
      (fun _ h => h) (fun y hy => by
        rcases hy with h | h | h | h
        · exact .inl (.inl (.inl (.inl h)))
        · exact .inl (.inl (.inl (.inr h)))
        · exact .inl (.inr h)
        · exact .inr h)

end SafegcdTermination.InitStackEffect
