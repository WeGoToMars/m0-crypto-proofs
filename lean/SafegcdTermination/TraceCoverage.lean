import SafegcdTermination.EndFootprint
import M0Crypto.Release.StackEffectGP

namespace SafegcdTermination.TraceCoverage

open SafegcdTermination.FinalCode SafegcdTermination.FinalSelect
open SafegcdTermination.Leaf (callTrace leafTrace)
open SafegcdTermination.PublicTrace (publicState)
open SafegcdRow (nextPC)
open SafegcdRow.BatchCode (bankE callTo)
open SafegcdTermination.Bank (addr)
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb M0Crypto.Sym M0Crypto.Release M0Crypto.Release.StackEffect

/-- Each byte in the given region has a write event in the trace. -/
def Covers (W : Word → Prop) (tr : List Event) : Prop :=
  ∀ y, W y → ∃ e ∈ tr, Writes e.accesses y

theorem Covers.append_left {W : Word → Prop} {a b : List Event} (h : Covers W a) :
    Covers W (a ++ b) := by
  intro y hy
  obtain ⟨e, he, hw⟩ := h y hy
  exact ⟨e, List.mem_append_left b he, hw⟩

theorem Covers.append_right {W : Word → Prop} {a b : List Event} (h : Covers W b) :
    Covers W (a ++ b) := by
  intro y hy
  obtain ⟨e, he, hw⟩ := h y hy
  exact ⟨e, List.mem_append_right a he, hw⟩

theorem Covers.mono {W W' : Word → Prop} {tr : List Event} (h : Covers W tr)
    (hW : ∀ y, W' y → W y) : Covers W' tr := fun y hy => h y (hW y hy)

theorem covers_block {is : List Instr} {wo : List (SExpr × Nat)} (hF : is.all Instr.falls = true)
    (h : covChk wo is = true) (s : State) : Covers (InR s wo) (traceAll is s) := by
  have hT := symTrace_sound is (sound_all hF) s SState.init
  rw [SState.init_denote] at hT
  rw [← hT]
  intro y ⟨r, hr, o, ho, hy⟩
  have hByte := List.all_eq_true.mp (List.all_eq_true.mp h r hr) o (List.mem_range.mpr ho)
  obtain ⟨x, hx, hxi⟩ := List.any_eq_true.mp hByte
  obtain ⟨se, hs, hW⟩ := List.mem_flatMap.mp hx
  obtain ⟨o', ho', ha⟩ := inRgnOff_den (spl_denote s) hxi
  have hIn : InRD (·.denote s) (wrsOf se.2.2) y :=
    ⟨x, hW, o', ho', hy.trans ha⟩
  exact ⟨_, List.mem_map.mpr ⟨se, hs, rfl⟩, inR_wrs.mp hIn⟩

private theorem pick_covers (base sp dst : Word) (off select : Nat) :
    Covers (Region dst 32) (pickTrace base sp dst off select) := by
  let pc := base + BitVec.ofNat 32 select
  let entry := publicState [(15,pc),(0,dst),(1,sp),(2,addr sp bankE)]
  have h : Covers (Region dst 32) (traceAll selectBody entry) := by
    apply (covers_block (wo := [(.reg0 0, 32)]) (by decide) (by decide +kernel) entry).mono
    intro y hy
    obtain ⟨o, ho, rfl⟩ := hy.exists
    exact ⟨_, List.mem_singleton_self _, o, ho, rfl⟩
  exact (h.append_left (b := [⟨nextPC pc selectBody,.bx 14,[]⟩])).append_right
    (a := [⟨base + BitVec.ofNat 32 off,callTo off select,[]⟩])

theorem final_output {q : SafegcdRow.BatchCode.Targets} {base sp dst : Word}
    {done sub select : Nat} :
    Covers (Region dst 32) (RunFinal.finalTrace q base sp dst done sub select) := by
  unfold RunFinal.finalTrace selectTrace
  simp only [List.append_assoc]
  apply Covers.append_right
  apply Covers.append_right
  apply Covers.append_right
  apply Covers.append_right
  apply Covers.append_right
  exact (pick_covers _ _ _ _ _).append_left

theorem output {q : SafegcdRow.BatchCode.Targets} {base sp dst src : Word}
    {start canon loop done sub select : Nat} :
    Covers (Region dst 32) (Invert.inversionTrace q base sp dst src start canon loop done sub select) :=
  final_output.append_right

end SafegcdTermination.TraceCoverage
