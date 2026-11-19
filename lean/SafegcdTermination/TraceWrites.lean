import SafegcdTermination.PublicTrace
import M0Crypto.Release.FrameBase

namespace SafegcdTermination.TraceWrites

open M0Crypto.Armv6M (State Reg Word)
open M0Crypto.Thumb M0Crypto.Sym
open M0Crypto.Release (Region WritesTo)
open M0Crypto.Release.Frame (Disj ne_of_disj)

set_option linter.unusedSimpArgs false

theorem byCheck {is : List Instr} {s : State} {rs : List (Reg × Word × Nat)} {W : Word → Prop}
    (hf : is.all Instr.falls = true) (hw : writeChk rs is = true)
    (h : ∀ p ∈ rs, ∀ o < p.2.2, W (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o)) :
    WritesTo W (traceAll is s) := by
  intro e he y hy
  obtain ⟨p,hp,o,ho,rfl⟩ := writeChk_sound rs is (sound_all hf) s hw e he y hy
  exact h p hp o ho

theorem frame {is : List Instr} {s : State} {r : Reg} {n : Nat}
    (hf : is.all Instr.falls = true) (hw : writeChk [(r,0,n)] is = true) :
    WritesTo (Region (s.regs r) n) (traceAll is s) := by
  refine byCheck (s := s) (W := Region (s.regs r) n) hf hw ?_
  intro q hq o ho
  rw [List.mem_singleton] at hq
  subst q
  apply Region.mk ho
  simp

theorem quiet {is : List Instr} {s : State} {W : Word → Prop}
    (hf : is.all Instr.falls = true) (hw : writeChk [] is = true) :
    WritesTo W (traceAll is s) :=
  byCheck hf hw (fun _ h _ _ => False.elim (List.not_mem_nil h))

theorem event {e : Event} {W : Word → Prop} (h : e.accesses = []) : WritesTo W [e] := by
  intro f hf x hx
  rw [List.mem_singleton] at hf
  subst f
  rw [h] at hx
  obtain ⟨a,ha,_⟩ := hx
  contradiction

theorem branch (pc : Word) (i : Instr) {W : Word → Prop} : WritesTo W [⟨pc,i,[]⟩] :=
  event rfl

theorem subregion {sp : Word} {n off m : Nat} {a : Word} (h : off+m ≤ n)
    (hr : Region (sp+BitVec.ofNat 32 off) m a) : Region sp n a := by
  obtain ⟨j,hj,rfl⟩ := hr.exists
  exact Region.mk (o := off+j) (by omega) (by rw [ofNat_add_assoc])

theorem noCode {code : List (BitVec 8)} {base sp dst : Word} {n m : Nat} {tr : List Event}
    (hs : Disj base code.length sp n) (hd : Disj base code.length dst m)
    (h : WritesTo (fun a => Region sp n a ∨ Region dst m a) tr) : TraceMissesCode code base tr := by
  intro e he i hi hew
  obtain hw | hw := h e he _ hew
  · obtain ⟨j,hj,hex⟩ := hw.exists
    exact ne_of_disj hs.1 hs.2.1 hs.2.2 hi hj hex
  · obtain ⟨j,hj,hex⟩ := hw.exists
    exact ne_of_disj hd.1 hd.2.1 hd.2.2 hi hj hex

end SafegcdTermination.TraceWrites
