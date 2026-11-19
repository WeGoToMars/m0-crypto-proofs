import M0Crypto.Release.Ed25519CallProgSound

/-!
# Call programs: public blocks are sound

`pubEval_sound`: a public block run from registers that hold `σ` and memory whose word views hold
leaves the memory, its registers holding the block's `σ`, and its known flags. The proof is the
symbolic executor's soundness (`Sym.symExec_sound`) and the soundness of the evaluation of syntax
(`exSv_sound`, `flBv_sound`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Sym (SExpr SBool SMem SState symExec)

section
variable {c : Ctx} {sp : Word} {σ : List (Reg × SV)} {Γ : List (Loc × Kd)} {t : State}

theorem kOf_val (w : Word) : (kOf w).val c sp = w := by simp [kOf, SV.val]

theorem kw_val {a : SV} {x : Word} (h : a.kw = some x) : a.val c sp = x := by
  cases a <;> simp [SV.kw] at h; subst h; rfl

theorem svK2_val {f : Word → Word → Word} {a b : Option SV} {v : SV} (h : svK2 f a b = some v)
    {x y : Word} (ha : ∀ u, a = some u → x = u.val c sp) (hb : ∀ u, b = some u → y = u.val c sp) :
    v.val c sp = f x y := by
  cases a with
  | none => simp [svK2] at h
  | some a =>
  cases b with
  | none => simp [svK2] at h
  | some b =>
  simp only [svK2] at h
  cases hx : a.kw <;> cases hy : b.kw <;> simp [hx, hy] at h
  subst h
  rw [kOf_val, ← kw_val hx, ← kw_val hy, ← ha a rfl, ← hb b rfl]

theorem addK_val {a v : SV} {n : Nat} (h : a.addK n = some v) : v.val c sp = a.val c sp + BitVec.ofNat 32 n := by
  cases a <;> simp [SV.addK] at h <;> subst h <;> simp [SV.val, BitVec.ofNat_add, BitVec.add_assoc]

theorem kw_bind_val {o : Option SV} {x : Word} (h : o.bind SV.kw = some x) {y : Word}
    (hv : ∀ u, o = some u → y = u.val c sp) : y = x := by
  cases o with
  | none => simp at h
  | some u => simp only [Option.bind_some] at h; rw [← kw_val (c := c) (sp := sp) h, hv u rfl]

variable (hσ : Holds c sp σ t.regs)
  (hΓ : ∀ o v, pwAt Γ o = some v → read32 t.mem (sp + BitVec.ofNat 32 o) = v.val c sp)
include hσ hΓ

/-- **The evaluation of syntax is sound**: a public value of syntax is its value at `t`. -/
theorem exSv_sound : ∀ (e : SExpr) (v : SV), exSv σ Γ e = some v → e.denote t = v.val c sp
  | .reg0 r, v, h => by
    simp only [exSv] at h; exact (hσ.get h).1
  | .const w, v, h => by simp only [exSv, Option.some.injEq] at h; subst h; rw [kOf_val]; rfl
  | .add a b, v, h => by
    simp only [exSv] at h
    simp only [SExpr.denote]; rw [svK2_val h (exSv_sound a) (exSv_sound b)]
  | .sub a b, v, h => by
    simp only [exSv] at h
    simp only [SExpr.denote]; rw [svK2_val h (exSv_sound a) (exSv_sound b)]
  | .and a b, v, h => by
    simp only [exSv] at h
    simp only [SExpr.denote]; rw [svK2_val h (exSv_sound a) (exSv_sound b)]
  | .or a b, v, h => by
    simp only [exSv] at h
    simp only [SExpr.denote]; rw [svK2_val h (exSv_sound a) (exSv_sound b)]
  | .xor a b, v, h => by
    simp only [exSv] at h
    simp only [SExpr.denote]; rw [svK2_val h (exSv_sound a) (exSv_sound b)]
  | .not a, v, h => by
    simp only [exSv] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [SExpr.denote, kOf_val, kw_bind_val hx (exSv_sound a)]
  | .lsl a n, v, h => by
    simp only [exSv] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [SExpr.denote, kOf_val, kw_bind_val hx (exSv_sound a)]
  | .lsr a n, v, h => by
    simp only [exSv] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [SExpr.denote, kOf_val, kw_bind_val hx (exSv_sound a)]
  | .awc a b c, v, h => by
    simp only [exSv] at h
    cases c with
    | const cin =>
      cases ha : exSv σ Γ a with
      | none => simp [ha, awcSv] at h
      | some x =>
      cases hb : exSv σ Γ b with
      | none => simp [ha, hb, awcSv] at h
      | some y =>
      have ea := exSv_sound a x ha
      have eb := exSv_sound b y hb
      simp only [ha, hb, awcSv] at h
      cases hx : x.kw <;> cases hy : y.kw <;> simp only [hx, hy] at h
      · simp at h
      · cases cin <;> simp at h
        simp only [SExpr.denote, SBool.denote, M0Crypto.Proofs.addWithCarry_fst, ea, eb, addK_val h,
          kw_val hy, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · cases cin <;> simp at h
        simp only [SExpr.denote, SBool.denote, M0Crypto.Proofs.addWithCarry_fst, ea, eb, addK_val h,
          kw_val hx, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
      · simp only [Option.some.injEq] at h; subst h
        rw [kOf_val]; simp only [SExpr.denote, SBool.denote, ea, eb, kw_val hx, kw_val hy]
    | _ => simp [awcSv] at h
  | .ld32 m a, v, h => by
    simp only [exSv] at h
    unfold ld32Sv at h
    split at h
    · rename_i w
      split at h
      · rename_i h13
        have h13' : t.regs 13 = sp := by rw [(hσ.get h13).1]; simp [SV.val]
        have := hΓ _ _ h
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
        simp only [SExpr.denote, SMem.denote, h13']; exact this
      · simp at h
    · simp at h
  | .mul _ _, _, h | .uxth _, _, h | .ror _ _ _, _, h | .lslR _ _ _, _, h | .lsrR _ _ _, _, h
  | .asr _ _, _, h | .rev _, _, h | .ld16 _ _, _, h | .ld8 _ _, _, h | .rotl _ _, _, h => by
    simp [exSv] at h

/-- **The evaluation of a flag is sound.** -/
theorem flBv_sound (b : SBool) (x : Bool) (h : flBv σ Γ b = some x) : b.denote t = x := by
  have e2 : ∀ a b, ∀ {x y : Word}, (exSv σ Γ a).bind SV.kw = some x → (exSv σ Γ b).bind SV.kw = some y →
      SExpr.denote t a = x ∧ SExpr.denote t b = y := fun a b _ _ ha hb =>
    ⟨kw_bind_val ha (exSv_sound hσ hΓ a), kw_bind_val hb (exSv_sound hσ hΓ b)⟩
  cases b with
  | const b => simp only [flBv, Option.some.injEq] at h; exact h
  | msb a =>
    simp only [flBv] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [SBool.denote, kw_bind_val hw (exSv_sound hσ hΓ a)]
  | isZero a =>
    simp only [flBv] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [SBool.denote, kw_bind_val hw (exSv_sound hσ hΓ a)]
  | awcC a b c =>
    cases c with
    | const cin =>
      simp only [flBv] at h
      cases ha : (exSv σ Γ a).bind SV.kw <;> cases hb : (exSv σ Γ b).bind SV.kw <;> simp [ha, hb] at h
      subst h
      obtain ⟨e1, e2⟩ := e2 a b ha hb
      simp only [SBool.denote, e1, e2]
    | _ => simp [flBv] at h
  | awcV a b c =>
    cases c with
    | const cin =>
      simp only [flBv] at h
      cases ha : (exSv σ Γ a).bind SV.kw <;> cases hb : (exSv σ Γ b).bind SV.kw <;> simp [ha, hb] at h
      subst h
      obtain ⟨e1, e2⟩ := e2 a b ha hb
      simp only [SBool.denote, e1, e2]
    | _ => simp [flBv] at h
  | _ => simp [flBv] at h

/-- **A public block is sound**: memory stays, the registers hold its `σ`, its known flags hold. -/
theorem pubEval_sound {g : List Instr} {r : PubR} (h : pubEval σ Γ g = some r) (hf : g.all Instr.falls = true) :
    (execAll g t).mem = t.mem ∧ Holds c sp r.σ (execAll g t).regs ∧
      (∀ b, r.n = some b → (execAll g t).n = b) ∧ (∀ b, r.z = some b → (execAll g t).z = b) ∧
      (∀ b, r.c = some b → (execAll g t).c = b) ∧ (∀ b, r.v = some b → (execAll g t).v = b) := by
  simp only [pubEval] at h
  split at h
  · rename_i hm
    simp only [Option.some.injEq] at h; subst h
    have hs := M0Crypto.Sym.symExec_sound g (M0Crypto.Sym.sound_all hf) t SState.init
    rw [SState.init_denote] at hs
    rw [← hs]
    refine ⟨?_, fun p hp => ?_, fun b hb => flBv_sound hσ hΓ _ _ hb, fun b hb => flBv_sound hσ hΓ _ _ hb,
      fun b hb => flBv_sound hσ hΓ _ _ hb, fun b hb => flBv_sound hσ hΓ _ _ hb⟩
    · simp only [SState.denote]
      cases hmm : (symExec g SState.init).mem <;> simp [hmm, isMem0] at hm
      rfl
    · obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hqp
      refine ⟨(show ∀ q ∈ pubRegs, q.val < 14 by decide) q hq, ?_⟩
      exact exSv_sound hσ hΓ _ _ hv
  · simp at h

end

end M0Crypto.Release.Ed25519CallProg
