import M0Crypto.Release.Poly1305Mac
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
/-!
Arithmetic building blocks for refining the execution state. `mac4_v` connects
four actual MAC instruction lists to the register-width column expression. The
complete reduction and loop refinement are proved in `Poly1305Body` and `Poly1305Loop`.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Mac (mac narrow colend v64)

/-- High-register accumulator representation used throughout the loop. -/
def hval (s : State) : Nat := Poly1305Arith.val5 (s.regs 8).toNat (s.regs 9).toNat
  (s.regs 10).toNat (s.regs 11).toNat (s.regs 14).toNat

def cw (s : State) (j : Nat) : Nat := (read32 s.mem (slot (s.regs 7) j)).toNat

/-- Four wide products of a column. -/
def mac4 (a b c d : Nat) : List Instr := mac 8 (2*a) ++ mac 9 (2*b) ++ mac 10 (2*c) ++ mac 11 (2*d)

theorem mac_regs (s : State) (h : Reg) (k : Nat) (r : Reg) (hr : 7 ≤ r.val) (h15 : r.val ≠ 15) :
    (execAll (mac h k) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ h15
  simp [mac, Instr.dsts]; omega

theorem mac_cw (s : State) (h : Reg) (w : Nat) (hw : w < 15) :
    v64 (execAll (mac h (2*w)) s) = (v64 s + (s.regs h).toNat * cw s w) % 2^64 := by
  rw [Poly1305Mac.mac_v64 s h (2*w) (by omega)]
  simp only [show 2*(2*w) = 4*w by omega, show 2*(2*w)+2 = 4*w+2 by omega]
  rw [← ofNat_add_assoc, show BitVec.ofNat 32 2 = 2#32 from rfl, Poly1305Mac.read16_pair]
  rfl

theorem mac4_mem (s : State) (a b c d : Nat) : (execAll (mac4 a b c d) s).mem = s.mem := by
  exact execAll_mem _ _ (by simp [mac4, List.all_append, Poly1305Mac.mac_noW])

theorem mac4_regs (s : State) (a b c d : Nat) (r : Reg) (hr : 7 ≤ r.val) (h15 : r.val ≠ 15) :
    (execAll (mac4 a b c d) s).regs r = s.regs r := by
  simp only [mac4, execAll_append]
  repeat rw [mac_regs _ _ _ r hr h15]

theorem mac4_v (s : State) (a b c d : Nat) (ha : a < 15) (hb : b < 15) (hc : c < 15) (hd : d < 15) :
    v64 (execAll (mac4 a b c d) s) =
      (((((v64 s + (s.regs 8).toNat * cw s a) % 2^64 + (s.regs 9).toNat * cw s b) % 2^64 +
        (s.regs 10).toNat * cw s c) % 2^64 + (s.regs 11).toNat * cw s d) % 2^64) := by
  simp only [mac4, execAll_append]
  rw [mac_cw _ 11 d hd, mac_cw _ 10 c hc, mac_cw _ 9 b hb, mac_cw _ 8 a ha]
  simp only [cw, execAll_mem _ _ (Poly1305Mac.mac_noW _ _), mac_regs _ _ _ 7 (by decide) (by decide),
    mac_regs _ _ _ 9 (by decide) (by decide), mac_regs _ _ _ 10 (by decide) (by decide),
    mac_regs _ _ _ 11 (by decide) (by decide)]

end M0Crypto.Release.Poly1305Blocks
