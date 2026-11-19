import SafegcdTermination.Bank
import M0Crypto.Release.Field25519Facts


namespace SafegcdTermination.FrameWords

open SafegcdRow
open SafegcdTermination.Bank
open SafegcdRow.BatchCode
open M0Crypto.Armv6M (State Mem read32 write32 read32_write32_same write32_other)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr read32_storeWords_same)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)

theorem store_read {m : Mem} {sp : Word} {dst i : Nat} {vs : List Word}
    (hi : i < vs.length) (hl : vs.length ≤ 2^28) :
    read32 (storeWords m (addr sp dst) vs) (addr sp (dst+4*i)) = vs[i] := by
  have h := read32_storeWords_same m (addr sp dst) vs i hi hl
  simpa only [addr, ofNat_add_assoc] using h

theorem store_read_outside {m : Mem} {sp : Word} {dst src : Nat} {vs : List Word}
    (hSrc : src+4 ≤ 2^32) (hDst : dst+4*vs.length ≤ 2^32)
    (hSep : src+4 ≤ dst ∨ dst+4*vs.length ≤ src) :
    read32 (storeWords m (addr sp dst) vs) (addr sp src) = read32 m (addr sp src) := by
  apply read32_congr
  intro j hj
  apply storeWords_other
  intro i k hi hk
  simp only [addr, ofNat_add_assoc]
  exact addr_sep sp (by omega) (by omega) (by omega)

theorem write_read_outside {m : Mem} {sp v : Word} {dst src : Nat}
    (hSrc : src+4 ≤ 2^32) (hDst : dst+4 ≤ 2^32)
    (hSep : src+4 ≤ dst ∨ dst+4 ≤ src) :
    read32 (write32 m (addr sp dst) v) (addr sp src) = read32 m (addr sp src) := by
  apply read32_congr
  intro j hj
  apply write32_other
  intro i hi
  simp only [addr, ofNat_add_assoc]
  exact addr_sep sp (by omega) (by omega) (by omega)

theorem store_frame {m : Mem} {sp : Word} {dst frame : Nat} {vs : List Word}
    (hDst : dst+4*vs.length ≤ frame) :
    WritesOnly m (storeWords m (addr sp dst) vs) sp frame := by
  intro a ha
  apply storeWords_other
  intro i k hi hk
  simp only [addr, ofNat_add_assoc]
  exact ha _ (by omega)

theorem write_frame {m : Mem} {sp v : Word} {dst frame : Nat} (h : dst+4 ≤ frame) :
    WritesOnly m (write32 m (addr sp dst) v) sp frame := by
  have hf : dst+4*[v].length ≤ frame := by simpa
  exact store_frame hf

theorem WritesOnly.trans {m m' m'' : Mem} {base : Word} {n : Nat}
    (h₁ : WritesOnly m m' base n) (h₂ : WritesOnly m' m'' base n) :
    WritesOnly m m'' base n := fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem restrict_frame {m m' : Mem} {sp : Word} {o n frame : Nat}
    (h : o+n ≤ frame) (hw : WritesOnly m m' (addr sp o) n) : WritesOnly m m' sp frame := by
  intro a ha
  apply hw
  intro i hi
  rw [addr, ofNat_add_assoc]
  exact ha _ (by omega)

theorem keep_word {m m' : Mem} {sp : Word} {dst n src : Nat}
    (hW : WritesOnly m m' (addr sp dst) n)
    (hSrc : src+4 ≤ 2^32) (hDst : dst+n ≤ 2^32)
    (hSep : src+4 ≤ dst ∨ dst+n ≤ src) :
    read32 m' (addr sp src) = read32 m (addr sp src) := by
  apply read32_congr
  intro i hi
  apply hW
  intro j hj
  simp only [addr, ofNat_add_assoc]
  exact addr_sep sp (by omega) (by omega) (by omega)

theorem keep_stack_word {s t : State} {dst n off : Nat}
    (h : t.sp = s.sp) (hw : WritesOnly s.mem t.mem (addr s.sp dst) n)
    (ho : off+4 ≤ 2^32) (hd : dst+n ≤ 2^32) (hs : off+4 ≤ dst ∨ dst+n ≤ off) :
    stackWord t off = stackWord s off := by
  unfold stackWord stackAddr
  rw [h]
  exact keep_word hw ho hd hs

theorem keep_field {s t : State} {dst n off : Nat}
    (h : t.sp = s.sp) (hw : WritesOnly s.mem t.mem (addr s.sp dst) n)
    (ho : off+32 ≤ 2^32) (hd : dst+n ≤ 2^32) (hs : off+32 ≤ dst ∨ dst+n ≤ off) :
    feVal t.mem (addr t.sp off) = feVal s.mem (addr s.sp off) := by
  rw [h]
  simp only [feVal_psum]
  apply psum_congr
  intro i hi
  simp only [slot_addr]
  obtain hs | hs := hs
  · exact congrArg BitVec.toNat (keep_word hw (by omega) hd (.inl (by omega)))
  · exact congrArg BitVec.toNat (keep_word hw (by omega) hd (.inr (by omega)))

end SafegcdTermination.FrameWords
