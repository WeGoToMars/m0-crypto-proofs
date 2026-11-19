import M0Crypto.Release.Ed25519Tables

/-!
The constants and tables of the `fast` build hold the specification's values (`TablesOk`), by
kernel evaluation, one declaration per table.
-/

namespace M0Crypto.Release.Ed25519TablesFast

open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519Tables
open M0Crypto.Artifacts.Ed25519Compact (ed_zero ed_one ed_d ed_d2 ed_sqrtm1 ed_mu ed_l9 sha512_K
  sha512_IV ed_odd_b ed_comb)

theorem fe : [ed_zero, ed_one, ed_d, ed_d2, ed_sqrtm1].map
    (fun o => leVal 32 (Build.fast.bytes.drop o)) = feConsts := by
  rw [← feConstsFast_eq]; decide +kernel

theorem sc : [ed_mu, ed_l9].map (fun o => leVal 36 (Build.fast.bytes.drop o)) = scConsts := by
  decide +kernel

theorem k : leVals 8 80 (Build.fast.bytes.drop sha512_K) = shaK := by decide +kernel

theorem iv : leVals 8 8 (Build.fast.bytes.drop sha512_IV) = shaIV := by decide +kernel

theorem odd : leVals 32 24 (Build.fast.bytes.drop ed_odd_b) = oddTable := by
  rw [← oddFast_eq]; decide +kernel

theorem comb : leVals 32 (24 * Build.fast.combs) (Build.fast.bytes.drop ed_comb) =
    combTable Build.fast.combs := by
  rw [← combFast_eq (by decide +kernel)]; decide +kernel

theorem tables_ok : TablesOk Build.fast := ⟨fe, sc, k, iv, odd, comb, by decide +kernel⟩

end M0Crypto.Release.Ed25519TablesFast
