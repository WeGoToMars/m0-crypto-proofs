import M0Crypto.Release.ConstantTime.ChaCha20Entry
import M0Crypto.Release.ConstantTime.AeadEncryptEntry
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-!
# Certificates for the three entry points

For each entry the analysis runs at build time (`ct_cert%`) and the kernel checks the
resulting certificate with `certOk` (`decide +kernel`). The statements fix what the
trace-equality proof relies on:

* the stack window: `[sp0 - stackBytes, sp0 + 4 * argWords)`, using the bound constants
  of `TraceSpec` and the number of stack arguments of the entry;
* the entry state: r0–r3 and the stack arguments public, LR the entry LR, every other
  register and every other stack slot secret, no flag information;
* for decryption, the declassified branch `Aead.decRejectBrAt`.

Cost (`set_option profiler true`, one development machine): kernel type checking 1.2 s
(ChaCha), 10.7 s (encrypt), 23.3 s (decrypt); interpreted generation about 25 s for each
AEAD entry. Budget: 60 s of kernel time per entry. Each entry has its own file
(`ChaCha20Entry`, `AeadEncryptEntry`, `AeadDecryptEntry`) so the three checks build in parallel.
-/
