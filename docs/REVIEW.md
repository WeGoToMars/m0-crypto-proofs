# Reviewing the m0-crypto proofs: ChaCha20-Poly1305 and the ARMv6-M model

This guide lists exactly which parts of the Lean code a person has to read to trust the proofs of ChaCha20, Poly1305 and the ChaCha20-Poly1305 AEAD, which document each part must be checked against, and how to keep that true as the proofs change. It assumes no background in formal verification.

**Scope.** This guide describes the proofs of library 0.2.0: release artifact 3,030 bytes, sha256 `b85f137f8356ea1d290578ce03616b3e00cff08aac7cc1104b3e9fdadfc990d3`. It is written for the commit it is part of. The lists in section 3 are the output of [`tools/trusted_defs.lean`](../tools/trusted_defs.lean), which computes them from the theorem statements themselves (section 6).

**Release assets.** ChaCha20-Poly1305, BLAKE2s and X25519 are released and verified separately. Each is its own relocation-free object (`m0crypto_chacha20poly1305.o`, `m0crypto_blake2s.o`, `m0crypto_x25519.o`) with its own Lake workspace `assets/ASSET`. The workspace compiles the shared sources in `lean/` against that asset's artifact, `assets/ASSET/artifact/M0Crypto/Artifacts/Release.lean`. It holds the asset's `Audit.lean`, `expected-axioms.txt` and `statements.golden`. In an asset's theorems, `Artifacts.Release` (and its abbreviation `B`) is that asset's `.text`. Sections 2 to 8 cover the ChaCha20-Poly1305 asset. Section 9 covers X25519. The model, decoder and shared statement vocabulary are the same source files in every asset.

## 1. What a proof gives you, and what it does not

A Lean theorem has two parts: a **statement** (what is claimed) and a **proof** (why it holds). Lean's kernel checks every proof mechanically, so you never need to read a proof to know it is valid. That is the whole point: of about 43,000 lines of Lean, 890 hand-written lines in 11 files are trusted. 790 of them need a careful human reading. The other 100 are the instruction decoding functions, which are compared with LLVM on every instruction of the code instead (section 3.2).

What you *do* have to read is the statement, and every definition the statement mentions, recursively. Together these are the **trusted base**. If a definition in the trusted base is wrong, the theorem can be proved and still say something other than what you think.

A fully checked proof can still mislead in six ways. Each has a defence in this repository:

| # | Failure | Example | Defence | Where |
|---|---|---|---|---|
| 1 | The **specification** is wrong | A wrong index in a diagonal round of `Spec/ChaCha20.lean`. The code is "proved" equal to a wrong cipher. | Read the spec against the RFC; the spec is run on RFC, Wycheproof and pyca/cryptography vectors. | 3.4 |
| 2 | The **machine model** is wrong | `adcs` computes the carry incorrectly. Proofs about the model then say nothing about the chip. | Read the model against the ARM manual; decoder compared with LLVM; model compared with QEMU after every instruction. | 3.1, 3.2 |
| 3 | The **statement is weaker than you think** | A precondition no real call can satisfy (the theorem is then *vacuous*: true but useless); a secret listed as public; a read region that allows everything. | Read every contract and statement; non-vacuity witnesses. | 3.5, 6 |
| 4 | The **proved bytes are not the shipped bytes** | The library is rebuilt after a change, but the proofs still refer to the old binary. | `check.sh` step 2b rebuilds the library, regenerates the artifact file from it and requires it to equal the checked-in one. | 3.3, 4 |
| 5 | The **proof is incomplete** | `sorry`, a new `axiom`, or `native_decide` (trusts compiled code instead of the kernel). | Source scan (step 5) and axiom audit (step 6) in `check.sh`, with `Audit.lean`. | 4 |
| 6 | **Assumptions outside the model** | Interrupts, a core whose timing depends on data, power analysis. | Stated in the README; tested on hardware, never proved. | 5 |

The rest of the Lean code (proofs, tactics, helper lemmas and the constant-time certificate checker in `Release/ConstantTime/`) needs no review for correctness: it is checked by the kernel against the statements. It still matters for maintenance cost, but not for trust.

## 2. Top-level theorems

These are the roots from which the trusted base is computed. A reviewer reads each statement once, in full, and checks that it says what the release notes claim.

| Theorem | File | Claim |
|---|---|---|
| `ChaCha20Xor.xor_correct` | [`ChaCha20Xor.lean`](../lean/M0Crypto/Release/ChaCha20Xor.lean) | ChaCha20 output = RFC 8439 |
| `Aead.encrypt_correct` | [`AeadEncrypt.lean`](../lean/M0Crypto/Release/AeadEncrypt.lean) | AEAD encryption = RFC 8439 §2.8 |
| `Aead.decrypt_correct` | [`AeadDecrypt.lean`](../lean/M0Crypto/Release/AeadDecrypt.lean) | Checked decryption; `out` untouched on failure |
| `ChaCha20Xor.xor_constant_time` | [`ChaCha20XorConstantTime.lean`](../lean/M0Crypto/Release/ChaCha20XorConstantTime.lean) | Trace depends only on public inputs |
| `ChaCha20Xor.xor_reads` | [`ChaCha20XorReads.lean`](../lean/M0Crypto/Release/ChaCha20XorReads.lean) | Reads stay in allowed regions |
| `ChaCha20Xor.xor_stack` | [`ChaCha20XorStack.lean`](../lean/M0Crypto/Release/ChaCha20XorStack.lean) | SP within 176 bytes of entry |
| `Aead.encrypt_constant_time`, `_reads`, `_stack` | [`AeadEncryptConstantTime.lean`](../lean/M0Crypto/Release/AeadEncryptConstantTime.lean), [`AeadReads.lean`](../lean/M0Crypto/Release/AeadReads.lean), [`AeadEncryptStack.lean`](../lean/M0Crypto/Release/AeadEncryptStack.lean) | Same, encryption (320 bytes) |
| `Aead.decrypt_constant_time`, `_reads`, `_stack` | [`AeadDecryptConstantTime.lean`](../lean/M0Crypto/Release/AeadDecryptConstantTime.lean), [`AeadReads.lean`](../lean/M0Crypto/Release/AeadReads.lean), [`AeadDecryptStack.lean`](../lean/M0Crypto/Release/AeadDecryptStack.lean) | Same, decryption (320 bytes; the verdict bit is public) |

All twelve are in `assets/chacha20poly1305/Audit.lean`, and the four X25519 theorems of section 9.1 are in `assets/x25519/Audit.lean`, so their axioms are checked.

The three correctness statements are written out at the theorems (search for the theorem name in its file). The nine constant-time, read and stack statements are written once, as Props, in [`ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean) (shared vocabulary in [`TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean)); those theorems only say `: TraceSpec.X`.

All four theorems about one function assume the same thing, a valid call: `ChaCha20Xor.Pre c s` for ChaCha20, and `Aead.APre c off s` for the two AEAD functions (`off` selects encryption or decryption). The hypotheses are therefore read once per definition, not once per theorem.

**What the golden file locks.** Each asset's `assets/ASSET/Audit.lean` lists its claims, and `assets/ASSET/statements.golden` holds the printed statement of every claim, then the printed body of every trusted definition those statements reach (`tools/trusted_defs.lean`, `printTrusted`): the machine model and decoder, the contracts (`Pre`, `Valid`, `AValid`, `ABuf`, `pub`, `Result`, the read regions), the `TraceSpec` Props and the specification. `check.sh` fails if any of them changes. The artifact bytes are not printed; step 2b pins them. What the file cannot show is whether a changed definition still means what its reference says; that is the review of section 3.

## 3. What to review, in order

| Order | Part | Files | Hand-written lines | Main reference |
|---|---|---:|---:|---|
| 1 | [Machine model](#31-machine-model) | 4 | 288 | ARMv6-M Architecture Reference Manual |
| 2 | [Decoder](#32-decoder) | 1 | 66 to read, 100 cross-checked | `Instr.exec`; `llvm-objdump` |
| 3 | [Artifact](#33-artifact) | 1 | generated (196) | the build; review the generator instead |
| 4 | [Specifications](#34-specifications) | 2 | 117 | RFC 8439 |
| 5 | [Contracts and statements](#35-contracts-and-statements) | 4 | 319 | public headers, AAPCS, README claims |

Line counts include doc comments. Structure fields are counted with their structure. The tables name declarations, not line numbers, so they do not go stale when code moves.

How to read a table row: open the file, find the declaration, open the reference at the cited place, and confirm they agree. When the note says what to look for, start there. If you disagree, the finding is a **specification or model bug**: report it, do not patch the proofs around it.

### 3.1 Machine model

The model is what "the code runs on a Cortex-M0+" means inside Lean. Every theorem relies on it, and nothing else checks it against hardware, so it deserves the most careful reading.

**Check against:** *ARMv6-M Architecture Reference Manual* (Arm DDI 0419), mainly §A2.2 (`AddWithCarry`, `LSL_C`, `LSR_C`, `ROR_C` pseudocode), §A2.3 (`BXWritePC`, for `pop {..., pc}`), §A3 (alignment, endianness), §A6.3 (condition codes), §A6.4 (shifts applied to a register: `DecodeImmShift`, `Shift_C`) and the §A6.7 page of each instruction. The module headers of [`Thumb/Exec.lean`](../lean/M0Crypto/Thumb/Exec.lean) and [`Armv6M/State.lean`](../lean/M0Crypto/Armv6M/State.lean) state the scope; read them first.

- For every instruction in `Instr.exec`: result value, flags written (and flags *not* written), destination and writeback registers, as on its A6.7 page.
- Immediate scaling, which happens here and not in the decoder: `imm5 × width` for `ldr`/`ldrh`/`ldrb` and their stores, `imm8 × 4` for SP-relative and literal forms, `imm7 × 4` for `add sp`/`sub sp`. The one exception is `bl`, whose offset the decoder delivers already scaled.
- `Instr.accesses` and `Instr.exec` compute each address separately. The trace records the first; the memory changes by the second. Two proved lemmas tie them together. Read their statements instead of comparing the addresses: `exec_mem_other` ([`Thumb/Program.lean`](../lean/M0Crypto/Thumb/Program.lean)), an instruction changes memory only at the bytes of its write accesses, and `exec_reads_only` ([`Thumb/ExecReads.lean`](../lean/M0Crypto/Thumb/ExecReads.lean)), its result depends on memory only at the bytes of its read accesses. So no byte an instruction uses is missing from the trace.
- The lemmas do not show the converse, that the trace records no more than the instruction uses. Check in `Instr.accesses` that each access has the instruction's size: 1, 2 or 4 bytes, and one 4-byte access per register for `push`, `pop`, `ldm` and `stm`. The alignment fault in `step` uses the same sizes. With the right size, a wrong address or direction would contradict the lemmas.
- PC reads as instruction address + 4; literal loads use `Align(PC + 4, 4)`.
- Branch targets: `b`, `bcond`, `bl` add a sign-extended, halfword-scaled offset to PC + 4.
- `bl` writes LR = return address | 1; `pop {pc}` faults if bit 0 of the loaded value is clear.
- Carry on subtraction is NOT borrow (ARM convention). This includes `sbcs`, which computes `Rdn + NOT(Rm) + C`, so C = 0 on entry subtracts one more.
- Memory is little-endian; unaligned accesses fault (ARMv6-M has no unaligned access).
- `Event` contains everything the constant-time claim should observe: PC, instruction, and the address, width and kind of every access.
- Known scope limits are acceptable: no exceptions or interrupts, ordinary RAM, one thread.

**Second check: QEMU.** `check.sh` step 7b ([`tools/qemu_steps.py`](../tools/qemu_steps.py)) single-steps 42 calls of the three functions in QEMU and runs the model from the same entry state. After each of about 218,000 instructions r0-r15 and the N, Z, C, V flags must be equal, and at each return the whole RAM must be equal. This compares the decoder and `Instr.exec` with an independent ARMv6-M implementation, including the flags the code never reads and the proofs therefore cannot see. Know its limits:

- It covers the instructions those calls execute: 1,450 of the 1,459. Not reached are the four instructions of the ChaCha20 counter-overflow return, one branch of `poly1305_blocks`, and four padding instructions between functions.
- It covers them on the values that occur. A model error that needs a particular operand (a carry out of bit 31 in one specific instruction, say) is found only if a traced call produces it. Reading `Instr.exec` is still required.
- Loads are checked through the registers they fill and stores through the final RAM. `Instr.accesses`, the addresses the trace records, is not compared with QEMU; it is tied to `Instr.exec` by the two lemmas of the list above.
- QEMU is another implementation, not the chip.

The two models handle code differently. The early fragment model keeps code in a separate immutable region. The release model in `Thumb/Exec.lean` fetches code from the same memory as data, and its contracts require that no write reaches the code bytes. The release theorems use the release model. (Some proof files and doc comments say "Harvard run": that is an intermediate proof device. The theorems are stated on `runUntil`, the single-memory run.)

In `Armv6M/Memory.lean` and `Armv6M/Step.lean` only the listed declarations are trusted; the rest of those files belongs to the fragment model and to proofs. In `Thumb/Exec.lean` everything above the closing "Helper checks" examples is trusted.

**[`Armv6M/State.lean`](../lean/M0Crypto/Armv6M/State.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Armv6M.Word` | 1 | 32-bit word as `BitVec 32`: wrap-around arithmetic, as on the core. |
| `Armv6M.Reg` | 2 |  |
| `Armv6M.LowReg` | 2 |  |
| `Armv6M.LowReg.toReg` | 1 |  |
| `Armv6M.State` | 7 | Registers r0-r15, APSR N/Z/C/V, byte-addressed memory. Nothing else is modelled (no EPSR/IPSR/PRIMASK, no exceptions). Check nothing the code depends on is missing. |
| `Armv6M.State.pc` | 2 | PC is the address of the *current* instruction; reads of PC inside instructions add 4 (see `exec`). ARM ARM: "PC reads as the instruction address + 4". |
| `Armv6M.State.reg` | 1 |  |
| `Armv6M.State.setReg` | 2 |  |
| `Armv6M.State.setNZ` | 3 | N = bit 31, Z = result is zero; C/V unchanged. |

**[`Armv6M/Memory.lean`](../lean/M0Crypto/Armv6M/Memory.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Armv6M.Mem` | 1 |  |
| `Armv6M.read32` | 2 | Little-endian: byte at `a` is bits 7:0. ARM ARM, endianness (AIRCR.ENDIANNESS = 0 on the MSPM0). |
| `Armv6M.write32` | 6 | Same byte order as `read32`. Check all four bytes and that other addresses are untouched. |
| `Armv6M.slot` | 2 |  |

**[`Armv6M/Step.lean`](../lean/M0Crypto/Armv6M/Step.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Armv6M.addWithCarry` | 6 | Transcription of the `AddWithCarry` pseudocode. Check carry = unsigned overflow, V = signed overflow. Subtraction is `x + ~y + 1`, so C = NOT borrow (ARM convention, opposite of x86). |
| `Armv6M.rorC` | 9 | `ROR_C`/`Shift_C` for ROR. Amount 0 → value and carry unchanged; amount ≡ 0 mod 32 but ≠ 0 → value unchanged, carry = bit 31. |

**[`Thumb/Exec.lean`](../lean/M0Crypto/Thumb/Exec.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Thumb.read8` | 1 |  |
| `Thumb.read16` | 1 | Little-endian halfword, zero-extended (`ldrh`). There is no `ldrsh`/`ldrsb` in the model. The code uses neither: the listing comparison of section 3.2 would fail on one. |
| `Thumb.write8` | 2 |  |
| `Thumb.write16` | 4 |  |
| `Thumb.fetch16` | 2 |  |
| `Thumb.lslC` | 3 | `Shift_C` LSL for n < 32: carry = last bit shifted out. n = 0 is `movs Rd, Rm` (MOV register, encoding T2; 31 sites in the code): value and carry unchanged. |
| `Thumb.lsrC` | 3 | `Shift_C` LSR for 1 ≤ n ≤ 32; `lsrs #0` encodes a shift by 32 (handled in `exec`). |
| `Thumb.condPassed` | 18 | Condition codes EQ…LE (A6.3 table). Check each of the 14 cases, especially HI (C ∧ ¬Z), LS, GE (N = V), GT, LT, LE. |
| `Thumb.listRegs` | 3 |  |
| `Thumb.bitCount` | 3 | Number of registers in a `push`/`pop`/`ldm`/`stm` list. |
| `Armv6M.State.setNZC` | 3 |  |
| `Armv6M.State.setNZCV` | 3 |  |
| `Armv6M.State.sp` | 1 |  |
| `Thumb.addFlags` | 5 | Writes the result and N, Z, C, V from `addWithCarry`. With `write := false` (used by `cmp`) only the flags change. |
| `Thumb.Kind` | 4 |  |
| `Thumb.Access` | 6 | One data access (kind, address, width). **This is what "constant-time" observes**: if something the hardware leaks is not in `Event`, the proofs say nothing about it. |
| `Thumb.Access.aligned` | 1 |  |
| `Thumb.Event` | 6 | Trace event = PC + decoded instruction + data accesses. Timing is assumed to be a function of this sequence (README assumption, tested on hardware, not proved). |
| `Thumb.Fault` | 11 | Faults stop the run; the theorems show the code reaches its return without any fault, so faults cannot be hidden. |
| `Thumb.storeWords` | 4 |  |
| `Thumb.wordAccesses` | 3 |  |
| `Thumb.loadRegs` | 4 |  |
| `Thumb.Instr.accesses` | 20 | Addresses of every load and store. **This function, not `exec`, is what the trace records.** `exec_mem_other` and `exec_reads_only` prove it covers every byte `exec` reads or writes, so check only the size of each access (1, 2 or 4 bytes; one 4-byte access per register in the multi-word forms). |
| `Thumb.Instr.exec` | 93 | **The core of the model.** One case per instruction; compare each with its A6.7 page: result, which flags are set (for example MULS sets only N, Z), register writeback for `ldm`/`stm`, branch targets (PC+4 + offset), `bl` sets LR = next instruction \| 1, `pop {pc}` requires bit 0 = 1. |
| `Thumb.step` | 14 | Fetch two halfwords, decode, fault on misalignment (ARMv6-M has no unaligned access), execute. |
| `Thumb.runUntil` | 14 | Runs until PC = `stop` (the return address). Theorems quantify over its result. Check it records every executed instruction in the trace. |
| `Thumb.CodeAt` | 3 | The bytes are in memory at `base`. Both precondition structures (`Valid`, `AValid`) require it of the release bytes. |
| `Thumb.Writes` | 3 | Byte addresses touched by a write access (all `width` bytes). |
| `Thumb.Reads` | 3 | Byte addresses touched by a read access (all `width` bytes). |

### 3.2 Decoder

[`Thumb/Decode.lean`](../lean/M0Crypto/Thumb/Decode.lean) has two parts, and they are reviewed differently.

**The instruction set: read it.** `Instr` and the small types beside it are what `Instr.exec` is defined over. Read them together with section 3.1.

| Declaration | Lines | Review note |
|---|---:|---|
| `Thumb.DpOp` | 4 | `sbcs` (SBC register, T1 encoding `0100000110 Rm Rdn`) was added for X25519. Its `exec` case is the `adcs` adder with the operand complemented, as in the manual's pseudocode `AddWithCarry(R[n], NOT(R[m]), APSR.C)`; it writes N, Z, C and V. |
| `Thumb.MemOp` | 4 |  |
| `Thumb.MemOp.width` | 4 |  |
| `Thumb.MemOp.isLoad` | 3 |  |
| `Thumb.Instr` | 47 | The instruction set the model accepts, with the width of every field. |
| `Thumb.Instr.size` | 4 | 4 bytes for `bl`, 2 for everything else. |

**The decoding functions: cross-checked, not read.** These turn bytes into an `Instr`. `check.sh` step 4b decodes every instruction of the release code with them, prints the result with `render` in [`Thumb/Listing.lean`](../lean/M0Crypto/Thumb/Listing.lean), and requires the text to equal `llvm-objdump`'s at all 1,459 instruction offsets. `render` prints every field of every `Instr` constructor: register names, scaled immediates, branch targets, literal addresses. So a decoding that differs from LLVM's in any field, at any instruction of the code, fails the check. A wrong line of the decoder that affects no instruction of the code is harmless, because the theorems are about this code only.

| Declaration | Lines |
|---|---:|
| `Thumb.low`, `Thumb.bits`, `Thumb.is32` | 6 |
| `Thumb.decodeDp` | 15 |
| `Thumb.memOpOfRegForm` | 8 |
| `Thumb.decode16` | 55 |
| `Thumb.decodeBL` | 12 |
| `Thumb.decode` | 4 |

What this argument rests on, and what a reviewer checks instead of the 100 lines:

- `render` and its helpers (66 lines) print each field of each constructor, in the role `Instr.exec` gives it. Read the two side by side: `render` has its own copy of the immediate scaling and of the branch-target arithmetic, and the comparison validates the decoder only as far as the two agree. This includes the `bl` offset, which the decoder delivers already scaled and both add as is.
- No two instructions that `exec` treats differently print alike. One known case: `condName` prints conditions 13, 14 and 15 all as `le`. The code uses only `eq`, `ne`, `lo` and `ls`.
- The comparison covers every offset `llvm-objdump` lists, which is every instruction boundary: two `#guard`s in `Listing.lean` require the model's sweep to tile each code range exactly and the code and data ranges to cover the artifact. It does not cover an offset inside a `bl` or inside a literal pool. Execution never gets there if every jump lands on a listed offset. Step 4b requires that of all 55 direct branches (`b`, conditional `b`, `bl`). The only other jumps are six `pop {..., pc}`, which return to the instruction after a `bl` or to the caller.
- `llvm-objdump` is the independent decoder and is trusted as such, together with [`tools/check_listing.py`](../tools/check_listing.py), which normalises both texts (for branches it keeps the target address and drops the symbol name).

**Check against:** `Instr.exec` (section 3.1) for the instruction set and for `render`. The encoding tables of DDI 0419 §A5.2 and the BL page in §A6.7 are needed only if you choose to read the decoding functions as well.

### 3.3 Artifact

[`Artifacts/Release.lean`](../assets/chacha20poly1305/artifact/M0Crypto/Artifacts/Release.lean) holds the asset's release `.text` as a byte list plus the function offsets. It is generated, so do not review the bytes. Review instead:

- [`tools/extract_release.py`](../tools/extract_release.py): it copies `.text` and the symbol offsets from the built object without changing them.
- [`tools/check.sh`](../tools/check.sh) step 2b: the library is rebuilt from source, the artifact file is regenerated in memory from the built object and must equal the checked-in file (bytes, offsets and sha256).
- The size and sha256 in the file's header are the ones the library's CHANGELOG and README state for the release. Nothing checks this mechanically: step 2b compares the file with a fresh build, not with a recorded value. (`build/lib/MANIFEST.txt` is written by that same build, so it always agrees and proves nothing here.) Any change of the artifact does show up as a diff of this checked-in file.

**[`Artifacts/Release.lean`](../assets/chacha20poly1305/artifact/M0Crypto/Artifacts/Release.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Artifacts.Release.chacha20poly1305_encrypt` | 1 | Entry offset `0x970`. |
| `Artifacts.Release.chacha20poly1305_decrypt` | 1 | Entry offset `0xa90`. |
| `Artifacts.Release.size` | 2 | `3030`. Generated. |
| `Artifacts.Release.bytes` | 192 | Generated by `tools/extract_release.py`; do not review byte by byte. Review the generator and that `check.sh` step 2b compares the regenerated file with this one. |

### 3.4 Specifications

The specifications are the answer key. They must be readable without any knowledge of the assembly or the model: they import nothing from `Thumb/` or `Release/`. Check that this stays true.

**Check against:** [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439) (§2.1 quarter round, §2.2 quarter round on the state, §2.3 block, §2.4 encryption, §2.5 Poly1305, §2.6 key generation, §2.8 AEAD).

- Each definition against its RFC section, in the RFC's own order.
- Constants digit by digit: "expand 32-byte k", the clamp mask, `2^130 − 5`.
- The test vectors are copied from the RFC, not produced by this spec. They are in [`Spec/ChaCha20Vectors.lean`](../lean/M0Crypto/Spec/ChaCha20Vectors.lean) (§2.1.1 as a kernel-checked theorem, §2.3.2 as a `#guard`) and at the end of [`Spec/Aead.lean`](../lean/M0Crypto/Spec/Aead.lean) (§2.4.2, §2.5.2, §2.8.2 as `#guard`s). A `#guard` is a compiled evaluation: a test, not a kernel proof.
- Anything that is not in the RFC is a design choice and must match the header: the ChaCha20 counter-overflow rule (`counterOk`).

`check.sh` step 4c ([`tools/spec_vectors.py`](../tools/spec_vectors.py)) also runs the specification on the vectors the library itself is tested with ([`../tests/aead_vectors.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/aead_vectors.h)): RFC 8439 §2.8.2, 316 Wycheproof vectors and 46 random ones from pyca/cryptography for the AEAD (303 that must encrypt and decrypt exactly, 60 that must be rejected), and 76 Poly1305 vectors. These come from independent implementations and include empty messages, empty AAD and lengths around the 16- and 64-byte block boundaries.

Vectors are a second check, but they do not replace reading: a spec bug on a path the vectors do not exercise passes all of them. Know what they do not cover:

- No vector is longer than 1,000 bytes, so only the low two bytes of each length field in `macData` are ever non-zero.
- ChaCha20 always starts at counter 1 (§2.4.2 and inside the AEAD) or 0 (the Poly1305 key block); no vector starts at another counter. `counterOk` has no vector: it is a design choice of this library.

**[`Spec/ChaCha20.lean`](../lean/M0Crypto/Spec/ChaCha20.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Spec.ChaCha20.Word` | 2 |  |
| `Spec.ChaCha20.Byte` | 2 |  |
| `Spec.ChaCha20.rotl` | 3 |  |
| `Spec.ChaCha20.quarterRound` | 15 | RFC 8439 §2.1: a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12; … 8; … 7. |
| `Spec.ChaCha20.State` | 2 |  |
| `Spec.ChaCha20.qround` | 4 |  |
| `Spec.ChaCha20.innerBlock` | 11 | RFC 8439 §2.3: column rounds then diagonal rounds; check the diagonal index sets. |
| `Spec.ChaCha20.wordOfBytes` | 3 |  |
| `Spec.ChaCha20.wordsOfBytes` | 4 |  |
| `Spec.ChaCha20.bytesOfWord` | 3 |  |
| `Spec.ChaCha20.constants` | 3 | "expand 32-byte k" as four little-endian words (§2.3). |
| `Spec.ChaCha20.initState` | 3 | §2.3: constants, key words 4-11, counter word 12, nonce words 13-15. |
| `Spec.ChaCha20.innerBlocks` | 4 |  |
| `Spec.ChaCha20.blockWords` | 5 |  |
| `Spec.ChaCha20.block` | 4 | §2.3: 20 rounds (10 double rounds), add the input state, serialize little-endian. |

**[`Spec/Aead.lean`](../lean/M0Crypto/Spec/Aead.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Spec.Aead.keystream` | 5 |  |
| `Spec.Aead.chacha20` | 4 | §2.4: keystream from counter, XOR, last partial block truncated. |
| `Spec.Aead.counterOk` | 2 | Counter overflow rule: the library rejects messages that would wrap the 32-bit counter. Not in the RFC text; check it matches the header contract. |
| `Spec.Aead.p` | 1 |  |
| `Spec.Aead.leNat` | 4 |  |
| `Spec.Aead.leBytes` | 3 |  |
| `Spec.Aead.clamp` | 2 | §2.5: r &= 0x0ffffffc0ffffffc0ffffffc0fffffff. |
| `Spec.Aead.chunks16` | 6 |  |
| `Spec.Aead.polyAcc` | 3 | §2.5: per 16-byte block, add with a 0x01 byte appended (2^128 · 1 for full blocks; 2^(8·len) for the last partial block), multiply by r, reduce mod p. |
| `Spec.Aead.poly1305` | 5 | §2.5: tag = (acc + s) mod 2^128, little-endian. |
| `Spec.Aead.pad16` | 1 |  |
| `Spec.Aead.macData` | 3 | §2.8: AAD ‖ pad16 ‖ ciphertext ‖ pad16 ‖ le64(len AAD) ‖ le64(len ciphertext). |
| `Spec.Aead.polyKey` | 2 | §2.6: first 32 bytes of the ChaCha20 block with counter 0. |
| `Spec.Aead.encrypt` | 4 | §2.8: encryption starts at counter 1. |
| `Spec.Aead.decrypt` | 4 | §2.8: tag compared before releasing plaintext; check what is returned on failure. |

### 3.5 Contracts and statements

Contracts say *when* a theorem applies (preconditions) and *what* it promises (postconditions). This is where a statement most easily ends up weaker than intended, and where no tool helps you.

They are in statement files, which contain definitions only and import nothing but the specification, the model and the artifact. Read each from top to bottom: [`Contract.lean`](../lean/M0Crypto/Release/Contract.lean) and [`TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean) (shared vocabulary), [`ChaCha20Contract.lean`](../lean/M0Crypto/Release/ChaCha20Contract.lean), [`AeadContract.lean`](../lean/M0Crypto/Release/AeadContract.lean), [`ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean) and, for X25519, [`X25519Contract.lean`](../lean/M0Crypto/Release/X25519Contract.lean) and [`X25519TraceSpec.lean`](../lean/M0Crypto/Release/X25519TraceSpec.lean) (section 9.2).

Two definitions carry most of the weight, so read them first:

- `Region a n y` says that address `y` is one of the `n` bytes starting at `a`. Every read region, write region and "outside the stack" condition is written with it, and so is the condition on the return address. Three neighbouring notions keep their own definitions: `Disj` (two ranges do not overlap), `InStackWindow` (the closed range SP may be in) and the bytes of one access (`Reads`, `Writes`).
- `Pre` (ChaCha20) and `APre` (AEAD) are the complete hypothesis of every top-level theorem: the preconditions, the entry state, and two conditions on the return address.

**Check against:** [`include/m0crypto/chacha20.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20.h), [`include/m0crypto/chacha20poly1305.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20poly1305.h), the claims in the [library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md#proofs-and-scope) and the [proofs README](../README.md#constant-time-traces-read-bounds-and-stack-bounds), and the Arm *Procedure Call Standard* (AAPCS32: arguments in r0-r3 then the stack, r4-r11 and SP preserved).

For every precondition, ask:

- Does the header require it of callers? A precondition the header does not state means the theorem covers fewer calls than the header promises.
- `Pre` and `APre` add two conditions to the precondition structures: LR has its Thumb bit set, and the return address is not inside the library's own code. Check that every call from outside the library meets them.
- Can a real call satisfy all preconditions at once? If not, the theorem is vacuous. See "non-vacuity" in section 6 for what exists.
- Is it about public values only? A precondition on secret data would quietly restrict the constant-time claim.

For every postcondition and statement, ask:

- Does it say what the README and the headers claim, with nothing missing? Go through the claims one by one: output bytes, return value, restored registers, write regions, output on decryption failure, **and the clearing of working state**.
- Clearing is stated more narrowly than the prose. ChaCha20 (`Result.wipe`): the 35 frame words are zero for an accepted call with `len ≠ 0`. AEAD (`zero`): 96 bytes of the AEAD's own frame are zero. No top-level theorem covers the callee frames inside an AEAD call (the ChaCha20 frame, the `poly1305_blocks` frame). Decide whether the README and header wording is acceptable against that.
- For constant time: is everything in `pub` really public, and is every secret absent from it?
- For read regions: is each allowed region needed, and is none of them "all memory"?

**[`Release/Contract.lean`](../lean/M0Crypto/Release/Contract.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Release.B` | 2 | The release bytes (short name for `Artifacts.Release.bytes`). |
| `Release.Region` | 4 | `y` is one of the `n` bytes from `a`: `(y − a) mod 2^32 < n`. **Used by every region of the contracts**; an error here changes all of them. Check the wrap-around reading: a region that crosses the top of memory continues at address 0 (the preconditions exclude that for caller buffers, through `Disj`). The proved lemmas `Region.mk` and `Region.exists` (`Release/FrameBase.lean`) show it equals "`y = a + o` for some `o < n`". |
| `Release.WritesTo` | 3 | Every write in the trace lies in a region: used for "writes stay inside caller buffers". |
| `Release.runStates` | 15 | Same run as `runUntil`, also returning every intermediate state (used by the stack statements). The proved lemma `runStates_events` (`Release/RunStates.lean`) shows its trace equals `runUntil`'s. |
| `Release.Frame.Disj` | 3 | Two byte ranges do not overlap and do not wrap around memory. **Used in almost every precondition**; an error here weakens all of them. |

**[`Release/ChaCha20Contract.lean`](../lean/M0Crypto/Release/ChaCha20Contract.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Release.ChaCha20Layout.chFrameWords` | 2 |  |
| `Release.ChaCha20Layout.chStackWords` | 2 |  |
| `Release.ChaCha20Layout.chStackBytes` | 2 |  |
| `Release.Frame.Ctx` | 11 | One ChaCha20 call: where the code is (`base`), entry SP, the six arguments, and the entry memory and registers. The return address is `regs0 14`. |
| `Release.Frame.Ctx.fp` | 2 |  |
| `Release.Frame.Ctx.bytesAt` | 4 |  |
| `Release.Frame.Ctx.keyB` | 1 |  |
| `Release.Frame.Ctx.nonceB` | 1 |  |
| `Release.Frame.Ctx.msg` | 1 |  |
| `Release.Frame.Ctx.outB` | 2 | Expected output byte `i`, read from the specification's output list. `[i]!` returns 0 past the end of the list; the list has `len` elements. |
| `Release.Frame.Ctx.oidx` | 2 |  |
| `Release.Frame.Ctx.ret` | 2 | Return address: LR with bit 0 cleared. |
| `Release.Frame.Valid` | 18 | ChaCha20 preconditions. Compare with `include/m0crypto/chacha20.h`: every condition should be required by the header, or the theorem is narrower than the promise. |
| `Release.ChaCha20Setup.Entry` | 13 | The entry state really is a call: PC at the function, r0-r3 hold `out`, `in`, `len`, `key`, and the two stack arguments hold `nonce` and `counter`. |
| `Release.ChaCha20Xor.Pre` | 9 | **The hypothesis of all four ChaCha20 theorems**: `Valid`, `Entry`, LR is a Thumb address, and the return address is outside the artifact. |
| `Release.ChaCha20Xor.OutS` | 2 | Address lies outside the 176 stack bytes. |
| `Release.ChaCha20Xor.Result` | 11 | What the ChaCha20 theorem concludes: return to LR, SP and r4-r11 restored, r0 = 0 or −1 by the counter rule, the output bytes, all other memory outside the 176 stack bytes unchanged. `wipe`: the 35 frame words are zero, **only for an accepted call with `len ≠ 0`**. |
| `Release.ChaCha20Xor.WrOk` | 5 | Allowed write region for ChaCha20: the 176 stack bytes, and `out` only if the call is accepted. |

**[`Release/AeadContract.lean`](../lean/M0Crypto/Release/AeadContract.lean)**

| Declaration | Lines | Review note |
|---|---:|---|
| `Release.Aead.ACall` | 14 | AEAD call arguments. |
| `Release.Aead.ACall.A` | 2 |  |
| `Release.Aead.ACall.ret` | 2 | Return address: LR with bit 0 cleared. |
| `Release.Aead.AEntry` | 14 | AEAD entry state (registers and stacked arguments per AAPCS). |
| `Release.Aead.encOff` | 2 |  |
| `Release.Aead.decOff` | 1 |  |
| `Release.Aead.ACall.keyB` | 2 |  |
| `Release.Aead.ACall.nonceB` | 1 |  |
| `Release.Aead.ACall.aadB` | 2 |  |
| `Release.Aead.ACall.ptB` | 2 |  |
| `Release.Aead.ACall.tagB` | 1 |  |
| `Release.Aead.ACall.expected` | 1 |  |
| `Release.Aead.AValid` | 9 | AEAD preconditions. Compare with `include/m0crypto/chacha20poly1305.h`. |
| `Release.Aead.ABuf` | 13 | Buffer placement. `in` is exactly `out` or disjoint from it; AAD and tag do not overlap `out`; `out` and `tag` do not overlap the code; all buffers are clear of the stack region. Compare with the overlap rule in the header. |
| `Release.Aead.APre` | 10 | **The hypothesis of all eight AEAD theorems**: `AValid`, `ABuf`, `AEntry` at the function's offset, LR is a Thumb address, and the return address is outside the artifact. |
| `Release.Aead.SWr` | 2 | The stack region of an AEAD call and its callees: `[sp0 - 320, sp0)`. |
| `Release.Aead.OutR` | 2 | Address lies in the output buffer. |
| `Release.Aead.AWr` | 2 | Allowed write region for encryption: the stack region, `out` and `tag`. |
| `Release.Aead.DWr` | 1 | Stack region or `out`: memory outside it is unchanged by decryption. |
| `Release.Aead.DAllowed` | 2 | Allowed write region for decryption: the stack region, and `out` only if the tag verifies. |
| `Release.Aead.RetPost` | 7 | Common return obligations: return address, SP, r4-r11, r0 = result, r1-r3 zero. |
| `Release.Aead.EncryptResult` | 6 | Encryption post: `RetPost`, ciphertext and tag equal `Spec.Aead.encrypt`, memory unchanged outside `AWr`. `zero`: 96 bytes of the AEAD's own frame (Poly1305 context and key block) are zero. Callee frames are not mentioned. |
| `Release.Aead.DecryptResult` | 9 | Decryption post: on failure r0 = −2 and `out` is unchanged; on success r0 = 0 and the plaintext equals the spec. `frame` and `zero` as for encryption. |

**[`Release/ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean)** (the shared `ReadsFrom` and `InStackWindow` are in [`Release/TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean))

| Declaration | Lines | Review note |
|---|---:|---|
| `Release.Frame.Ctx.pub` | 5 | **What counts as public** for ChaCha20 constant time. Everything not listed may differ between the two runs. A field wrongly listed here would make the theorem weaker without any failure. |
| `Release.Aead.ACall.pub` | 5 | What counts as public for the AEAD. Same warning. |
| `Release.Aead.ACall.verdict` | 2 | The one secret bit allowed to influence decryption's trace: whether the tag verifies. |
| `Release.TraceSpec.aeadStackBytes` | 3 | 320: stack bytes of an AEAD call including its callees. |
| `Release.TraceSpec.ReadsFrom` | 3 | Every read in the trace lies in a region. |
| `Release.TraceSpec.ChaCha20XorReadRegion` | 6 | Where ChaCha20 may read: one `Region` per buffer. Check no secret region beyond the inputs is allowed. The stack region starts at `fp` and includes the 8 bytes of stack arguments above the 176. |
| `Release.TraceSpec.AeadEncryptReadRegion` | 8 | The stack region includes the 16 bytes of stack arguments above the 320. |
| `Release.TraceSpec.AeadDecryptReadRegion` | 5 | The encryption region plus the tag. It also admits `out`, which decryption has no need to read when `out` and `in` differ: the bound is wider than necessary there (stated in the proofs README). |
| `Release.TraceSpec.InStackWindow` | 3 | SP stays within [sp0 − N, sp0]. |
| `Release.TraceSpec.ChaCha20XorConstantTime` | 6 | Two valid calls (`Pre` twice) with equal `pub` give equal `runUntil` results (trace or fault) for **every** fuel. With too little fuel both sides are `.error .fuel` and no trace is compared; the content is at the fuel values where the runs return, which exist by the read-bound theorem. |
| `Release.TraceSpec.ChaCha20XorReads` | 6 |  |
| `Release.TraceSpec.ChaCha20XorStack` | 6 |  |
| `Release.TraceSpec.AeadEncryptConstantTime` | 6 |  |
| `Release.TraceSpec.AeadEncryptReads` | 6 |  |
| `Release.TraceSpec.AeadEncryptStack` | 6 |  |
| `Release.TraceSpec.AeadDecryptConstantTime` | 7 | As for encryption, with the extra hypothesis that both calls have the same `verdict`. |
| `Release.TraceSpec.AeadDecryptReads` | 6 |  |
| `Release.TraceSpec.AeadDecryptStack` | 6 |  |

## 4. Trusted code that is not a Lean definition

These files decide whether the proofs are about the shipped library and whether they are complete. Review each once, then review every diff to them.

| File | Lines | What it guarantees |
|---|---:|---|
| [`tools/check.sh`](../tools/check.sh) | 296 | The release gate, per asset (`tools/check.sh [ASSET...]`). Step 2b: rebuilds each asset and compares the regenerated artifact file with the checked-in one. Step 4: builds each asset's proofs in its workspace. Step 4b: compares the decoder with `llvm-objdump`. Step 4c: runs the specification on external vectors. Step 5: rejects `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/`extern` in sources. Step 6: audits axioms. Step 6b: compares statements with the golden file. Step 7: runs the QEMU tests. Step 7b: compares the model with QEMU instruction by instruction. |
| [`../tools/build_lib.sh`](../../tools/build_lib.sh) | 51 | Builds the object whose `.text` is proved, with the pinned toolchain. |
| [`tools/extract_release.py`](../tools/extract_release.py) | 172 | Generates an asset's `Artifacts/Release.lean` from its built object. |
| [`tools/check_listing.py`](../tools/check_listing.py), [`lean/DumpListing.lean`](../lean/DumpListing.lean), [`lean/M0Crypto/Thumb/Listing.lean`](../lean/M0Crypto/Thumb/Listing.lean) | 83 + 5 + 129 | The decoder-versus-LLVM comparison, including `render`, which prints the model's decoding. This is what stands in for reading the decoding functions (section 3.2). |
| [`tools/spec_vectors.py`](../tools/spec_vectors.py), [`lean/SpecVectors.lean`](../lean/SpecVectors.lean) | 50 + 61 | Runs the specification on the library's test vectors (section 3.4). A test: an error here could hide a specification bug, not create a false theorem. |
| [`tools/qemu_steps.py`](../tools/qemu_steps.py), [`lean/StepTrace.lean`](../lean/StepTrace.lean) | 180 + 84 | Compares the model with QEMU after every instruction of sampled calls (section 3.1). Also a test. |
| `assets/ASSET/Audit.lean` | | Per asset: the claims (section 6, "Claim policy"). `check.sh` requires one axiom report per claim, drawn only from `propext`, `Classical.choice`, `Quot.sound`. |
| [`tools/statements.sh`](../tools/statements.sh), [`tools/claims.sh`](../tools/claims.sh) + `assets/ASSET/statements.golden` | | Per asset: printed statement of every claim and body of every trusted definition. See section 2. |
| [`lean-toolchain`](../lean-toolchain), [`tools/versions.txt`](../tools/versions.txt), [`../tools/versions.txt`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tools/versions.txt) | — | Pinned Lean, LLVM and QEMU versions. |
| [`tools/trusted_defs.lean`](../tools/trusted_defs.lean) | 120 | Computes the lists in section 3 and the definitions printed into the golden files. An error here would hide trusted code from the reviewer. `check.sh` runs it through `statements.sh`. |

Also trusted, outside this repository:

- The Lean kernel and the Lean core library (`BitVec`, `List`; `omega`'s proof output is kernel-checked).
- Lean's elaborator, for the meaning of what you read: the kernel checks the elaborated statement, and you read its source text.
- Whatever puts the library on the chip (linker, image conversion, flashing): the proofs are about these 3,030 bytes at a 4-byte-aligned address. The object has no relocations, so a linker has nothing to patch.

The assembler is *not* trusted. The proofs are about its output bytes, whatever the source says.

## 5. Assumptions no review can remove

These are stated in the [library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md#proofs-and-scope). A reviewer checks that they are stated, not that they hold:

- Execution is sequential, without interrupts or exceptions, and nothing else modifies memory while a function runs (another bus master such as DMA would).
- Memory is ordinary RAM: no faults, no device side effects.
- Execution time depends only on the trace (instructions, addresses, branches). True for the Cortex-M0+ (no cache, no branch prediction) per Arm's documentation; tested on the MSPM0L2228 by cycle measurements, not proved.
- Physical side channels and fault injection (power analysis, electromagnetic leakage, glitching) are out of scope.

## 6. Keeping the proofs robust

Trust is not a one-time review. Every change to the code or proofs can move the trusted base. These habits keep the review small and valid.

**Check the reading list before every review.**

```sh
(cd assets/chacha20poly1305 && lake build)
tools/trusted_defs.sh chacha20poly1305      # likewise blake2s, x25519
```

The tool prints every trusted declaration with its file and line range, then one `FILE` line per file. Those `FILE` lines must name exactly the eleven hand-written files of section 3, the two of section 9 (`Spec/X25519.lean`, `X25519Contract.lean`) and the artifact file, plus the BLAKE2s files, which this document does not yet cover. A file that appears for the first time holds new trusted code: move that definition into a statement file, or review the new file. The roots are the claims in the asset's `Audit.lean` without the non-vacuity witnesses, so adding a claim there is the only step.

The tables in section 3 are this output plus one hand-written note per declaration. To refresh them, add a row (with a note) for each new declaration, drop rows that disappeared, and correct the line counts.

**Claim policy (every asset).** An asset's `Audit.lean` lists exactly its claims, in this order: for each global function of the asset's object, a correctness, a constant-time, a read-bound and a stack-bound theorem, and a non-vacuity witness (`*_nonvacuous`) whose statement is the correctness precondition at a concrete call; then the asset's composition claims (AEAD `rejected_writes`, BLAKE2s `hash_*`, `c1`, `c4`). Supporting lemmas are not listed: `#print axioms` on a claim already follows its whole proof, and step 5 scans every source for `sorry` and axioms. Internal routines (local symbols: X25519 `fe_*`, Poly1305 `init`/`blocks`/`finish`) are not claims; their contracts are proved and used inside the claims of the functions that call them, and the artifact file marks each function offset `exported` or `internal`. A composed claim with many hypotheses names them as a structure (BLAKE2s `C1Hyp`, `C4Hyp`) so that its witness can state them at a concrete call; a constant-time witness uses two executions that differ in their secret input (BLAKE2s `c4_nonvacuous`: two message byte strings). Open against this policy: the per-function constant-time claims of all three assets have no two-execution witness (their witnesses show the correctness precondition).

**Review statement diffs, not proof diffs.** For any change, the questions are:

1. Did an asset's `statements.golden` change? Read every changed statement in full.
2. Did a trusted file change? This is the only check on the contract definitions and on the bodies of the `TraceSpec` Props, so it is not optional. Read the diff against its reference:

   ```sh
   git diff <reviewed commit> -- lean/M0Crypto/Spec lean/M0Crypto/Armv6M \
     lean/M0Crypto/Thumb/Decode.lean lean/M0Crypto/Thumb/Exec.lean lean/M0Crypto/Thumb/Listing.lean \
     lean/M0Crypto/Release/Contract.lean lean/M0Crypto/Release/ChaCha20Contract.lean \
     lean/M0Crypto/Release/AeadContract.lean lean/M0Crypto/Release/TraceSpec.lean \
     lean/M0Crypto/Release/ChaCha20TraceSpec.lean lean/M0Crypto/Release/X25519TraceSpec.lean \
     lean/M0Crypto/Release/X25519Contract.lean lean/M0Crypto/Assets \
     assets tools ../tools/build_lib.sh
   ```

3. Did `check.sh` pass from a clean checkout?

If all three are fine, the proof changes need no correctness review.

**Watch for these patterns.** An agent (or a person) under pressure to make a proof go through tends to change the statement instead of the proof:

- a new or stronger hypothesis (smaller set of calls covered);
- a new helper definition used in a statement (new trusted code);
- a `pub` tuple that grows (weaker constant-time claim);
- a write or read region that grows;
- a postcondition that is dropped or replaced by something weaker;
- `sorry`, `axiom`, `native_decide`, or a raised `maxRecDepth`/`maxHeartbeats` to force a `decide` through (the last two are not unsound, only a cost signal).

**Non-vacuity.** Each function has a concrete call that satisfies `Pre` (or `APre`), the whole hypothesis of its correctness, read and stack theorems: [`Release/ChaCha20Poly1305NonVacuity.lean`](../lean/M0Crypto/Release/ChaCha20Poly1305NonVacuity.lean) proves this for the three functions, with calls that are in place, unaligned and non-empty, and passes each witness to its correctness theorem. The constant-time theorems take two such calls with equal `pub` (and, for decryption, equal verdict); the same witness taken twice fits. Check that the witnesses are realistic rather than degenerate. The executable release checks (`Thumb/ReleaseCheck/`) run the real bytes on concrete inputs, which is strong evidence but not a proof that the contracts are satisfiable.

**Keep the trusted base where it is.** Statements mention only definitions from `Spec/`, the model, and the statement files. A new definition that a statement needs goes into a statement file, never into a proof file.

**Known gaps.**

- The golden file does not lock definition bodies or the `TraceSpec` Props (section 2); the diff in question 2 is what covers them.
- The decoding functions are trusted through the comparison with LLVM, not through reading (section 3.2).
- The clearing of working state is proved only as far as section 3.5 says. Beyond that it is tested, not proved: `Thumb/ReleaseCheck/Cases.lean` (`sameResidue`) checks on concrete inputs that the stack left behind does not depend on the secrets.
- The model is compared instruction by instruction with QEMU, on sampled calls (section 3.1). It is compared with the chip only through the outputs and cycle counts of whole function calls.

## 7. Learning by breaking things

The fastest way to understand what each part protects is to break it on purpose and watch what fails. Do these on a scratch branch and revert afterwards. Build only the modules you need (`lake build +Module.Name`); a full build takes several minutes.

1. **Read a statement in full.** `tools/statements.sh chacha20poly1305` prints every claim with full names, then every trusted definition. Pick `xor_correct` and trace each name to its definition, first in that output, then in the tables above. Then pick `xor_constant_time`: the statement is only a name, and its body is printed further down.
2. **See the axiom audit.** `lake env lean Audit.lean` in `assets/chacha20poly1305` prints the axioms of each theorem. Replace a proof step in `Release/ChaCha20Xor.lean` by `sorry`, run `lake build`, and run it again: `sorryAx` appears for every audited theorem that depends on that proof, and `check.sh` fails.
3. **Break the spec.** In `Spec.ChaCha20.quarterRound`, change the rotation 12 to 11. The vectors in `Spec/ChaCha20Vectors.lean` fail. Then ask: which spec errors would the vectors *not* catch? (Hint: the length fields of `macData`.)
4. **Break the model.** In `Armv6M.addWithCarry`, return the carry negated. Build the release proofs and see which theorems fail: that shows you how much depends on one line. Then try an error in a flag: remove `.setNZ x` from the `movImm` case of `Instr.exec`, build `+M0Crypto.Thumb.FastRun` and run the step 7b command from `check.sh`. It stops at the first instruction after which the model and QEMU differ.
5. **Make a theorem vacuous.** Add `h : False` as a hypothesis to a copy of a small theorem. It proves trivially. This is why section 3.5 asks whether preconditions can all hold.
6. **See who protects a contract.** Add a field to `Valid` in `ChaCha20Contract.lean` (for example `short : c.len.toNat < 64`) and build `+M0Crypto.Release.AeadKey`. The golden file would show the new field, but the build stops first: the AEAD proof must establish `Valid` for its own inner ChaCha20 call, and the witness in `NonVacuity.lean` no longer fits. A contract is protected by whoever has to satisfy it. A definition nobody has to satisfy, such as `pub` or a read region, is protected only by review.
7. **Mutate the assembly.** [`tools/mutate_aead.py`](../tools/mutate_aead.py) applies deliberate bugs to the AEAD source and checks that the QEMU tests or the model's executable release checks detect each one. (It does not run the proofs.) Read its mutant list and predict which check catches each mutant before running it.

Background reading: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) (chapters on propositions, quantifiers and structures are enough to read every statement here) and [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) (to read definitions such as `Instr.exec`).

## 8. Reference documents

| Document | Used for |
|---|---|
| [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439), ChaCha20 and Poly1305 for IETF Protocols | `Spec/ChaCha20.lean`, `Spec/Aead.lean`, vectors (§2.1.1, §2.3.2, §2.4.2, §2.5.2, §2.8.2) |
| [ARMv6-M Architecture Reference Manual](https://developer.arm.com/documentation/ddi0419/latest) (DDI 0419) | Machine model and decoder |
| [Procedure Call Standard for the Arm Architecture](https://github.com/ARM-software/abi-aa/releases) (AAPCS32) | Entry contracts: argument registers, stack arguments, callee-saved registers |
| [Cortex-M0+ Technical Reference Manual](https://developer.arm.com/documentation/ddi0484/latest) (DDI 0484) and [Generic User Guide](https://developer.arm.com/documentation/dui0662/latest) (DUI 0662) | Timing assumption (instruction cycle counts, no cache or branch prediction) |
| [`include/m0crypto/chacha20.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20.h), [`chacha20poly1305.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20poly1305.h) | Contracts: what callers must guarantee and what they are promised |
| [Library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md), [proofs README](../README.md) | The claims the theorems must support |
| [RFC 7748](https://www.rfc-editor.org/rfc/rfc7748), Elliptic Curves for Security | `Spec/X25519.lean` (section 5), vectors (section 5.2) |
| [`include/m0crypto/x25519.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/x25519.h) | X25519 contract (section 9) |

Links that start with `../../` point into the library repository and work in a local checkout with submodules, not on the proofs repository's own web page.

## 9. X25519 (`m0c_x25519`)

The X25519 unit is four symbols of the release artifact: the entry `m0c_x25519` (offset `Artifacts.Release.x25519`) and the field routines `m0c_fe_mul`, `m0c_fe_sqr` and `m0c_fe_mulc_add`, which only the entry calls. It is reviewed like the other functions: read the statements and the definitions they use, never the proofs. This section lists what is specific to X25519. Sections 3.1-3.3 (model, decoder, artifact), 4 and 6 apply unchanged.

### 9.1 Top-level theorems

| Theorem | File | Claim |
|---|---|---|
| `X25519.x25519_correct : X25519.Correct` | [`X25519Correct.lean`](../lean/M0Crypto/Release/X25519Correct.lean) | Every valid call returns; `out` holds RFC 7748 `X25519(scalar, point)`; all other memory outside the stack window is unchanged; the 480 stack bytes below the saved registers are zero; r4-r11 and SP restored, r0 = 0 (`M0C_OK`), r1-r3 and r12 zero; only the stack window and `out` are written |
| `X25519.x25519_constant_time : TraceSpec.X25519ConstantTime` | [`X25519Trace.lean`](../lean/M0Crypto/Release/X25519Trace.lean) | Trace depends only on the base, entry SP, LR and the three pointers |
| `X25519.x25519_reads : TraceSpec.X25519Reads` | same | Reads only `scalar`, `point`, the artifact and the stack window |
| `X25519.x25519_stack : TraceSpec.X25519Stack` | same | SP within 516 bytes below its entry value at every state |

All four assume exactly `X25519.Pre c s`. They are the claims in `assets/x25519/Audit.lean`, with the non-vacuity witness `NonVacuity.x25519_pre_nonvacuous` (`X25519NonVacuity.lean`): a call where `out` is `point`, at an odd address, and `scalar` is unaligned, on RFC 7748 vector 1.

### 9.2 What to read

| Part | File | Declarations | Lines | Reference |
|---|---|---:|---:|---|
| Specification | [`Spec/X25519.lean`](../lean/M0Crypto/Spec/X25519.lean) | 15 | 68 | RFC 7748 section 5 |
| Contract | [`X25519Contract.lean`](../lean/M0Crypto/Release/X25519Contract.lean) | 15 | 87 | `include/m0crypto/x25519.h`, AAPCS32 |
| Trace statements | [`X25519TraceSpec.lean`](../lean/M0Crypto/Release/X25519TraceSpec.lean): `X25519.Ctx.pub`, `X25519ReadRegion`, `X25519ConstantTime`, `X25519Reads`, `X25519Stack` | 5 | 26 | the claims of section 9.1 |
| Model | `sbcs` in `Thumb.DpOp` and `Instr.exec` (section 3.1) | 1 | 4 | ARMv6-M manual, SBC (register) |
| Artifact | `Artifacts.Release.x25519`, `size`, `bytes` | 3 | generated (444) | `llvm-nm -S` of the built object; section 3.3 |

Produced by `tools/trusted_defs.sh x25519`. With the model (287 lines), the decoder (167) and the shared vocabulary (37), the X25519 asset trusts 672 hand-written lines in 10 files, of which 181 are its own.

**Specification.** `Spec/X25519.lean` follows RFC 7748 section 5 in the RFC's own names and order. Check:

- `decodeScalar25519`: clears bits 0-2 of byte 0, clears bit 7 of byte 31, sets bit 6 of byte 31.
- `decodeUCoordinate`: masks bit 7 of byte 31 (`bits = 255`) and does *not* reduce: values of `p` or more are reduced by the field arithmetic, as the RFC requires.
- `ladderStep`: one loop iteration for `t = 254` down to `0`, with `a24 = 121665`, `z_2 = E * (AA + a24 * E)`, and the swap carried between iterations. The RFC's `z_3 = x_1 * (DA - CB)^2` uses `x_1 = u`, the decoded (unreduced) coordinate; every result is reduced mod `p`.
- `output`: the final `cswap`, then `x_2 * z_2^(p - 2)` written as a power, then `encodeUCoordinate` (`% p`, 32 little-endian bytes). `output_eq_fast` is a theorem marked `@[csimp]`: it changes only how compiled tests evaluate `output`, not its meaning.
- No zero check: the function returns the all-zero output for low-order points, as wolfSSL's low-level `curve25519()` does. Rejecting those is the caller's (protocol's) job.

Vectors, as `#guard`s in [`Spec/X25519Vectors.lean`](../lean/M0Crypto/Spec/X25519Vectors.lean): RFC 7748 section 5.2, both single vectors (the second has the top bit of `u` set) and the iteration after 1 and 1,000 steps. Section 6.1 (Diffie-Hellman) is not separately run. The machine code itself is run on vector 1 under QEMU by step 7b.

**Contract.** Read `X25519Contract.lean` from top to bottom. Points to check:

- `Pre` = `Valid` + `Entry` + Thumb-mode LR + return address outside the artifact. `Valid` asks that `out` not overlap the code and that none of the three buffers overlap the 516-byte stack window; `scalar` and `point` may overlap the code (they are only read). The three buffers may be unaligned and may overlap each other in any way (the entry reads `scalar` and `point` completely before it writes `out`); the witness uses `out = point`.
- `Result.mem` says memory *outside the stack window* is unchanged except `out`. Inside the window, `wipe` says the 480 bytes below the saved registers are zero. `Result` says nothing about the top 36 bytes. By the code they hold the caller's r4-r11 and LR as saved at entry, the caller's own values rather than secrets of this call; this is read from the epilogue, not stated by a theorem.
- `X25519.Ctx.pub` lists what is public: base, entry SP, LR, and the three pointers. Scalar and point bytes, all other memory and the other registers are secret.
- `X25519ReadRegion` is `scalar` ∪ `point` ∪ artifact ∪ stack window. `out` is not in it, so the code never reads `out` unless `out` overlaps an input.

### 9.3 Assumptions the X25519 theorems carry

These are in addition to section 5, and no review removes them:

- **The Thumb model is faithful for the instructions used.** Evidence: the decoder is compared with `llvm-objdump` on every instruction (step 4b), the model with QEMU after every instruction of six sampled windows of one call (step 7b: prologue, one ladder step, the exit of each loop kind, epilogue; 25,548 instructions, 3,230 of the asset's 3,462 distinct instructions), and `sbcs` on a fixture covering both carries, overflow and zero. Not proved.
- **The bytes proved are the bytes linked.** `check.sh` step 2b regenerates the artifact from the built object; `src/x25519.S` is generated by `tools/gen_x25519.py` and compared in step 2b. The object is relocation-free.
- **The caller meets `Pre`:** three 32-byte buffers, 516 bytes of stack, no buffer overlapping the code or the stack window, a Thumb-mode return address outside the artifact.
- **Interrupts are outside the model.** An exception taken during the call pushes r0-r3, r12, LR, PC and xPSR, which may hold secret-dependent values, *below* the current SP. That is below the stack window, so the final wipe does not clear it, and the handler's own stack use can overwrite or leave it. A handler also sees the call's secrets in the window until the wipe. `wipe` and the constant-time claim are therefore about uninterrupted calls; a caller that needs the guarantee with interrupts enabled must mask them or clear the stack below the window itself.
- **Constant time is a statement about the model's trace.** Whether equal traces take equal time depends on the chip, in particular on `muls` taking the same number of cycles for every operand (the Cortex-M0+ multiplier is a build option of the core, single-cycle or 32-cycle iterative; either takes a fixed time). That is checked by measurement on the MSPM0L2228, not by Lean.

### 9.4 Checks specific to X25519

- [`tools/mutate_x25519.py`](../tools/mutate_x25519.py): 14 single-instruction mutants over the four symbols (flipped `adcs`/`sbcs`, changed shifts and constants, a swapped register, a changed loop count, a skipped wipe store, a register not cleared, a store replaced by a branch on a secret carry). Each is patched into a copy of the object; the executable release checks (`Thumb/ReleaseCheck/X25519*`) must reject the functional ones and the constant-time certificate the timing one. A byte change is also expected to break the proofs, since they are about these bytes; the run does not check that.
- [`tools/qemu_x25519_windows.py`](../tools/qemu_x25519_windows.py): the sampled QEMU comparison of step 7b.
