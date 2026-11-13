# Naming conventions

Modules, namespaces and theorems follow one convention:

- Directories by layer: `Armv6M/` and `Thumb/` (machine models), `Spec/` (specifications), `Sym/` (symbolic executor), `Proofs/` and `Artifacts/` (standalone fragments), `Release/` (facts about the release bytes), `Release/ConstantTime/` (the constant-time certificate checker).
- File stems are UpperCamelCase `<Component><Part>` with words spelled out. The components are `ChaCha20`, `Poly1305`, `Aead`, `Blake2s` and `X25519`; `ChaCha`, `Poly`, `AEAD` and `CT` are not used in names. Short forms allowed in file names: `Sem`, `Imm8`, `Rfc`, `Pc`, `Sp`, `Alu`, `Mem`, `Defs`.
- A file's namespace is its module path, with these exceptions:
  - All `Aead*` files share `M0Crypto.Release.Aead`. `Poly1305Blocks*` files share `M0Crypto.Release.Poly1305Blocks`, and `Poly1305Finish*` files share `M0Crypto.Release.Poly1305Finish`.
  - All files in `Release/ConstantTime/` share `M0Crypto.Release.ConstantTime`.
  - The release-check shards in `Thumb/ReleaseCheck/` share `M0Crypto.Thumb.ReleaseCheck`.
  - An asset's statement files (`<Component>Contract`, `<Component>TraceSpec`, `Blake2sStatements`) and the files that prove those statements (`Blake2sClaims`, `Blake2sComposed`, `X25519Correct`) use the component namespace `M0Crypto.Release.<Component>`.
  - The BLAKE2s per-function contracts sit in `M0Crypto.Release.Blake2s.Init`, `.Update` and `.Final`.
  - A `<Stem>Defs` file holds definitions split out of `<Stem>` so that other files can import them without waiting for its proofs. It shares `<Stem>`'s namespace.
- Casing conventions: theorems are snake_case, Props and types are UpperCamelCase, and data is lowerCamelCase (acronyms are capitalized as words, e.g. `keyOk`). Each specification and theorem has one name without aliases.
- Top-level theorems are `<Component>.<operation>_<property>`, with property one of `correct`, `constant_time`, `reads` or `stack`.
- Exceptions among the claims: the composition claims `Aead.rejected_writes`, `Blake2s.hash_correct` and `Blake2s.hash_constant_time`, and the non-vacuity witnesses in namespace `NonVacuity`, which end in `_nonvacuous` but whose stems differ by asset (`xor_correct_nonvacuous`, `init_pre_nonvacuous`, `x25519_pre_nonvacuous`; `hash_correct_nonvacuous` and `hash_constant_time_nonvacuous` for the two BLAKE2s composition claims).
- Lean defs that mirror an assembly macro keep the macro's name (`ach`, `mac4`, `narrow`, `colend`, `qr`, `dround`).

Names changed after 0.1.0 without compatibility aliases; earlier commits (such as `e10ef67`) retain the old names.
