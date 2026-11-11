# Naming conventions

Modules, namespaces and theorems follow one convention:

- Directories by layer: `Armv6M/` and `Thumb/` (machine models), `Spec/` (specifications), `Sym/` (symbolic executor), `Proofs/` and `Artifacts/` (standalone fragments), `Release/` (facts about the release bytes), `Release/ConstantTime/` (the constant-time certificate checker).
- File stems are UpperCamelCase `<Component><Part>` with words spelled out. The components are `ChaCha20`, `Poly1305` and `Aead`; `ChaCha`, `Poly`, `AEAD` and `CT` are not used in names. Short forms allowed in file names: `Sem`, `Imm8`, `Rfc`, `Pc`, `Sp`, `Alu`, `Mem`, `Defs`.
- A file's namespace is its module path, except that all `Aead*` files share `M0Crypto.Release.Aead`, `Poly1305Blocks*` share `M0Crypto.Release.Poly1305Blocks`, `Poly1305Finish*` share `M0Crypto.Release.Poly1305Finish`, all files in `Release/ConstantTime/` share `M0Crypto.Release.ConstantTime`, and the release-check shards in `Thumb/ReleaseCheck/` share `M0Crypto.Thumb.ReleaseCheck`. A `<Stem>Defs` file holds definitions split out of `<Stem>` so that other files can import them without waiting for its proofs; it shares `<Stem>`'s namespace.
- Casing conventions: theorems are snake_case, Props and types are UpperCamelCase, and data is lowerCamelCase (acronyms are capitalized as words, e.g. `keyOk`). Each specification and theorem has one name without aliases.
- Top-level theorems are `<Component>.<operation>_<property>`, with property one of `correct`, `constant_time`, `reads` or `stack`.
- Lean defs that mirror an assembly macro keep the macro's name (`ach`, `mac4`, `narrow`, `colend`, `qr`, `dround`).

Names changed after 0.1.0 without compatibility aliases; earlier commits (such as `e10ef67`) retain the old names.
