#!/usr/bin/env python3
"""Extract the release artifact (the .text of the library unit) into a Lean module.

The library is one relocatable object, src/m0crypto.S -> m0crypto.o. This tool
checks the properties that make its .text bytes the artifact the proofs bind to:

* ELF32 little-endian ARM relocatable object;
* no relocation section of any kind (so the bytes do not depend on the link layout);
* no allocated section other than .text with nonzero size (no data, rodata or bss);
* .text alignment 4 (link it at a 4-byte-aligned address);
* every global function symbol has the Thumb bit set, a nonzero size, starts in a
  `$t` code range and ends inside .text;

and writes lean/M0Crypto/Artifacts/Release.lean with the bytes, their sha256,
the offsets of the global function symbols, and the code/data ranges given by the
ARM mapping symbols ($t / $d; ELF for the Arm Architecture §5.5.5). `--check` regenerates in memory and
fails if the checked-in file differs.

Standard library only.

Usage:
  extract_release.py OBJECT OUT.lean [--check]
"""
import hashlib
import struct
import sys

SHF_ALLOC = 0x2
SHT_REL, SHT_RELA, SHT_SYMTAB, SHT_NOBITS = 9, 4, 2, 8
STB_GLOBAL, STT_FUNC = 1, 2


def fail(msg):
    sys.exit(f"extract_release: {msg}")


def cstr(data, off):
    end = data.index(b"\0", off)
    return data[off:end].decode("ascii")


def parse(data):
    if data[:4] != b"\x7fELF" or data[4] != 1 or data[5] != 1:
        fail("expected a little-endian ELF32 file")
    (e_type, e_machine, _v, _entry, _phoff, e_shoff, _flags, _ehsize, _phes, _phn,
     e_shentsize, e_shnum, e_shstrndx) = struct.unpack_from("<HHIIIIIHHHHHH", data, 16)
    if e_type != 1:
        fail("expected ET_REL (an assembled object, not a linked image)")
    if e_machine != 40:
        fail("expected EM_ARM")
    secs = []
    for i in range(e_shnum):
        (name, typ, flags, _addr, off, size, link, _info, align, entsize) = struct.unpack_from(
            "<IIIIIIIIII", data, e_shoff + i * e_shentsize)
        secs.append(dict(name=name, type=typ, flags=flags, off=off, size=size, link=link,
                         align=align, entsize=entsize))
    strtab = secs[e_shstrndx]
    for s in secs:
        s["sname"] = cstr(data, strtab["off"] + s["name"])
    return secs


def main(argv):
    if len(argv) not in (3, 4) or (len(argv) == 4 and argv[3] != "--check"):
        sys.exit(__doc__)
    obj, out = argv[1], argv[2]
    check = len(argv) == 4
    data = open(obj, "rb").read()
    secs = parse(data)
    for s in secs:
        if s["type"] in (SHT_REL, SHT_RELA):
            fail(f"relocation section {s['sname']} present: the bytes would depend on the link")
        if s["flags"] & SHF_ALLOC and s["sname"] != ".text" and s["size"]:
            fail(f"allocated section {s['sname']} ({s['size']} bytes): the library must be code only")
    texts = [i for i, s in enumerate(secs) if s["sname"] == ".text"]
    if len(texts) != 1:
        fail("expected exactly one .text section")
    ti = texts[0]
    text = secs[ti]
    if text["align"] != 4:
        fail(f".text alignment is {text['align']}, expected 4")
    code = data[text["off"]:text["off"] + text["size"]]
    syms = []
    maps = []
    for s in secs:
        if s["type"] != SHT_SYMTAB:
            continue
        names = secs[s["link"]]
        for k in range(s["size"] // 16):
            (st_name, value, size, info, _other, shndx) = struct.unpack_from(
                "<IIIBBH", data, s["off"] + 16 * k)
            name = cstr(data, names["off"] + st_name)
            if shndx == ti and info >> 4 == 0 and name.split(".")[0] in ("$t", "$d", "$a"):
                maps.append((value, name.split(".")[0]))
            if info >> 4 == STB_GLOBAL and info & 0xF == STT_FUNC:
                if shndx != ti:
                    fail("global function outside .text")
                if not value & 1:
                    fail(f"global function {name} lacks the Thumb bit: callers would BLX to ARM state")
                syms.append((value & ~1, size, name))
    syms.sort()
    maps.sort()
    if not maps or maps[0] != (0, "$t"):
        fail("expected a $t mapping symbol at offset 0")
    if any(k == "$a" for _, k in maps):
        fail("ARM-state code ($a) present")
    if len({v for v, _ in maps}) != len(maps):
        fail("two mapping symbols at one offset")
    ranges = []  # (start, end, kind), contiguous, covering .text
    for i, (v, k) in enumerate(maps):
        end = maps[i + 1][0] if i + 1 < len(maps) else len(code)
        if end > v:
            if ranges and ranges[-1][2] == k:
                ranges[-1] = (ranges[-1][0], end, k)
            else:
                ranges.append((v, end, k))
    for a, b, k in ranges:
        if a % 2 or b % 2 or (k == "$d" and (a % 4 or b % 4)):
            fail(f"misaligned {k} range 0x{a:x}-0x{b:x}")
    code_ranges = [(a, b) for a, b, k in ranges if k == "$t"]
    for value, size, name in syms:
        # A function may contain a literal pool, so only its entry must be code.
        if not size or value + size > len(code) or not any(a <= value < b for a, b in code_ranges):
            fail(f"global function {name} (0x{value:x}, {size} B) does not start in a code range")
    data_ranges = [(a, b) for a, b, k in ranges if k == "$d"]
    digest = hashlib.sha256(code).hexdigest()
    lines = [
        "-- GENERATED by tools/extract_release.py from the library unit src/m0crypto.S.",
        "-- Do not edit; regenerate with tools/extract_release.py.",
        f"-- .text sha256: {digest}",
        "",
        "/-! The release artifact: the exact `.text` bytes of the relocation-free library",
        "object. They are the same at any 4-byte-aligned link address. -/",
        "",
        "namespace M0Crypto.Artifacts.Release",
        "",
        f"/-- sha256 of `bytes`: {digest}. -/",
        f"def sha256 : String := \"{digest}\"",
        "",
        "/-- Byte offsets of the exported functions (Thumb bit cleared) and their sizes. -/",
    ]
    for value, size, name in syms:
        lines.append(f"def {name.removeprefix('m0c_')} : Nat := 0x{value:x}  -- {name}, {size} bytes")
    fmt = lambda rs: ", ".join(f"(0x{a:x}, 0x{b:x})" for a, b in rs)
    lines += ["", "/-- Half-open offset ranges of Thumb code (`$t`) and of literal data (`$d`),",
              "from the assembler's mapping symbols. Together they cover `bytes`. -/",
              f"def codeRanges : List (Nat × Nat) := [{fmt(code_ranges)}]",
              f"def dataRanges : List (Nat × Nat) := [{fmt(data_ranges)}]"]
    lines += ["", "/-- Length of `bytes` in bytes. Statements and proofs name this, not a literal. -/",
              f"def size : Nat := {len(code)}"]
    lines += ["", "set_option maxRecDepth 100000 in", "/-- The bytes of `.text` (`size` of them). -/", "def bytes : List (BitVec 8) := ["]
    rows = [", ".join(f"0x{b:02x}#8" for b in code[i:i + 16]) for i in range(0, len(code), 16)]
    lines.append(",\n".join("  " + r for r in rows) + "]")
    lines += ["", "set_option maxRecDepth 100000 in",
              "theorem bytes_length : bytes.length = size := by decide", "",
              "end M0Crypto.Artifacts.Release", ""]
    text_out = "\n".join(lines)
    if check:
        try:
            cur = open(out).read()
        except FileNotFoundError:
            fail(f"{out} does not exist")
        if cur != text_out:
            fail(f"{out} does not match {obj}; regenerate with tools/extract_release.py")
        print(f"ok {out} matches {obj} (sha256 {digest})")
    else:
        open(out, "w").write(text_out)
        print(f"wrote {out} ({len(code)} bytes, sha256 {digest})")


if __name__ == "__main__":
    main(sys.argv)
