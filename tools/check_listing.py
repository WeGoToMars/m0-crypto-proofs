#!/usr/bin/env python3
"""Compare the Lean model's decoding of the release artifact with llvm-objdump.

Runs lean/DumpListing.lean (the model's decoder and renderer, Thumb/Listing.lean)
and `llvm-objdump -d` on build/lib/speed/m0crypto.o, normalises both, and requires
the same instruction at the same offset for every instruction of every code range.
Branch lines compare the target address only; PC-relative loads also compare the
literal address. objdump's `.word` lines (literal pools) are skipped; the Lean
side's ranges come from the same mapping symbols.

Usage: check_listing.py OBJDUMP OBJECT
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def objdump_lines(objdump, obj):
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", obj], check=True,
                         capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        if re.search(r"\s\.(word|short|byte)\s", line):
            continue  # literal pool data
        m = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if not m:
            continue
        off, mn, ops = int(m.group(1), 16), m.group(2), m.group(3)
        if mn.startswith("."):
            continue
        comment = ""
        if "@" in ops:
            ops, comment = ops.split("@", 1)
        ops = " ".join(ops.split())
        if mn == "bl" or re.fullmatch(r"b(eq|ne|hs|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)?", mn):
            ops = ops.split()[0]
        elif mn == "ldr" and "[pc" in ops:
            ops += " @ " + comment.split()[0]
        res[off] = f"{mn} {ops}".strip()
    return res


def lean_lines():
    out = subprocess.run(["lake", "env", "lean", "--run", "lean/DumpListing.lean"], cwd=ROOT,
                         check=True, capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        if line.startswith("error"):
            sys.exit(f"check_listing: model sweep failed: {line}")
        off, text = line.split("\t")
        res[int(off, 16)] = text
    return res


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__)
    want, got = objdump_lines(argv[1], argv[2]), lean_lines()
    bad = [o for o in sorted(set(want) | set(got)) if want.get(o) != got.get(o)]
    for o in bad[:20]:
        print(f"  0x{o:x}: objdump {want.get(o)!r}  model {got.get(o)!r}")
    if bad:
        sys.exit(f"check_listing: {len(bad)} of {len(want)} instructions differ")
    print(f"ok: model decoding matches llvm-objdump at all {len(want)} instruction offsets")


if __name__ == "__main__":
    main(sys.argv)
