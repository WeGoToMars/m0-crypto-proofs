#!/usr/bin/env python3
"""Mutation check for the X25519 release code.

    python3 -I tools/mutate_x25519.py --dry-run [--obj OBJ] [--work DIR]
    python3 -I tools/mutate_x25519.py --exec    [--obj OBJ] [--work DIR] [--cert] [--only NAME ...]
    python3 -I tools/mutate_x25519.py --list SYMBOL [--obj OBJ]

Unlike tools/mutate_aead.py and tools/mutate_blake2s.py, which edit the assembly source and
rebuild, each mutant here is a single 16-bit instruction patched into a copy of the release
object (default: the library's build/lib/x25519/m0crypto_x25519.o). The patch keeps every size and offset, so
the routine offsets that `Thumb/ReleaseCheck/X25519Cases.lean` and the certificate take from
`llvm-nm -S` stay valid, and src/x25519.S (a generated file compared by tools/check.sh) is never
touched. Targets are found by pattern: a window of consecutive instructions, as `llvm-objdump`
prints them, that must occur exactly once inside the symbol's range from `llvm-nm -S`. No
address is written down here.

Modes:

* --dry-run: for every mutant, locate the window, patch one halfword, disassemble the patched
  symbol and check that exactly one instruction changed, at the target, into the expected text;
  then run tools/extract_release.py on the patched object (its structural checks) into WORK.
  Nothing else is run. This is the part that needs no Lean.
* --exec: the dry run, then the executable release checks (the `#guard`s of the modules below) on each mutant, in a
  copy of the proofs tree under WORK (rsync, .lake included, so only the modules that import
  the artifact rebuild): regenerate the X25519 asset's Artifacts/Release.lean from the patched
  object and build, in that asset's workspace (assets/x25519),
  M0Crypto.Thumb.ReleaseCheck.X25519Routines and .X25519Shard0-3. A mutant is DETECTED when
  one of those modules fails with "release check FAILED" or a failing `#guard`. Any other
  failure (an upstream module, a timeout) is a tool ERROR, never a detection.
  --cert also builds M0Crypto.Release.ConstantTime.X25519Entry (the constant-time
  certificate; about 5 minutes and up to 6 GB per mutant).
* --list SYMBOL: print the symbol's instructions in the normalised form the patterns use.

Expected catchers (column `expect`):

* exec   the executable release checks must detect it;
* cert   timing-only: the executable checks are expected to miss it, the constant-time
         certificate (--cert) and `x25519_constant_time` must not.
Every mutant also names the proof that must reject it (`proof`); those are
recorded, not run. Lean runs go under `nice -n 5` with an alarm (--timeout seconds per build).
Exit status 1 if a mutant does not apply to exactly one instruction, an `exec` mutant is not
detected by the executable checks, a --cert run misses a mutant, or a tool fails.
"""
import argparse
import os
import re
import shutil
import struct
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.abspath(os.environ.get("M0C_LIB", os.path.join(ROOT, "..")))
LLVM = os.environ.get("M0C_LLVM_BIN", "/opt/homebrew/opt/llvm/bin")
CASES = os.path.join(ROOT, "lean", "M0Crypto", "Thumb", "ReleaseCheck", "X25519Cases.lean")
WS = os.path.join("assets", "x25519")
REL = os.path.join(WS, "artifact", "M0Crypto", "Artifacts", "Release.lean")
EXEC_MODULES = ["M0Crypto.Thumb.ReleaseCheck.X25519Routines"] + [
    f"M0Crypto.Thumb.ReleaseCheck.X25519Shard{i}" for i in range(4)]
CERT_MODULES = ["M0Crypto.Release.ConstantTime.X25519Entry"]
SYMBOLS = ["m0c_fe_mul", "m0c_fe_sqr", "m0c_fe_mulc_add", "m0c_x25519"]


def field(lo, width, value):
    """Set bits lo .. lo+width-1 of the halfword to `value`."""
    mask = ((1 << width) - 1) << lo
    return lambda hw: (hw & ~mask) | ((value << lo) & mask)


def const(new):
    return lambda hw: new


ADCS_TO_SBCS = field(6, 4, 0b0110)   # data processing 010000 op Rm Rdn: ADC = 0101, SBC = 0110
SBCS_TO_ADCS = field(6, 4, 0b0101)
NOP = 0x46C0                         # mov r8, r8
BHS_NEXT = 0xD2FF                    # bhs to the next instruction (offset -1 halfword)

# Each mutant: name, symbol, window (normalised instruction texts, consecutive), index of the
# target inside the window, transform of its halfword, regex the new text must match,
# expected catcher (exec / cert), and the proof that must reject it.
MUTANTS = [
    # m0c_fe_mul
    dict(name="fe_mul: Karatsuba sign mask sbcs -> adcs", sym="m0c_fe_mul",
         window=["str r2, [sp, #0x8c]", "mov r12, r1", "mov r11, r2", "ldm r1!, {r4, r6}", "ldm r2!, {r5, r7}", "mov r8, r5",
                 "mov r10, r7", "subs r0, r6, r4", "sbcs r2, r2"], at=8, patch=SBCS_TO_ADCS, new=r"adcs r2, r2$",
         expect="exec", proof="m0c_fe_mul contract"),
    dict(name="fe_mul: reduction constant 38 -> 39", sym="m0c_fe_mul",
         window=["movs r7, #0x26", "movs r2, #0x0", "uxth r6, r4"], at=0,
         patch=field(0, 8, 39), new=r"movs r7, #0x27$",
         expect="exec", proof="m0c_fe_mul contract"),
    dict(name="fe_mul: bit-255 fold shift 31 -> 30", sym="m0c_fe_mul",
         window=["lsls r4, r4, #0x1", "lsrs r3, r5, #0x1f", "adds r4, r4, r3",
                 "lsls r5, r5, #0x1"], at=1, patch=field(6, 5, 30), new=r"lsrs r3, r5, #0x1e$",
         expect="exec", proof="m0c_fe_mul contract"),
    dict(name="fe_mul: top limb adds r1 swapped for r3", sym="m0c_fe_mul",
         window=["mov r2, r12", "adds r2, r2, r1", "str r2, [r0, #0x1c]"], at=1,
         patch=field(6, 3, 3), new=r"adds r2, r2, r3$",
         expect="exec", proof="m0c_fe_mul contract"),
    # m0c_fe_sqr
    dict(name="fe_sqr: doubled cross term shift 17 -> 16", sym="m0c_fe_sqr",
         window=["str r1, [sp, #0x88]", "mov r12, r1", "ldm r1!, {r4, r6}", "subs r0, r6, r4",
                 "sbcs r1, r1", "eors r0, r1", "subs r0, r0, r1", "lsrs r1, r0, #0x10",
                 "uxth r0, r0", "movs r2, r1", "muls r2, r0, r2", "muls r1, r1, r1",
                 "muls r0, r0, r0", "lsls r3, r2, #0x11"], at=13,
         patch=field(6, 5, 16), new=r"lsls r3, r2, #0x10$",
         expect="exec", proof="m0c_fe_sqr contract"),
    dict(name="fe_sqr: reduction carry adcs -> sbcs", sym="m0c_fe_sqr",
         window=["adds r5, r5, r6", "adcs r4, r2", "adds r5, r5, r3", "adcs r4, r2",
                 "mov r3, r12"], at=1, patch=ADCS_TO_SBCS, new=r"sbcs r4, r2$",
         expect="exec", proof="m0c_fe_sqr contract"),
    # m0c_fe_mulc_add
    dict(name="fe_mulc_add: top limb high-half shift 17 -> 16", sym="m0c_fe_mulc_add",
         window=["ldr r3, [r1, #0x1c]", "uxth r4, r3", "lsrs r3, r3, #0x10", "muls r4, r7, r4",
                 "muls r3, r7, r3", "lsls r5, r3, #0x11"], at=5,
         patch=field(6, 5, 16), new=r"lsls r5, r3, #0x10$",
         expect="exec", proof="m0c_fe_mulc_add contract"),
    dict(name="fe_mulc_add: fold constant 19 -> 18", sym="m0c_fe_mulc_add",
         window=["movs r5, #0x13", "muls r3, r5, r3"], at=0,
         patch=field(0, 8, 18), new=r"movs r5, #0x12$",
         expect="exec", proof="m0c_fe_mulc_add contract"),
    # m0c_x25519
    dict(name="x25519: ladder count 254 -> 253", sym="m0c_x25519",
         window=["movs r0, #0xfe", "str r0, [sp, #0x140]"], at=0,
         patch=field(0, 8, 253), new=r"movs r0, #0xfd$",
         expect="exec", proof="ladder loop / x25519_correct"),
    dict(name="x25519: scalar clamp shift 3 -> 2", sym="m0c_x25519",
         window=["lsrs r4, r4, #0x3", "lsls r4, r4, #0x3", "str r4, [sp, #0x120]"], at=0,
         patch=field(6, 5, 2), new=r"lsrs r4, r4, #0x2$",
         expect="exec", proof="prologue / x25519_correct"),
    dict(name="x25519: ladder X2+Z2 carry adcs -> sbcs", sym="m0c_x25519",
         window=["movs r0, #0xfe", "str r0, [sp, #0x140]", "add r0, sp, #0xa0", "add r1, sp, #0x20",
                 "add r2, sp, #0x40", "ldm r1!, {r3, r4}", "ldm r2!, {r5, r6}", "adds r3, r3, r5",
                 "adcs r4, r6"], at=8, patch=ADCS_TO_SBCS, new=r"sbcs r4, r6$",
         expect="exec", proof="ladder step / x25519_correct"),
    dict(name="x25519: last wipe store skipped", sym="m0c_x25519",
         window=["stm r0!, {r1, r2, r3, r4, r5}", "add sp, #0x1e0"], at=0,
         patch=const(NOP), new=r"mov r8, r8$",
         expect="exec", proof="wipe / x25519_correct (Result)"),
    dict(name="x25519: r12 not cleared at exit", sym="m0c_x25519",
         window=["add sp, #0x1e0", "movs r0, #0x0", "mov r12, r0"], at=2,
         patch=const(0x46E4), new=r"mov r12, r12$",
         expect="exec", proof="epilogue / x25519_correct (Result)"),
    dict(name="x25519: dead store -> branch on secret carry", sym="m0c_x25519",
         window=["adcs r1, r2", "str r1, [r0, #0x1c]", "lsls r1, r1, #0x1",
                 "lsrs r1, r1, #0x1", "str r1, [r0, #0x1c]"], at=1,
         patch=const(BHS_NEXT), new=r"bhs ",
         expect="cert", proof="x25519_constant_time"),
]


def tool(name):
    p = os.path.join(LLVM, name)
    return p if os.path.exists(p) else shutil.which(name) or sys.exit(f"{name} not found")


def run(cmd, cwd=None, env=None, timeout=None):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)


def text_offset(data):
    """File offset and size of .text in an ELF32 little-endian object."""
    e_shoff, = struct.unpack_from("<I", data, 32)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 46)
    secs = [struct.unpack_from("<IIIIIIIIII", data, e_shoff + i * e_shentsize) for i in range(e_shnum)]
    stroff = secs[e_shstrndx][4]
    for s in secs:
        name = data[stroff + s[0]:data.index(b"\0", stroff + s[0])]
        if name == b".text":
            return s[4], s[5]
    sys.exit("no .text section")


def symbols(obj):
    """{name: (offset, size)} from llvm-nm -S, local symbols included."""
    out = run([tool("llvm-nm"), "-S", "--defined-only", obj]).stdout
    syms = {}
    for line in out.splitlines():
        f = line.split()
        if len(f) == 4 and f[2].lower() == "t":
            syms[f[3]] = (int(f[0], 16), int(f[1], 16))
    missing = [s for s in SYMBOLS if s not in syms]
    if missing:
        sys.exit(f"llvm-nm: missing {missing}")
    return syms


LINE = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{4,8} )+)\s*\t(\S+)(?:\t(.*))?$")


def disasm(obj, start, size):
    """[(offset, encoding hex, normalised text)] of [start, start+size), data words skipped."""
    out = run([tool("llvm-objdump"), "-d", "--triple=thumbv6m-none-eabi",
               f"--start-address={start:#x}", f"--stop-address={start + size:#x}", obj])
    if out.returncode:
        sys.exit("llvm-objdump failed: " + out.stderr)
    ins = []
    for line in out.stdout.splitlines():
        m = LINE.match(line)
        if not m or m.group(3).startswith("."):
            continue
        ops = (m.group(4) or "").split("@")[0]
        ins.append((int(m.group(1), 16), m.group(2).strip(),
                    " ".join((m.group(3) + " " + ops).split())))
    return ins


def locate(ins, window, at):
    texts = [t for _, _, t in ins]
    hits = [i for i in range(len(texts) - len(window) + 1) if texts[i:i + len(window)] == window]
    return hits


def make_mutant(obj_bytes, syms, mutant, obj_path, workdir):
    """Patch one mutant; returns (patched path, report line) or (None, error)."""
    off, size = syms[mutant["sym"]]
    ins = disasm(obj_path, off, size)
    hits = locate(ins, mutant["window"], mutant["at"])
    if len(hits) != 1:
        return None, f"window occurs {len(hits)} times in {mutant['sym']}"
    addr, enc, old = ins[hits[0] + mutant["at"]]
    if len(enc) != 4:
        return None, f"target {old!r} is not a 16-bit instruction"
    toff, _ = text_offset(obj_bytes)
    pos = toff + addr
    hw, = struct.unpack_from("<H", obj_bytes, pos)
    new_hw = mutant["patch"](hw)
    if new_hw == hw:
        return None, "patch does not change the halfword"
    data = bytearray(obj_bytes)
    struct.pack_into("<H", data, pos, new_hw)
    slug = re.sub(r"[^a-z0-9]+", "-", mutant["name"].lower()).strip("-")
    path = os.path.join(workdir, "mutants", slug + ".o")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "wb").write(bytes(data))
    after = disasm(path, off, size)
    diff = [(a, b) for a, b in zip(ins, after) if a != b]
    if len(after) != len(ins) or len(diff) != 1 or diff[0][0][0] != addr:
        return None, f"patched disassembly changes {len(diff)} instructions (lengths {len(ins)}/{len(after)})"
    new = diff[0][1][2]
    if not re.match(mutant["new"], new):
        return None, f"patched text {new!r} does not match {mutant['new']!r}"
    changed = sum(1 for a, b in zip(obj_bytes, data) if a != b)
    if changed > 2:
        return None, f"{changed} bytes changed"
    rel = os.path.join(workdir, "mutants", slug + ".lean")
    x = run([sys.executable, "-I", os.path.join(ROOT, "tools", "extract_release.py"), path, rel])
    if x.returncode:
        return None, "extract_release rejects the patched object: " + (x.stdout + x.stderr).strip()[-200:]
    return path, (f"{mutant['sym']}+{addr - off:#x} (.text {addr:#x}): {hw:04x} {old}  ->  "
                  f"{new_hw:04x} {new}")


def check_offsets(syms):
    """The routine sizes in X25519Cases.lean must equal llvm-nm's, and the routines must lie back
    to back below m0c_x25519 (the file derives their offsets from that)."""
    src = open(CASES).read()
    order = [("feMul", "m0c_fe_mul"), ("feSqr", "m0c_fe_sqr"), ("feMulcAdd", "m0c_fe_mulc_add")]
    for k, s in order:
        m = re.search(rf"^def {k}Size : Nat := (0x[0-9a-f]+)", src, re.M)
        if not m or int(m.group(1), 16) != syms[s][1]:
            sys.exit(f"X25519Cases.lean {k}Size differs from llvm-nm {s}")
    ends = [syms[s][0] + syms[s][1] for _, s in order]
    starts = [syms[s][0] for _, s in order[1:]] + [syms["m0c_x25519"][0]]
    if ends != starts:
        sys.exit("field routines are not back to back below m0c_x25519")


def lake_build(pdir, modules, timeout):
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    mb = os.path.join(pdir, "tools", "membuild.py")
    cmd = [sys.executable, mb] if os.path.exists(mb) else ["lake", "build"]
    full = ["nice", "-n", "5", "perl", "-e", f"alarm {timeout}; exec @ARGV"] + cmd + modules
    r = run(full, cwd=os.path.join(pdir, WS), env=env)
    out = r.stdout + r.stderr
    failed = sorted(set(re.findall(r"^✖ \[\d+/\d+\] Building (\S+)", out, re.M)))
    return r.returncode, failed, out


def classify(rc, failed, out, modules):
    """PASS / DETECTED / ERROR for one build of `modules`."""
    if rc == 0:
        return "PASS", ""
    caught = re.search(r"release check FAILED: [^\n]*|#guard[^\n]*|did not evaluate to `true`[^\n]*", out)
    if failed and set(failed) <= set(modules) and caught:
        return "DETECTED", caught.group(0)[:160]
    if rc in (-14, 142) or "Alarm clock" in out:
        return "ERROR", "timeout"
    return "ERROR", f"rc {rc}, failing {failed[:4]}: " + " | ".join(out.strip().splitlines()[-3:])[:200]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--dry-run", action="store_true")
    g.add_argument("--exec", action="store_true")
    g.add_argument("--list", metavar="SYMBOL")
    ap.add_argument("--obj", default=os.path.join(LIB, "build", "lib", "x25519", "m0crypto_x25519.o"))
    ap.add_argument("--work", default="/tmp/m0c-mut-x25519")
    ap.add_argument("--cert", action="store_true")
    ap.add_argument("--only", nargs="*", default=None, help="substrings of mutant names")
    ap.add_argument("--timeout", type=int, default=3600, help="seconds per Lean build")
    args = ap.parse_args()

    obj = os.path.abspath(args.obj)
    syms = symbols(obj)
    if args.list:
        off, size = syms[args.list]
        for addr, enc, t in disasm(obj, off, size):
            print(f"{addr - off:#06x} {enc:9} {t}")
        return 0

    # The object must be the one the proofs bind (read-only comparison).
    chk = run([sys.executable, "-I", os.path.join(ROOT, "tools", "extract_release.py"), obj,
               os.path.join(ROOT, REL), "--check"])
    if chk.returncode:
        sys.exit(f"the object differs from {REL}: " + chk.stdout + chk.stderr)
    check_offsets(syms)
    base = open(obj, "rb").read()
    os.makedirs(args.work, exist_ok=True)

    chosen = [m for m in MUTANTS if not args.only or any(s in m["name"] for s in args.only)]
    if not args.cert and not args.dry_run:
        skipped = [m["name"] for m in chosen if m["expect"] == "cert"]
        chosen = [m for m in chosen if m["expect"] != "cert"]
        for n in skipped:
            print(f"SKIP {n}: only the certificate is expected to catch it; rerun with --cert")
    per_sym = {s: sum(m["sym"] == s for m in chosen) for s in SYMBOLS}
    print(f"object {obj}\n{len(chosen)} mutants: " + ", ".join(f"{s} {n}" for s, n in per_sym.items()))
    bad, built = 0, []
    for m in chosen:
        path, msg = make_mutant(base, syms, m, obj, args.work)
        print(f"{'APPLIES' if path else 'NOAPPLY':8} {m['name']}\n         {msg}")
        bad += path is None
        built.append((m, path))
    if args.dry_run:
        print(f"\n{len(chosen) - bad}/{len(chosen)} mutants apply to exactly one instruction")
        return 1 if bad else 0

    pdir = os.path.join(args.work, "proofs")
    excl = [".git", "build", "__pycache__"] + ([".lake"] if os.path.isdir(os.path.join(pdir, WS, ".lake")) else [])
    r = run(["rsync", "-a", "--delete"] + [f"--exclude={e}" for e in excl] + [ROOT + "/", pdir + "/"])
    if r.returncode:
        sys.exit("rsync failed: " + r.stderr)
    rel = os.path.join(pdir, REL)

    def extract(o):
        return run([sys.executable, "-I", os.path.join(pdir, "tools", "extract_release.py"), o, rel]).returncode

    modules = EXEC_MODULES + (CERT_MODULES if args.cert else [])
    if extract(obj):
        sys.exit("baseline extract failed")
    rc, failed, out = lake_build(pdir, modules, args.timeout)
    if rc:
        sys.exit("baseline checks do not build: " + " ".join(failed) + "\n" + out[-600:])
    print("baseline: executable checks" + (" and certificate" if args.cert else "") + " build")
    rows = []
    try:
        for m, path in built:
            if path is None:
                rows.append((m, "NOAPPLY", "", "")); continue
            if extract(path):
                print(f"ERROR {m['name']}: extract failed"); bad += 1; continue
            rc, failed, out = lake_build(pdir, EXEC_MODULES, args.timeout)
            ex, why = classify(rc, failed, out, EXEC_MODULES)
            ce = "not run"
            if args.cert:
                rc2, failed2, out2 = lake_build(pdir, CERT_MODULES, args.timeout)
                ce = "PASS" if rc2 == 0 else ("DETECTED" if set(failed2) <= set(CERT_MODULES) and failed2
                                              else "ERROR")
            ok = "ERROR" not in (ex, ce) and (
                (m["expect"] == "exec" and ex == "DETECTED") or
                (m["expect"] == "cert" and ce == "DETECTED"))
            if m["expect"] == "cert" and ex == "DETECTED":
                print(f"NOTE {m['name']}: expected the executable checks to miss it")
            bad += not ok
            rows.append((m, ex, ce, why))
            print(f"{'ok' if ok else 'FAIL':4} exec={ex:8} cert={ce:8} {m['name']}\n     {why}", flush=True)
    finally:
        extract(obj)   # leave the copy at the baseline artifact
    print("\n| Symbol | Mutant | Expected | Executable checks | Certificate | Future proof |\n|---|---|---|---|---|---|")
    for m, ex, ce, _ in rows:
        print(f"| {m['sym']} | {m['name']} | {m['expect']} | {ex} | {ce} | {m['proof']} |")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
