#!/usr/bin/env python3
"""Mutation check for the BLAKE2s release code.

    python3 -I tools/mutate_blake2s.py [WORKDIR]      (default WORKDIR /tmp/m0c-mut-b2s)

Works on copies; neither the library nor the proofs tree is modified. The library is the
parent of this proofs tree (its `proofs` submodule) or M0C_LIB; the script stops before copying
anything unless it holds the BLAKE2s release sources. WORKDIR must be new, empty or a
previous WORKDIR of this script. For each deliberate
bug below it applies the edit to src/blake2s_*.S in a copy of the library, rebuilds the
release object, then runs three checks:

* QEMU: tools/test_qemu.sh of the copy (does a test image see the bug?);
* executable checks: regenerates assets/blake2s/artifact/M0Crypto/Artifacts/Release.lean in a
  copy of the proofs tree and runs that asset's native `release_check` executable (the checks
  the proofs build runs in Lean's interpreter, Thumb/ReleaseCheck/Blake2s*);
* proofs: builds, in that asset's workspace, every module with `Blake2s` in its name except
  the interpreted release-check modules (the BLAKE2s proofs and certificates). The modules
  that fail are listed. A mutant is REJECTED by the proofs when Lean reports an error in a
  failing module (tools/mutation_run.py). A killed or crashed worker or a timeout is an ERROR.

Every mutant must be rejected by the proofs. Mutants marked "qemu-blind" are expected to pass
QEMU (they show that tests alone would miss them). QEMU DETECTS a mutant when the BLAKE2s
image reports a failing check or stops with a fault, and reports TIMEOUT when the image hangs. A
QEMU that does not start is an ERROR. The first run builds the copy from
scratch (several minutes); each mutant then costs one rebuild of everything that imports the
artifact and has `Blake2s` in its name. Exit status 1 if a mutant is not rejected, does not change the bytes, or a tool
fails.
"""
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))   # python3 -I leaves the script directory out
from native_check import native_check
from mutation_run import lake_build as lean_build, lean_verdict
LIB = os.path.abspath(os.environ.get("M0C_LIB", os.path.join(ROOT, "..")))
LIB_FILES = ["include/m0crypto/blake2s.h", "src/blake2s_stream.S", "tools/build_lib.sh"]
MARKER = ".m0c-mutate-blake2s"
CS, CP, ST, CPY = "blake2s_compress.S", None, "blake2s_stream.S", "blake2s_copy.S"

# (name, file, original, mutated, expectation). Each original occurs exactly once.
MUTANTS = [
    ("rotation 12 -> 11 in B2_G", CS,
     "    movs r4, #12\n    rors r1, r4\n", "    movs r4, #11\n    rors r1, r4\n", ""),
    ("swapped SIGMA entries in round 2", CS,
     "B2_ROUND 14,10,4,8,9,15,13,6,", "B2_ROUND 10,14,4,8,9,15,13,6,", ""),
    ("f0 not XORed into v14", CS,
     "    eors r6, r0\n    mov r11, r6                 /* v14", "    mov r6, r6\n    mov r11, r6                 /* v14", ""),
    ("padding word store writes two bytes", ST,
     "    str r0, [r1, r6]\n    adds r6, #4\n", "    strh r0, [r1, r6]\n    adds r6, #4\n", ""),
    ("count carry dropped (adcs -> adds)", ST,
     "    adds r2, #BLOCK_BYTES\n    adcs r3, r0\n", "    adds r2, #BLOCK_BYTES\n    adds r3, r0\n", "qemu-blind"),
    ("branch on a message byte in update", ST,
     "    ldrb r3, [r1]\n    strb r3, [r0]\n    adds r1, #1\n    adds r0, #1\n    subs r2, #1\n    bne .Lb2u_bytes\n",
     "    ldrb r3, [r1]\n    strb r3, [r0]\n    adds r1, #1\n    adds r0, #1\n    cmp r3, #0\n    beq 9f\n9:  subs r2, #1\n    bne .Lb2u_bytes\n",
     "qemu-blind"),
    ("message-indexed load in B2_G", CS,
     "    adds r0, r0, r4\n    eors r3, r0\n    movs r4, #16\n",
     "    adds r0, r0, r4\n    lsls r4, r4, #31\n    lsrs r4, r4, #29\n    ldr r4, [r4]\n    eors r3, r0\n    movs r4, #16\n",
     "qemu-blind"),
    ("used load moved to a buf load", ST,
     "    ldr r7, [r4, #CTX_USED]     /* the only load of used: entry, before any store */\n    cmp r6, #0\n",
     "    ldr r7, [r4, #CTX_BUF]      /* the only load of used: entry, before any store */\n    cmp r6, #0\n", ""),
    ("copy reads one byte past src", CPY,
     "    ldrb r3, [r1]\n    strb r3, [r0]\n    adds r1, #1\n    adds r0, #1\n    subs r2, #1\n    bne .Lb2c_byte_loop\n",
     "    ldrb r3, [r1]\n    ldrb r7, [r1, r2]\n    strb r3, [r0]\n    adds r1, #1\n    adds r0, #1\n    subs r2, #1\n    bne .Lb2c_byte_loop\n",
     "qemu-blind"),
    ("deeper compress frame without a contract change", CS,
     "#define LOCALS      100 ", "#define LOCALS      140 ", ""),
    ("frame clear one batch short", CS,
     "    .rept LOCALS/20\n", "    .rept LOCALS/20-1\n", ""),
    ("r12 not cleared at the compress exit", CS,
     "    .endr\n    mov r12, r0\n", "    .endr\n    mov r12, r12\n", ""),
    ("update returns with r3 not cleared", ST,
     "/* no message byte or digest word left in r0-r3 */\n    movs r1, #0\n    movs r2, #0\n    movs r3, #0\n",
     "/* no message byte or digest word left in r0-r3 */\n    movs r1, #0\n    movs r2, #0\n    movs r2, #0\n", ""),
]


def run(cmd, cwd=None, env=None, timeout=3600):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)


def sync(src, dst, excludes):
    cmd = ["rsync", "-a", "--delete"] + [f"--exclude={e}" for e in excludes] + [src + "/", dst + "/"]
    r = run(cmd)
    if r.returncode:
        sys.exit("rsync failed: " + r.stderr)


def build_lib(libdir):
    r = run([os.path.join(libdir, "tools", "build_lib.sh"), "blake2s"])
    if r.returncode:
        return None, (r.stdout + r.stderr).strip()[-300:]
    return os.path.join(libdir, "build", "lib", "blake2s", "m0crypto_blake2s.o"), ""


def workspace(pdir):
    return os.path.join(pdir, "assets", "blake2s")


def extract(obj, pdir):
    out = os.path.join(workspace(pdir), "artifact", "M0Crypto", "Artifacts", "Release.lean")
    return run([sys.executable, "-I", os.path.join(pdir, "tools", "extract_release.py"), obj, out])


# Seconds for one run of the executable checks (they take about 10 s on the release object).
# A mutant can make the model run to the step limit, which the evaluator handles slowly; that
# is reported as TIMEOUT. It is not a detection and not an error: the proofs decide.
EXEC_TIMEOUT = 300


def blake2s_modules(pdir):
    """Every Lean module with `Blake2s` in its file name, except the interpreted release
    checks (the native executable runs those) and the asset root, which imports them."""
    base = os.path.join(pdir, "lean")
    return sorted(os.path.relpath(os.path.join(d, f), base)[:-5].replace(os.sep, ".")
                  for d, _, fs in os.walk(os.path.join(base, "M0Crypto")) for f in fs
                  if f.endswith(".lean") and "Blake2s" in f and os.path.basename(d) != "Assets"
                  and not re.match(r"Blake2s(Shard\d+|Pairwise)\.lean$", f))


def lake_build(pdir):
    """(ACCEPTED | REJECTED | ERROR, failing modules, detail) of the BLAKE2s proofs."""
    v, detail = lean_verdict(lean_build(workspace(pdir), blake2s_modules(pdir), 3600))
    verdict = {"PASS": "ACCEPTED", "DETECTED": "REJECTED"}.get(v, "ERROR")
    return verdict, detail.split() if v == "DETECTED" else [], detail


def image_verdict(out, img):
    """(PASS | DETECTED | TIMEOUT | ERROR, details) of one image in test_qemu.sh output."""
    if f"== {img}\n" not in out:
        return "ERROR", [f"{img} did not run"]
    log = out.split(f"== {img}\n")[1].split("\n== ")[0]
    status = re.search(rf"^FAIL: {img}: qemu exit status (\d+)", out, re.M)
    fails = sorted({l.split(" 0x")[0][5:] for l in log.splitlines() if l.startswith("FAIL ")})
    if fails or "RESULT: FAIL" in log:
        return "DETECTED", fails or ["RESULT: FAIL"]
    if status is None:
        return ("PASS", []) if "RESULT: PASS" in log else ("ERROR", [f"{img}: no result line"])
    code = int(status.group(1))
    if code == 124:
        return "TIMEOUT", [f"{img} hangs"]
    if code in (126, 127):
        return "ERROR", [f"{img}: QEMU did not start (status {code})"]
    if code == 0:   # exit 0 without RESULT: PASS
        return "ERROR", [f"{img}: no result line"]
    return "DETECTED", [f"{img} faults (status {code})"]


def qemu(libdir):
    """(PASS | DETECTED | TIMEOUT | ERROR, details) of the BLAKE2s test images."""
    r = run([os.path.join(libdir, "tools", "test_qemu.sh"), "blake2s"], env=dict(os.environ, TIMEOUT="60"))
    out = r.stdout + r.stderr
    vs = [image_verdict(out, img) for img in ("test_blake2s", "test_irq_blake2s")]
    for v in ("ERROR", "DETECTED", "TIMEOUT"):
        if any(x == v for x, _ in vs):
            return v, [d for x, ds in vs if x == v for d in ds]
    return "PASS", []


def check_dirs():
    """Stop before any copy unless LIB is the library and WORK is ours to overwrite."""
    missing = [f for f in LIB_FILES if not os.path.isfile(os.path.join(LIB, f))]
    if missing:
        sys.exit(f"{LIB} is not the m0-crypto library (no {missing[0]}): set M0C_LIB")
    if os.path.isdir(WORK) and os.listdir(WORK) and not os.path.exists(os.path.join(WORK, MARKER)):
        sys.exit(f"{WORK} is not empty and was not made by this script")
    os.makedirs(WORK, exist_ok=True)
    open(os.path.join(WORK, MARKER), "w").close()


def main():
    libd, prd = os.path.join(WORK, "lib"), os.path.join(WORK, "proofs")
    check_dirs()
    sync(LIB, libd, [".git", "proofs", "build", "bench"])
    # First run: copy the built tree (.lake included) so only changed modules rebuild.
    sync(ROOT, prd, [".git", "build", "__pycache__"] + ([".lake"] if os.path.isdir(os.path.join(workspace(prd), ".lake")) else []))
    obj, err = build_lib(libd)
    if not obj:
        sys.exit("baseline library build failed: " + err)
    base_obj = open(obj, "rb").read()
    if extract(obj, prd).returncode:
        sys.exit("baseline extract failed")
    verdict, failed, detail = lake_build(prd)
    if verdict != "ACCEPTED":
        sys.exit(f"baseline proofs do not build: {verdict} {detail}")
    ex, why = native_check(workspace(prd))
    if ex != "PASS":
        sys.exit("baseline executable checks do not pass: " + why)
    print("baseline: proofs build, library object %d bytes" % len(base_obj))
    bad = 0
    rows = []
    for name, f, old, new, expect in MUTANTS:
        path = os.path.join(libd, "src", f)
        orig = open(path).read()
        if orig.count(old) != 1:
            print(f"ERROR {name}: original occurs {orig.count(old)} times"); bad += 1; continue
        open(path, "w").write(orig.replace(old, new))
        try:
            obj, err = build_lib(libd)
            if not obj:
                print(f"ERROR {name}: library build failed: {err}"); bad += 1; continue
            if open(obj, "rb").read() == base_obj:
                print(f"ERROR {name}: mutant does not change the bytes"); bad += 1; continue
            q, qk = qemu(libd)
            if extract(obj, prd).returncode:
                print(f"ERROR {name}: extract failed"); bad += 1; continue
            ex, why = native_check(workspace(prd), EXEC_TIMEOUT)
            if ex == "ERROR" and "timed out" in why:
                ex = "TIMEOUT"
            verdict, failed, detail = lake_build(prd)
            if verdict != "REJECTED" or "ERROR" in (q, ex):
                bad += 1
                if ex == "ERROR":
                    print(f"ERROR {name}: {why}")
                if verdict == "ERROR":
                    print(f"ERROR {name}: proofs build: {detail}")
            if expect == "qemu-blind" and q != "PASS":
                print(f"NOTE {name}: expected QEMU to miss it, but it reported {q}")
            rows.append((name, q, ",".join(qk), verdict, " ".join(m.replace("M0Crypto.", "") for m in failed[:6]), ex))
            print(f"{verdict:9} qemu={q:8} exec={ex:8} {name}\n    first failing modules: {rows[-1][4]}", flush=True)
        finally:
            open(path, "w").write(orig)
    # Leave the copy at the baseline artifact.
    obj, _ = build_lib(libd)
    extract(obj, prd)
    print("\n| Mutant | QEMU | Executable checks | Proofs | Failing modules (first six) |\n|---|---|---|---|---|")
    for r in rows:
        print(f"| {r[0]} | {r[1]} | {r[5]} | {r[3]} | {r[4]} |")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    WORK = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else "/tmp/m0c-mut-b2s")
    main()
