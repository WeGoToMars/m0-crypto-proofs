#!/usr/bin/env python3
"""Run a Lake build under a memory budget.

    membuild.py [lake build arguments...]

Lake starts as many Lean processes as there are cores and knows nothing about memory.
This runner starts `lake build` unchanged and supervises the Lean processes it spawns:
when the memory they need together exceeds the budget, the newest ones are paused
(SIGSTOP) and resumed (SIGCONT) as the older ones finish. Nothing is killed, and the
build's result is exactly Lake's.

"Need" is the larger of a process's current memory and the peak that module reached in
an earlier run, remembered in `.lake/membuild-peaks.json`. Memory is the footprint, which
counts compressed and swapped pages; resident size alone shrinks under pressure. So the
first build reacts to memory as it grows, and later builds hold a known-heavy module back
before it starts.

Budget: half of physical memory, or M0C_BUILD_MEM_GB. Standard library only; macOS and
Linux.
"""
import ctypes
import json
import os
import signal
import subprocess
import sys
import time

PEAKS = os.path.join(".lake", "membuild-peaks.json")


def physical_bytes():
    return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")


def footprint(pid, rss):
    """Memory charged to `pid`, including compressed and swapped pages; `rss` if unknown."""
    try:
        if sys.platform == "darwin":
            # proc_pid_rusage, RUSAGE_INFO_V2: a 16-byte uuid, then 64-bit counters;
            # ri_phys_footprint is the eighth.
            buf = (ctypes.c_uint64 * 64)()
            if ctypes.CDLL("/usr/lib/libproc.dylib").proc_pid_rusage(pid, 2, ctypes.byref(buf)) == 0:
                return max(rss, buf[2 + 7])
        else:
            fields = dict(l.split(":", 1) for l in open(f"/proc/{pid}/status"))
            return sum(int(fields.get(k, "0 kB").split()[0]) for k in ("VmRSS", "VmSwap")) * 1024
    except (OSError, ValueError, AttributeError):
        pass
    return rss


def processes():
    """pid -> (ppid, rss bytes, command line)."""
    out = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,command="], capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        f = line.split(None, 3)
        if len(f) == 4:
            res[int(f[0])] = (int(f[1]), int(f[2]) * 1024, f[3])
    return res


def lean_children(root, procs):
    """Lean compiler processes descended from `root`: pid -> (memory, module source path)."""
    res = {}
    for pid, (ppid, rss, cmd) in procs.items():
        argv = cmd.split()
        if not argv or os.path.basename(argv[0]) != "lean":
            continue
        p = ppid
        while p in procs and p != root:
            p = procs[p][0]
        if p != root:
            continue
        src = next((a for a in argv[1:] if a.endswith(".lean")), None)
        if src:
            res[pid] = (footprint(pid, rss), os.path.relpath(src))
    return res


def main():
    budget = float(os.environ.get("M0C_BUILD_MEM_GB", 0)) * 2**30 or physical_bytes() / 2
    try:
        peaks = json.load(open(PEAKS))
    except (OSError, ValueError):
        peaks = {}
    build = subprocess.Popen(["lake", "build"] + sys.argv[1:])
    stopped, order, held = set(), [], set()
    try:
        while build.poll() is None:
            lean = lean_children(build.pid, processes())
            order = [p for p in order if p in lean] + sorted(p for p in lean if p not in order)
            stopped &= set(lean)
            total = 0
            for i, pid in enumerate(order):
                mem, src = lean[pid]
                peaks[src] = max(peaks.get(src, 0), mem)
                total += peaks[src]
                fits = i == 0 or total <= budget  # the oldest process always runs
                if not fits and pid not in stopped:
                    os.kill(pid, signal.SIGSTOP)
                    stopped.add(pid)
                    if src not in held:
                        held.add(src)
                        print(f"membuild: holding {src} (needs about {peaks[src] / 2**30:.1f} GB)", flush=True)
                elif fits and pid in stopped:
                    os.kill(pid, signal.SIGCONT)
                    stopped.discard(pid)
            time.sleep(1)
    finally:
        for pid in stopped:
            try:
                os.kill(pid, signal.SIGCONT)
            except ProcessLookupError:
                pass
        if build.poll() is None:
            build.terminate()
        os.makedirs(".lake", exist_ok=True)
        json.dump(peaks, open(PEAKS, "w"), indent=0, sort_keys=True)
    return build.returncode


if __name__ == "__main__":
    sys.exit(main())
