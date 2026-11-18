#!/usr/bin/env python3
"""Run a Lake build under a memory budget.

    membuild.py [lake build arguments...]

Lake starts as many Lean processes as there are cores and knows nothing about memory.
This runner starts `lake build` unchanged and supervises the Lean processes it spawns:
when the memory they need together exceeds the budget, the newest ones are paused
(SIGSTOP) and resumed (SIGCONT) as the older ones finish. Below the hard limit nothing is
killed, and the build's result is exactly Lake's.

"Need" is the larger of a process's current memory and the peak that module reached in
an earlier successful run, remembered in `.lake/membuild-peaks.json`. A module with no remembered peak
is taken to need M0C_BUILD_UNKNOWN_GB (default 3), so a first build holds it back before it
has grown: a paused process keeps the memory it has. Memory is the footprint, which counts
compressed and swapped pages; resident size alone shrinks under pressure.

Hard limit: when the Lean processes together, running and paused, hold more than
M0C_BUILD_KILL_GB (default 1.5 times the budget), the runner kills them and Lake and exits
with status 137.

Pausing makes Lake's per-module times include the pauses. The runner therefore also writes
each module's CPU time (user + system, sampled once a second, so up to a second low) to
`.lake/membuild-times.json` for this run; `tools/build_profile.py --times` reads it.

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
TIMES = os.path.join(".lake", "membuild-times.json")


def cpu_seconds(s):
    """`ps` cputime, `[[dd-]hh:]mm:ss[.ss]`, in seconds."""
    days, _, s = s.rpartition("-")
    total = 0.0
    for part in s.split(":"):
        total = total * 60 + float(part)
    return total + (int(days) * 86400 if days else 0)


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
    """pid -> (ppid, rss bytes, command line, cpu seconds)."""
    out = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,time=,command="], capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        f = line.split(None, 4)
        if len(f) == 5:
            res[int(f[0])] = (int(f[1]), int(f[2]) * 1024, f[4], cpu_seconds(f[3]))
    return res


def lean_children(root, procs):
    """Lean compiler processes descended from `root`: pid -> (memory, module source path, cpu s)."""
    res = {}
    for pid, (ppid, rss, cmd, cpu) in procs.items():
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
            res[pid] = (footprint(pid, rss), os.path.relpath(src), cpu)
    return res


def main():
    # A timeout or kill (SIGALRM, SIGTERM) exits through the finally below, which resumes
    # paused Lean processes and stops Lake and its Lean processes instead of leaving them.
    def stop(signum, _frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGALRM, stop)
    budget = float(os.environ.get("M0C_BUILD_MEM_GB", 0)) * 2**30 or physical_bytes() / 2
    unknown = float(os.environ.get("M0C_BUILD_UNKNOWN_GB", 3)) * 2**30
    limit = float(os.environ.get("M0C_BUILD_KILL_GB", 0)) * 2**30 or 1.5 * budget
    try:
        peaks = json.load(open(PEAKS))
    except (OSError, ValueError):
        peaks = {}
    known = set(peaks)
    killed = False
    build = subprocess.Popen(["lake", "build"] + sys.argv[1:])
    stopped, order, held, times = set(), [], set(), {}
    try:
        while build.poll() is None:
            lean = lean_children(build.pid, processes())
            order = [p for p in order if p in lean] + sorted(p for p in lean if p not in order)
            stopped &= set(lean)
            used = sum(mem for mem, _, _ in lean.values())
            if used > limit:
                print(f"membuild: KILLED: the Lean processes hold {used / 2**30:.1f} GB, "
                      f"limit {limit / 2**30:.1f} GB", flush=True)
                killed = True
                build.kill()
                for pid in lean:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                break
            total = 0
            for i, pid in enumerate(order):
                mem, src, cpu = lean[pid]
                times[src] = max(times.get(src, 0), cpu)
                peaks[src] = max(peaks.get(src, 0), mem)
                need = peaks[src] if src in known else max(mem, unknown)
                total += need
                fits = i == 0 or total <= budget  # the oldest process always runs
                if not fits and pid not in stopped:
                    try:
                        os.kill(pid, signal.SIGSTOP)
                    except ProcessLookupError:   # it finished since `ps` listed it
                        continue
                    stopped.add(pid)
                    if src not in held:
                        held.add(src)
                        print(f"membuild: holding {src} (needs about {need / 2**30:.1f} GB)", flush=True)
                elif fits and pid in stopped:
                    try:
                        os.kill(pid, signal.SIGCONT)
                    except ProcessLookupError:
                        pass
                    stopped.discard(pid)
            time.sleep(1)
    finally:
        for pid in stopped:
            try:
                os.kill(pid, signal.SIGCONT)
            except ProcessLookupError:
                pass
        if build.poll() is None:
            workers = lean_children(build.pid, processes())
            build.terminate()
            build.wait()
            for pid in workers:
                try:
                    os.kill(pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
        os.makedirs(".lake", exist_ok=True)
        # Peaks only from a build that completed: a killed or failed module's sample is low
        # and would let the next build start it next to others.
        if not killed and build.returncode == 0:
            json.dump(peaks, open(PEAKS, "w"), indent=0, sort_keys=True)
        json.dump(times, open(TIMES, "w"), indent=0, sort_keys=True)
    return 137 if killed else build.returncode


if __name__ == "__main__":
    sys.exit(main())
