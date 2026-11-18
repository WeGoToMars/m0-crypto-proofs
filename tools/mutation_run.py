"""Process control and verdicts shared by the mutation scripts (tools/mutate_*.py).

A mutant counts as caught by a Lean build only when Lean itself rejects it: the build fails,
every failing module is one the caller expects, and Lean reports an error at a source
position in one of them. A build that fails without such an error (a killed or crashed
worker, a memory kill, a timeout) is a tool ERROR.
"""
import os
import re
import signal
import subprocess
import sys

MEMBUILD = os.path.join(os.path.dirname(os.path.abspath(__file__)), "membuild.py")
FAILED = re.compile(r"^✖ \[\d+/\d+\] Building (\S+)", re.M)
LOCATED = re.compile(r"^error: (\S+\.lean):\d+:\d+:", re.M)
EXIT = re.compile(r"exited with code (\d+)")


class Run:
    def __init__(self, returncode, out, timed_out):
        self.returncode, self.out, self.timed_out = returncode, out, timed_out


def run_group(cmd, timeout=None, grace=60, **kw):
    """Run `cmd` in its own process group and capture its output. On timeout, SIGTERM the
    group (membuild.py then resumes paused workers and stops Lake), and SIGKILL it after
    `grace` seconds."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         start_new_session=True, **kw)
    try:
        out, _ = p.communicate(timeout=timeout)
        return Run(p.returncode, out, False)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGTERM)
        try:
            out, _ = p.communicate(timeout=grace)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            out, _ = p.communicate()
        return Run(p.returncode, out, True)


def lake_build(workspace, modules, timeout):
    """Build `modules` in `workspace` under membuild.py at nice 5."""
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    return run_group(["nice", "-n", "5", sys.executable, MEMBUILD] + modules, timeout,
                     cwd=workspace, env=env)


def module_file(module):
    return module.replace(".", "/") + ".lean"


def lean_verdict(r, expected=None):
    """(PASS | DETECTED | ERROR, detail) for a Lean build `r`. DETECTED needs failing modules,
    all in `expected` when given, and an error at a source position in one of them."""
    if r.timed_out:
        return "ERROR", "timed out"
    if r.returncode == 0:
        return "PASS", ""
    failed = sorted(set(FAILED.findall(r.out)))
    codes = {int(c) for c in EXIT.findall(r.out)} - {0, 1}
    located = {f for f in LOCATED.findall(r.out)
               if any(f.endswith(module_file(m)) for m in failed)}
    if "membuild: KILLED" in r.out or codes:
        return "ERROR", f"build killed (exit codes {sorted(codes)}): " + r.out.strip()[-200:]
    if failed and located and (expected is None or set(failed) <= set(expected)):
        return "DETECTED", " ".join(failed)
    return "ERROR", f"lake build rc {r.returncode}, failing {failed}: " + r.out.strip()[-200:]


def select(names, only):
    """The names that `only` (substrings, or None for all) selects. Every substring must match
    at least one name."""
    if only is None:
        return list(names)
    unmatched = [o for o in only if not any(o in n for n in names)]
    if unmatched:
        sys.exit(f"no mutant matches {unmatched}")
    return [n for n in names if any(o in n for o in only)]
