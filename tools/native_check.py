"""Build and run an asset's native release-check executable (`release_check` in the asset's
lakefile): the checks the asset root runs in Lean's interpreter, compiled. The mutation scripts
use it because a compiled run takes seconds where the interpreted modules take minutes."""
import os
import subprocess


def native_check(workspace, timeout=1800):
    """Returns (result, message), result in PASS / DETECTED / ERROR. A mutant is DETECTED only
    when the executable ran and reported a failing case; a build failure, a crash or a timeout
    is an ERROR."""
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
    b = subprocess.run(["lake", "build", "release_check"], cwd=workspace, env=env,
                       capture_output=True, text=True)
    if b.returncode:
        return "ERROR", "release_check does not build: " + (b.stdout + b.stderr).strip()[-300:]
    try:
        r = subprocess.run([os.path.join(workspace, ".lake", "build", "bin", "release_check")],
                           cwd=workspace, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "ERROR", "release_check timed out"
    out = (r.stdout + r.stderr).strip().splitlines()
    failed = next((l for l in out if "release check FAILED" in l), None)
    if r.returncode == 0 and failed is None:
        return "PASS", out[-1] if out else ""
    if r.returncode == 1 and failed is not None:
        return "DETECTED", failed
    return "ERROR", f"release_check rc {r.returncode}: " + " | ".join(out[-3:])
