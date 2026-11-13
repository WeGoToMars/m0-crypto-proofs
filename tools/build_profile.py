#!/usr/bin/env python3
"""Summarize a clean Lake build using the import graph of this checkout.

Run in the same source snapshot that produced LOG:
  /usr/bin/time -p lake --no-ansi build > build.log 2>&1
  python3 -I /path/to/tools/build_profile.py build.log --json profile.json
A partial/incremental log is rejected rather than reporting a false critical path.

Under tools/membuild.py, Lake's module times include the time a module was paused; pass
`--times .lake/membuild-times.json` to weight modules by their CPU time instead (Lake's time
is kept for modules too short to be sampled).
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--json", type=Path, dest="json_path")
    parser.add_argument("--root", default="M0Crypto")
    parser.add_argument("--times", type=Path, dest="times_path",
                        help="membuild-times.json: per-module CPU seconds replace Lake's times")
    args = parser.parse_args()
    log = re.sub(r"\x1b\[[0-9;]*m", "", args.log.read_text())
    if "Build completed successfully" not in log or "error: build failed" in log:
        parser.error("log must contain a successful build")
    times = {}
    for name, duration in re.findall(r"\bBuilt (M0Crypto[\w.]*) \(([^)]+)\)", log):
        parts = re.findall(r"([\d.]+)(ms|s|m|h)", duration)
        if not parts:
            parser.error(f"unrecognized module duration: {duration}")
        times[name] = sum(float(n) * {"ms": .001, "s": 1, "m": 60, "h": 3600}[u]
                          for n, u in parts)
    sources = {".".join(p.relative_to("lean").with_suffix("").parts): p
               for p in Path("lean").rglob("*.lean")}
    if args.times_path:
        cpu = json.loads(args.times_path.read_text())
        # modules that finished between two samples have no CPU time; keep Lake's for them
        times.update({".".join(Path(src).relative_to("lean").with_suffix("").parts): s
                      for src, s in cpu.items()})
    imports = {name: re.findall(r"^import\s+(M0Crypto[\w.]*)", p.read_text(), re.M)
               for name, p in sources.items()}
    reachable = set()

    def visit(name):
        if name in reachable:
            return
        if name not in sources:
            parser.error(f"missing source for {name}; use the log's source snapshot")
        reachable.add(name)
        for dep in imports[name]:
            visit(dep)

    visit(args.root)
    if missing := sorted(reachable - times.keys()):
        parser.error("modules missing from clean log: " + ", ".join(missing))

    @lru_cache(None)
    def longest(name):
        weight, chain = max((longest(dep) for dep in imports[name]),
                            default=(0, []), key=lambda item: item[0])
        return weight + times[name], chain + [name]

    critical, chain = longest(args.root)
    timer = {key: float(value) for key, value in
             re.findall(r"^(real|user|sys)\s+([\d.]+)$", log, re.M)}
    data = {
        "wall_seconds": timer.get("real"),
        "user_seconds": timer.get("user"),
        "sys_seconds": timer.get("sys"),
        "module_count": len(reachable),
        "sum_module_seconds": sum(times[name] for name in reachable),
        "critical_seconds": critical,
        "critical_path": [{"module": name, "seconds": times[name]} for name in chain],
        "times": {name: times[name] for name in sorted(reachable)},
        "imports": {name: imports[name] for name in sorted(reachable)},
        "source_sha256": {name: hashlib.sha256(sources[name].read_bytes()).hexdigest()
                          for name in sorted(reachable)},
    }
    if args.json_path:
        args.json_path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"Modules: {data['module_count']}")
    print(f"Wall: {data['wall_seconds']} s; summed module wall time: {data['sum_module_seconds']:.2f} s")
    print(f"Weighted import critical path: {critical:.2f} s ({len(chain)} modules)")
    print(" → ".join(chain))
    print("Module times are rounded and depend on concurrent work; this is a scheduling estimate.")
    print("Slowest modules:")
    for name in sorted(reachable, key=lambda n: -times[n])[:15]:
        print(f"  {times[name]:8.1f} s  {name}")


if __name__ == "__main__":
    main()
