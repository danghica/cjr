#!/usr/bin/env python3
"""Compile unchanged generated programs alongside optimized comparison tests."""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import tempfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("list", "array", "array_list", "hash_map")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cjc", default="/private/tmp/cangjie-sdk/cangjie/bin/cjc")
    ap.add_argument("--sdkroot", default="/private/tmp/cj-sdk")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--only", choices=NAMES)
    ap.add_argument("--compile-only", action="store_true")
    ap.add_argument("--output", type=Path, default=ROOT / "benchmark/results")
    args = ap.parse_args()
    names = [args.only] if args.only else NAMES
    env = os.environ.copy()
    home = Path(args.cjc).resolve().parents[1]
    env["CANGJIE_HOME"] = str(home)
    env["SDKROOT"] = args.sdkroot
    env["DYLD_LIBRARY_PATH"] = str(home / "runtime/lib/darwin_aarch64_cjnative")
    args.output.mkdir(parents=True, exist_ok=True)
    metadata = {
        "date_utc": datetime.now(timezone.utc).isoformat(),
        "os": platform.platform(), "architecture": platform.machine(),
        "compiler": subprocess.check_output([args.cjc, "--version"], env=env, text=True).strip(),
        "optimization": "-O2", "runs": args.runs, "samples_per_process": 7,
        "clock": "std.time.MonoTime.now()", "calibration_target_ns": 20_000_000,
        "allocation_batch_repetition_limit": "262144 / n",
        "machine": "Mac mini, Apple M4, 10 cores (4 performance + 6 efficiency), 16 GB RAM",
        "steady_batch_repetition_limit": 65536,
        "sdkroot": args.sdkroot,
        "generated_source_sha256": {name: digest(ROOT / f"generated/cj/{name}.cj") for name in names},
        "harness_source_sha256": {name: digest(ROOT / f"benchmark/{name}_bench.cj") for name in names},
        "common_sha256": digest(ROOT / "benchmark/common.cj"),
    }
    rows = []
    with tempfile.TemporaryDirectory(prefix="cjr-benchmark-") as scratch:
        for name in names:
            binary = str(Path(scratch) / name)
            cmd = [args.cjc, f"generated/cj/{name}.cj", "benchmark/common.cj",
                   f"benchmark/{name}_bench.cj", "--test", "-O2", "-o", binary]
            compile_result = subprocess.run(cmd, cwd=ROOT, env=env, text=True, capture_output=True)
            (args.output / f"{name}.compile.log").write_text(compile_result.stdout + compile_result.stderr)
            if compile_result.returncode:
                print(compile_result.stdout + compile_result.stderr, flush=True)
                raise SystemExit(compile_result.returncode)
            print(f"Compiled {name} with -O2", flush=True)
            if args.compile_only:
                continue
            for run in range(args.runs):
                result = subprocess.run([binary], cwd=ROOT, env=env, text=True, capture_output=True,
                                        timeout=600)
                (args.output / f"{name}.run{run}.log").write_text(result.stdout + result.stderr)
                if result.returncode:
                    print(result.stdout + result.stderr, flush=True)
                    raise SystemExit(result.returncode)
                count = 0
                pattern = r"BENCH,([a-z_]+),(CJR|Std),(\d+),(\d+),(\d+),(\d+),(-?\d+)"
                for match in re.finditer(pattern, result.stdout):
                    case, impl, n, trial, ns, ops, checksum = match.groups()
                    rows.append(dict(case=case, implementation=impl, n=int(n), process=run,
                                     trial=int(trial), elapsed_ns=int(ns), operations=int(ops),
                                     checksum=int(checksum), ns_per_operation=int(ns) / int(ops)))
                    count += 1
                wanted = {"list": 84, "array": 84, "array_list": 126, "hash_map": 210}[name]
                if count != wanted:
                    raise RuntimeError(f"{name}: expected {wanted} rows, got {count}")
                if not count:
                    raise RuntimeError(f"{name}: no benchmark rows produced")
                print(f"{name}: process {run + 1}/{args.runs}, {count} checked measurements", flush=True)
    if args.compile_only:
        return
    with (args.output / "raw.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    groups = {}
    for r in rows:
        groups.setdefault((r["case"], r["implementation"], r["n"]), []).append(r["ns_per_operation"])
    summary = []
    for (case, impl, n), values in sorted(groups.items()):
        qs = statistics.quantiles(values, n=4, method="inclusive")
        summary.append(dict(case=case, implementation=impl, n=n, samples=len(values),
                            median_ns=statistics.median(values), q1_ns=qs[0], q3_ns=qs[2],
                            min_ns=min(values), max_ns=max(values)))
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    for name, old in metadata["generated_source_sha256"].items():
        assert digest(ROOT / f"generated/cj/{name}.cj") == old, "generated source was modified"
    print(f"Saved {len(rows)} measurements to {args.output}", flush=True)

if __name__ == "__main__":
    main()
