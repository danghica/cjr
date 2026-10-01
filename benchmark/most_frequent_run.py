#!/usr/bin/env python3
"""Run the generated most-frequent example beside two std-library baselines."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
PATTERN = re.compile(r"BENCH,([a-z_]+),(\d+),(\d+),(CJR|StdSort|StdHash),(\d+),(\d+),(-?\d+)")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cjc", default="/private/tmp/cangjie-sdk/cangjie/bin/cjc")
    ap.add_argument("--sdkroot", default="/private/tmp/cj-sdk")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--output", type=Path, default=ROOT / "benchmark/results/most_frequent")
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    sdk = Path(args.cjc).resolve().parents[1]
    env = dict(__import__("os").environ)
    env.update(CANGJIE_HOME=str(sdk), SDKROOT=args.sdkroot,
               DYLD_LIBRARY_PATH=str(sdk / "runtime/lib/darwin_aarch64_cjnative"))
    meta = {"date_utc": datetime.now(timezone.utc).isoformat(), "compiler":
            subprocess.check_output([args.cjc, "--version"], env=env, text=True).strip(),
            "optimization": "-O2", "runs": args.runs, "samples_per_process": 7,
            "machine": "Apple M4 Mac mini, 16 GB RAM, macOS 26.6.2",
            "implementations": {p: digest(ROOT / p) for p in
                ["generated/cj/most_frequent.cj", "benchmark/most_frequent_bench.cj"]}}
    rows = []
    with tempfile.TemporaryDirectory(prefix="cjr-mf-") as tmp:
        binary = str(Path(tmp) / "bench")
        cmd = [args.cjc, "generated/cj/most_frequent.cj", "benchmark/most_frequent_bench.cj",
               "--test", "-O2", "-o", binary]
        built = subprocess.run(cmd, cwd=ROOT, env=env, text=True, capture_output=True)
        (args.output / "compile.log").write_text(built.stdout + built.stderr)
        if built.returncode:
            raise SystemExit(built.stdout + built.stderr)
        for process in range(args.runs):
            run = subprocess.run([binary], cwd=ROOT, env=env, text=True, capture_output=True,
                                 timeout=900)
            (args.output / f"run{process}.log").write_text(run.stdout + run.stderr)
            if run.returncode:
                raise SystemExit(run.stdout + run.stderr)
            found = list(PATTERN.finditer(run.stdout))
            if len(found) != 231:
                raise RuntimeError(f"process {process}: expected 231 measurements, got {len(found)}")
            for m in found:
                case, n, trial, impl, elapsed, reps, result = m.groups()
                rows.append(dict(case=case, n=int(n), trial=int(trial), process=process,
                                 implementation=impl, elapsed_ns=int(elapsed), repetitions=int(reps),
                                 result=int(result), ns_per_call=int(elapsed)/int(reps)))
    with (args.output / "raw.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    grouped = {}
    for row in rows:
        grouped.setdefault((row["case"], row["n"], row["implementation"]), []).append(row["ns_per_call"])
    summary = []
    for (case, n, impl), times in sorted(grouped.items()):
        q = statistics.quantiles(times, n=4, method="inclusive")
        summary.append(dict(case=case,n=n,implementation=impl,samples=len(times),
                            median_ns=statistics.median(times),q1_ns=q[0],q3_ns=q[2]))
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    (args.output / "metadata.json").write_text(json.dumps(meta, indent=2)+"\n")
    print(f"saved {len(rows)} samples to {args.output}")

if __name__ == "__main__":
    main()
