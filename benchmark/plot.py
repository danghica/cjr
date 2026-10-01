#!/usr/bin/env python3
"""Produce publication figures and a LaTeX table from saved measurements."""
import csv
import json
from pathlib import Path
import statistics
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "benchmark/results"
FIG = ROOT / "paper/figures"
FIG.mkdir(parents=True, exist_ok=True)
summary = json.loads((DATA / "summary.json").read_text())
lookup = {(r["case"], r["implementation"], r["n"]): r for r in summary}
paired = {}
with (DATA / "raw.csv").open() as f:
    for r in csv.DictReader(f):
        k = (r["case"], int(r["n"]), int(r["process"]), int(r["trial"]))
        paired.setdefault(k, {})[r["implementation"]] = float(r["ns_per_operation"])
groups = [
    ("Linked lists", [("list_traverse", "Traverse"), ("list_build_scan", "Prepend + scan")]),
    ("Arrays", [("array_read", "Indexed read"), ("array_write_read", "Write + read passes")]),
    ("Array lists", [("arraylist_read", "Indexed read"), ("arraylist_build_scan", "Append + scan"),
                      ("arraylist_rotate", "Front removal + append")]),
    ("Hash maps", [("hashmap_build_scan", "Insert + scan"), ("hashmap_hit", "Lookup hit"),
                   ("hashmap_miss", "Lookup miss"), ("hashmap_wide_key", "Hit: keys >= 1 million"),
                   ("hashmap_collision", "Hit: colliding keys")]),
]
plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42, "ps.fonttype": 42})
fig, axs = plt.subplots(2, 2, figsize=(10.8, 8.4), constrained_layout=True)
fig.suptitle("Generated CJR / Cangjie standard library: relative elapsed time", fontsize=15)
table = []
for ax, (family, cases) in zip(axs.flat, groups):
    for i, (case, label) in enumerate(cases):
        n = max(r["n"] for r in summary if r["case"] == case)
        values = [d["CJR"] / d["Std"] for (c, s, _, _), d in paired.items() if c == case and s == n]
        med = statistics.median(values)
        q1, _, q3 = statistics.quantiles(values, n=4, method="inclusive")
        color = "#25866d" if med < 1 else "#bf642f"
        ax.barh(i, med, color=color, height=.48)
        ax.errorbar(med, i, xerr=[[med-q1], [q3-med]], fmt="none", ecolor="#263238", capsize=4)
        ax.text(max(q3, med)*1.10, i, f"{med:.2f}x", va="center", fontsize=10, bbox=dict(facecolor="white", edgecolor="none", pad=1))
        a, b = lookup[case, "CJR", n], lookup[case, "Std", n]
        table.append((family, label, n, a["median_ns"], b["median_ns"], med))
    ax.set_yticks(range(len(cases)), [f"{label}\n(n={max(r['n'] for r in summary if r['case']==case):,})" for case,label in cases])
    ax.invert_yaxis()
    ax.set_xscale("log")
    low = .2 if family == "Linked lists" else .5
    high = 4 if family in ("Linked lists", "Arrays") else 40
    ax.set_xlim(low, high)
    ax.set_ylim(len(cases)-.5, -.5)
    ticks = [v for v in [.25,.5,1,2,4,8,16,32] if low <= v <= high]
    ax.xaxis.set_major_locator(FixedLocator(ticks))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x,p: f"{x:g}x"))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.axvline(1, color="#455a64", linestyle="--", linewidth=1.4)
    ax.set_title(family, loc="left", fontsize=12, fontweight="bold")
    ax.set_xlabel("Time ratio (log scale): below 1x is faster")
    ax.grid(axis="x", alpha=.17)
    ax.set_axisbelow(True)
fig.savefig(FIG / "benchmark-overview.pdf", bbox_inches="tight")
fig.savefig(FIG / "benchmark-overview.png", dpi=180, bbox_inches="tight")
plt.close(fig)

fig, axs = plt.subplots(2, 2, figsize=(10.8, 8.5), constrained_layout=True)
fig.suptitle("Workload scaling and hash-map key sensitivity", fontsize=15)
for ax, (case, title, unit) in zip(axs.flat, [
    ("arraylist_rotate", "ArrayList: front removal + append", "ns per rotation pair"),
    ("hashmap_hit", "HashMap: hit, keys 0 to n-1", "ns per lookup"),
    ("hashmap_wide_key", "HashMap: hit, keys 1,000,000 to 1,000,000+n-1", "ns per lookup"),
    ("hashmap_collision", "HashMap: hit, keys i*(2n)", "ns per lookup")]):
    sizes = sorted({r["n"] for r in summary if r["case"] == case})
    for impl, color in [("CJR", "#bf642f"), ("Std", "#2878a2")]:
        records = [lookup[case, impl, n] for n in sizes]
        med = [r["median_ns"] for r in records]
        err = [[r["median_ns"]-r["q1_ns"] for r in records],
               [r["q3_ns"]-r["median_ns"] for r in records]]
        ax.errorbar(sizes, med, yerr=err, marker="o", capsize=4, linewidth=2, color=color,
                    label="Generated CJR" if impl=="CJR" else "Standard library")
    ax.set_xscale("log", base=2); ax.set_yscale("log")
    ax.xaxis.set_major_locator(FixedLocator(sizes))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x,p: f"{int(x):,}"))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_title(title, loc="left", fontsize=10.5, fontweight="bold")
    ax.set_xlabel("Number of entries n (log scale)")
    ax.set_ylabel(unit+" (log scale)")
    ax.grid(which="major", alpha=.2); ax.legend(fontsize=9)
fig.savefig(FIG / "benchmark-scaling.pdf", bbox_inches="tight")
fig.savefig(FIG / "benchmark-scaling.png", dpi=180, bbox_inches="tight")
plt.close(fig)

tex = ["% Generated by benchmark/plot.py from benchmark/results/raw.csv and summary.json.",
       r"\begin{tabular}{@{}lrrrr@{}}", r"\hline",
       r"Workload & $n$ & CJR (ns) & Std (ns) & Ratio \\", r"\hline"]
for family, label, n, a, b, med in table:
    name = family + ": " + label
    name = name.replace("Hit: keys >= 1 million", "Large-key hit").replace("Hit: colliding keys", "Colliding hit")
    tex.append(f"{name} & {n:,} & {a:.2f} & {b:.2f} & {med:.2f} " + r"\\")
tex += [r"\hline", r"\end{tabular}"]
(DATA / "measurements.tex").write_text("\n".join(tex)+"\n")
print("Wrote overview, scaling plots, and measurements.tex")
