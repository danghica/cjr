#!/usr/bin/env python3
"""Plot repeated end-to-end most-frequent measurements."""
import csv, json, statistics
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "benchmark/results/most_frequent"
OUT = ROOT / "paper/figures"
rows = list(csv.DictReader((DATA / "raw.csv").open()))
groups = defaultdict(dict)
for r in rows:
    groups[(r["case"], int(r["n"]), int(r["process"]), int(r["trial"]))][r["implementation"]] = int(r["elapsed_ns"]) / int(r["repetitions"])
summary = defaultdict(list)
for r in rows:
    summary[(r["case"], int(r["n"]), r["implementation"])].append(int(r["elapsed_ns"]) / int(r["repetitions"]))

case_titles = {"dense":"Dense signed values", "wide":"Permuted distinct values",
               "small_domain":"Seven-value domain", "sorted":"Sorted input",
               "reverse_sorted":"Reverse-sorted input"}
colors = {"CJR":"#c65b23", "StdSort":"#287aa1", "StdHash":"#26856a"}
fig1, ax1 = plt.subplots(figsize=(7, 4.8))
fig2, ax2 = plt.subplots(figsize=(7, 6.8))
cases = ["dense", "wide", "small_domain"]
sizes = [256, 4096, 16384]
offset = {"CJR":-0.22, "StdSort":0, "StdHash":0.22}
for impl in colors:
    for case, marker in zip(cases, ["o", "s", "^"]):
        xs=[]; med=[]; lo=[]; hi=[]
        for n in sizes:
            vals=summary[(case,n,impl)]
            xs.append(n); med.append(statistics.median(vals))
            lo.append(statistics.median(vals)-np.quantile(vals,.25))
            hi.append(np.quantile(vals,.75)-statistics.median(vals))
        ax1.errorbar(xs, med, yerr=[lo,hi], marker=marker, linewidth=1.5,
                     capsize=2, color=colors[impl], alpha=.85,
                     label=f"{impl}, {case_titles[case].lower()}")
ax1.set_xscale("log",base=2); ax1.set_yscale("log")
ax1.set_xlabel("Input length (n)"); ax1.set_ylabel("Median nanoseconds per full call")
ax1.set_title("Scaling on three distributions")
ax1.grid(True,which="both",alpha=.2)
ax1.legend(fontsize=8,ncol=2,loc="upper left")

keys=sorted({(case,n) for case,n,_ in summary})
labels=[]; vals={k:[] for k in ["StdSort","StdHash"]}
for case,n in keys:
    ratios={k:[] for k in vals}
    for (c,nn,p,t),v in groups.items():
        if c==case and nn==n and "CJR" in v:
            for baseline in ratios:
                ratios[baseline].append(v["CJR"]/v[baseline])
    if not ratios["StdSort"]: continue
    labels.append(f"{case_titles[case]}\n n={n:,}")
    for baseline in vals: vals[baseline].append(statistics.median(ratios[baseline]))
y=np.arange(len(labels)); height=.34
for k,dy in [("StdSort",-.18),("StdHash",.18)]:
    ax2.barh(y+dy, vals[k], height=height, label=f"CJR / {k}", color=colors[k], alpha=.9)
    for yy,v in zip(y+dy,vals[k]): ax2.text(v*1.06,yy,(f"{v:.0f}x" if v >= 10 else f"{v:.2g}x"),va="center",fontsize=9)
ax2.axvline(1,color="#333333",linestyle="--",linewidth=1)
ax2.set_xscale("log"); ax2.set_yticks(y,labels,fontsize=9); ax2.invert_yaxis()
ax2.set_xlabel("Median paired time ratio (lower is faster)")
ax2.set_title("CJR time relative to standard-library baselines")
ax2.grid(True,axis="x",which="both",alpha=.2); ax2.legend(fontsize=8)
OUT.mkdir(parents=True,exist_ok=True)
for fig, name in [(fig1,"most-frequent-scaling"),(fig2,"most-frequent-ratios")]:
    fig.tight_layout()
    fig.savefig(OUT/f"{name}.png",dpi=180,bbox_inches="tight")
    fig.savefig(OUT/f"{name}.pdf",bbox_inches="tight")

lines = [r"\begin{table}[H]", r"\centering\small",
         r"\begin{tabular}{lrrrr}", r"\hline",
         r"Distribution & $n$ & CJR ($\mu$s) & std.sort ($\mu$s) & HashMap ($\mu$s) \\",
         r"\hline"]
for case,n in keys:
    times = [statistics.median(summary[(case,n,impl)])/1000 for impl in ["CJR","StdSort","StdHash"]]
    lines.append(case_titles[case] + " & " + f"{n:,}" + " & " + " & ".join(f"{v:,.2f}" for v in times) + r" \\")
lines += [r"\hline",r"\end{tabular}",
          r"\caption{Median time per complete operation; 21 samples per entry.}",r"\end{table}"]
(ROOT/"paper/most-frequent-results.tex").write_text("\n".join(lines)+"\n")
print(OUT/"most-frequent-scaling.pdf")
print(OUT/"most-frequent-ratios.pdf")
