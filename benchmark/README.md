# CJR / Cangjie standard-library benchmarks

Measured on 30 September 2026 with Cangjie 1.0.5 (cjnative), `-O2`,
aarch64-apple-darwin, on an Apple M4 Mac mini with 16 GB RAM and macOS 26.6.2.
The comparison uses the standard library shipped in that SDK, not version 1.1.

## Reproduce

The runner compiles each unchanged `generated/cj/{name}.cj` with `common.cj`
and its benchmark test. Each binary contains both implementations. Imports
alias standard types so the generated class names do not conflict. The
illustrative generated `main` is not the benchmark entry point: `--test`
runs the benchmark suite. Compiler and runtime paths can be supplied through
`--cjc` and `--sdkroot`. This machine needs the same macOS SDK linker-stub
workaround as the unit tests described in `test/report.md`.

```sh
python3 benchmark/run.py --cjc /path/to/cangjie/bin/cjc --sdkroot /path/to/macos-sdk
python3 benchmark/plot.py  # requires matplotlib
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/cjr-tutorial.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/cjr-tutorial.tex
```

`run.py --compile-only` checks that all comparison suites compile without
rerunning them. `--only list|array|array_list|hash_map` selects one suite;
use a separate `--output` directory for a partial run to preserve the full
saved data. Compiler logs, process logs, and temporary binaries are not
committed. `results/raw.csv` contains all 1,512 measured observations;
`summary.json` contains per-case medians and quartiles; `metadata.json`
records configuration and SHA-256 hashes of the generated and harness sources.
`plot.py` creates the figures in `paper/figures/` and the results table used
by `paper/benchmark.tex`.

## Timing and checks

Four suites run in three separate processes each. There are 36
workload/size points, two implementations per point, and seven trials per
process: 36 * 2 * 7 * 3 = 1,512 samples. Each implementation is warmed up
twice and calibrated independently toward a 20 ms batch. Steady-state
batches cap repetitions at 65,536; allocating batches cap repetitions at
262,144 / n to limit unreclaimed raw buffers. The shortest actual measured
batch was 838 microseconds. The order of CJR and standard-library measurements
alternates within each trial. Processes are run sequentially, without core
pinning. The median is over 21 samples; IQR denotes the 25th to 75th percentiles,
not a confidence interval. The relative-time plot uses the median and IQR of
21 ratios paired by process/trial. Absolute-time plots use the median and IQR
of the individual implementation times. Loop and callback costs are included;
there is no empty-loop subtraction.

`MonoTime.now()` measures elapsed time inside the test method. Compilation,
test registration, logging, setup for steady-state workloads, and checksum
assertions are outside the timed regions. Every measured batch computes a
checksum, which is consumed and checked after timing. Setup validates every
hash-map entry; front-rotation workloads also verify the final sequence and
size. All twelve suite executions passed.

## Workloads and units

- List traversal follows `head` / `tail` on the CJR nodes and
  `firstNode` / `next` on the standard `LinkedList<Int64>`. Both sum the same
  contents. Build-and-scan prepends 0..n-1 to an empty list and traverses it.
  Units are ns per visited node or per inserted-and-visited item. Sizes:
  256, 4,096, 16,384. CJR is singly linked; the standard type is doubly linked
  and tracks collection membership. They implement different contracts.
- Arrays read all initialized cells in permuted order `(i*17) % n`, which
  visits every cell because n is a power of two. Write-and-read performs
  n stores followed by n reads; the unit is ns per elementary access,
  dividing by 2n. Sizes: 256, 4,096, 65,536. Constructors are excluded, and
  the harness writes every CJR cell before its first read. The baseline is
  `std.core.Array<Int64>` indexed with `[]`; CJR uses unchecked pointer access.
- ArrayList read uses the same permutation. Build-and-scan appends 0..n-1
  from the default constructor, including natural capacity growth, then
  reads every value. Sizes: 256, 4,096, 16,384. Front rotation performs n
  remove-at-zero / append pairs on a fixed-size list, returning to the
  original contents; units are ns per pair. Sizes: 256, 1,024, 4,096.
- HashMap build-and-scan inserts distinct sequential keys with value 3*i+1
  from default construction, including growth, and then reads them. Hits
  query 0..n-1 and misses query n..2n-1. Large-key hits use
  1,000,000..1,000,000+n-1. Sizes: 256, 4,096, 16,384. Colliding hits use
  keys i*(2n), at sizes 256, 1,024, 4,096: these all start in bucket zero
  at the generated map's final capacity 2n. The baseline receives exactly
  the same keys; its bucket policy is not forced to match. Units are ns per
  lookup or per inserted-and-looked-up item. Presence checks are included
  for hits (`Int64Option.ok` versus standard `Option.getOrThrow()`).

## Scope

These are warm-cache, single-threaded microbenchmarks of actual generated
programs, not a proof of performance parity. Default growth policies and
public operation costs are included. No generated code was modified,
no raw buffers were freed by the harness, and no GC was forced. CJR growing
arrays/maps abandon old malloc buffers; standard arrays are managed. This
memory-management difference makes sustained allocating workloads a different
question from these bounded batches.

HashMap construction still relies on the allocator returning zero-valued tags.
All data checks passed on this runtime, but the benchmark does not fix or
prove that assumption. The zero-initialization gap documented in the tutorial
appendix remains. Valid indexes and representable Int64 values are used.
The data do not support claims about out-of-range behavior, large-machine
integer limits, arbitrary keys, asymptotic complexity bounds, or memory usage.

## Most-frequent integer

`most_frequent_run.py` compiles the **printer-emitted**
`generated/cj/most_frequent.cj` with `most_frequent_bench.cj`. It compares
complete, input-preserving operations with identical empty and earliest
first-occurrence tie semantics. The two baselines are adapters authored
for this experiment using SDK `std.sort.sort` and `std.collection.HashMap`,
not built-in most-frequent functions. The map baseline counts and records
the maximum in one pass, then searches the input in original order.

```sh
python3 benchmark/most_frequent_run.py --cjc /path/to/cangjie/bin/cjc --sdkroot /path/to/macos-sdk
MPLBACKEND=Agg python3 benchmark/most_frequent_plot.py
```

Three processes, seven samples per process, three implementations, and
11 distribution/size points produce 693 measurements in
`results/most_frequent/raw.csv`. Each batch uses `262144/n` repetitions
for every implementation. Trial order rotates; each operation receives two
warmup calls. Setup, printing, and checksum validation are outside timing.
Allocation, copying, sorting/counting, scanning, option construction, and
CJR temporary-buffer frees are inside. Native managed-object garbage
collection is not forced or standardized between samples. The generated
implementation frees both raw buffers; its input is constructed once.

Dense signed, permuted distinct, and seven-value-domain cases use sizes
256, 4096, and 16384. Sorted and reverse-sorted distinct cases use only
256 to bound the reused Lomuto algorithm's quadratic worst case. These
are deterministic distributions, not randomized pivot experiments.
`summary.json` contains medians and quartiles; `metadata.json` records
compiler/machine settings and hashes of both measured sources.
`most_frequent_plot.py` generates two report figures and a LaTeX timing
table. Ratios are medians of matched process/trial ratios; they can differ
slightly from ratios of independently computed medians.

The complete CJR operation has a checked Iris refinement theorem `mf_wp`
and specification corollary `mf_spec_wp`. These cover both branches,
copying, paired quicksort, grouping, tie-breaking, raw-buffer cleanup,
and input preservation. Benchmarks measure emitted native performance;
they do not establish the correctness of the printer or native compiler.
