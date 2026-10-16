# Historical combined collection benchmark record

Measurements below retain their original run provenance. Active harnesses, configurations, and reports now belong to each directory under `example/`. Use `make benchmark` at the repository root or `make benchmark` inside an individual example; no timings were rerun during the move.

# CJR / Cangjie standard-library benchmarks

This directory preserves the original mixed-suite measurements and source
metadata from October 12, 2026. The older narrative below describes the October 9
manuscript snapshot and remains historical context. The current PDF tutorial
now uses the saved October 12 observations for lists, arrays, and array lists,
and the separate October 16 hashmap run with bounded multiplicative hashing.
The historical raw samples and metadata in this directory are unchanged.

The [current hashmap report](../../example/hash_map/benchmark/results/report.html)
and its [immediate baseline](../../example/hash_map/benchmark/before-multiplication/report.html)
record the hash comparison. The [PDF tutorial](../cjr-tutorial.pdf) explains the
workloads, units, and tradeoffs. Rebuild its figures and table with
`python3 paper/update_benchmarks.py` (ReportLab required), then `make cj`.
This redraws saved measurements; `make benchmark` collects new timings.

## Reproduce

The project-wide runner reads the per-suite JSON configuration next to each
harness. It compiles each unchanged generated program and stores normalized
observations, summaries, metadata, SVG charts, and an offline HTML report.
`CJC` and `SDKROOT` select the compiler and SDK; the runner applies the shared
macOS linker-stub compatibility copy when needed.

```sh
make benchmark
```

This runs both CJR container suites and the most-frequent suite. To run one
suite directly, pass its configuration to the common runner:

```sh
python3 -m tools.project_tools.examples benchmark
python3 -m tools.project_tools.examples report
python3 -m tools.project_tools.examples report
```

The same runner is used by the independent quadtree example. Harness code,
workload definitions, and suite configuration remain with each example.

## Historical October 9 manuscript narrative

The timing discussion below is retained as historical context; it does not
describe the refreshed manuscript figures or the October 16 hashmap run.

Each generated container is compiled unchanged with its shared measurement
helpers and comparison harness. `--test` runs the benchmark suite rather than
the generated illustrative `main`. The compiler and SDK are selected with the
`CJC` and `SDKROOT` environment variables. On this machine, the common runner
applies the macOS SDK linker-stub workaround used by the unit tests.

The shared runner writes compiler and process logs, normalized CSV rows,
per-workload medians and quartiles, compiler/machine metadata, charts, and an
offline report under each suite's configured output directory.

## Timing and checks

Four suites run in three separate processes each. There are 36
workload/size points, two implementations per point, and seven trials per
process: 36 * 2 * 7 * 3 = 1,512 samples. Each implementation is warmed up
twice and calibrated independently toward a 20 ms batch. Steady-state
batches cap repetitions at 65,536; allocating batches cap repetitions at
262,144 / n to limit unreclaimed raw buffers. The shortest actual measured
batch was 857 microseconds. The order of CJR and standard-library measurements
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
- ArrayList access now uses unchecked pointer operations under valid-index
  preconditions. Read uses the same permutation. Build-and-scan appends 0..n-1
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
  lookup or per inserted-and-looked-up item. CJR computes the initial bucket
  with one signed `%` operation and at most one addition; it still uses
  linear probing without hash mixing. Presence checks are included
  for hits (`Int64Option.ok` versus standard `Option.getOrThrow()`).

## Results after native bulk copying

Front removal plus append now uses native `memmove` for the overlapping
suffix shift. The exact CJR method bodies and their proofs are unchanged;
the printer enables this lowering only for verified ArrayList growth and
removal, with a positive-length guard. Clearing the old tail word and all
size/version updates remain explicit. Front removal remains O(n).

At n=4,096, CJR rotation fell from the preceding saved median of
4996 ns to
309 ns per removal/append pair, about
16.2 times
faster. Stdlib takes 317 ns; the median paired
CJR/stdlib ratio is 0.97, down from 15.76.
At n=256 and 1,024 the new CJR medians are
22.70 and 80.09 ns, with
paired ratios 1.11 and
1.05 respectively.

Bulk copying also improves growth: at n=16,384, append-and-scan fell from
4.82 to
3.60 ns per item (about
1.34 times
faster), with paired CJR/stdlib ratio 0.93.
Indexed access is essentially unchanged. These before/after results span
separate desktop runs; they are not a same-run isolation of every effect.

The full collection refresh contains 1,512 checked measurements. Native
allocation now supplies zero-filled cells, and `get` / `contains` use a
separately verified bounded loop returning an option directly. Insertion
and removal retain the slot-aware, tombstone-aware probe.

Collision-heavy lookup at n=4,096 fell from the previous saved CJR median
of 19.41 microseconds to 3.90 microseconds,
about 5.0 times faster. Stdlib takes
1.01 microseconds; the median paired
CJR/stdlib ratio is 3.85, down from 18.80.
All these CJR keys still start in bucket zero, so the loop still walks a
long linear-probe chain. Hash mixing has not been added.

At n=16,384, ordinary hits take 4.46 ns versus
2.47 ns (paired ratio 1.85),
and misses take 3.27 ns versus
1.67 ns (ratio 1.96).
Large-key lookup at n=256 takes 4.44 ns versus
2.48 ns (ratio 1.79).
The earlier primitive remainder repair continues to avoid normalization
work proportional to key magnitude.

The n=256 CJR miss point is now 3.48 ns, with quartiles
3.36–3.52 ns,
versus 1.70 ns for stdlib. The previous saved
point had median 1,313 ns and quartiles 3.72–1,328 ns. That broad distribution
is absent in this run. Allocation initialization and lookup changed together;
these separate desktop runs do not isolate their individual timing effects.

## Scope

These are warm-cache, single-threaded microbenchmarks of actual generated
programs, not a proof of performance parity. Default growth policies and
public operation costs are included. No generated code was modified,
no raw buffers were freed by the harness, and no GC was forced. CJR growing
arrays/maps abandon old raw buffers; standard arrays are managed. This
memory-management difference makes sustained allocating workloads a different
question from these bounded batches.

Primitive allocation now emits `calloc`, so successful native allocations
supply the zero-valued cells required by the CJR proofs. Native regression
tests cover fresh arrays and map buffers after dirtying and freeing buffers.
Allocation failure, printer correctness, and compiler correctness remain
outside the formal results. Valid indexes and representable Int64 values are used.
The data do not support claims about out-of-range behavior, large-machine
integer limits, arbitrary keys, asymptotic complexity bounds, or memory usage.

## Most-frequent integer

The shared runner compiles the **printer-emitted**
`example/most_frequent/extracted/most_frequent.cj` with `most_frequent_bench.cj`. It compares
complete, input-preserving operations with identical empty and earliest
first-occurrence tie semantics. The two baselines are adapters authored
for this experiment using SDK `std.sort.sort` and `std.collection.HashMap`,
not built-in most-frequent functions. The map baseline counts and records
the maximum in one pass, then searches the input in original order.

```sh
python3 tools/project_tools/benchmark.py run example/most_frequent/benchmark/benchmark.config.json
python3 tools/project_tools/benchmark.py plot example/most_frequent/benchmark/benchmark.config.json
python3 tools/project_tools/benchmark.py report example/most_frequent/benchmark/benchmark.config.json
```

Refreshed on 9 October 2026 alongside the collection suites.
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
The shared report contains normalized timings and compiler metadata. Ratios
in the historical manuscript figures are medians of matched process/trial ratios; they can differ
slightly from ratios of independently computed medians.

The complete CJR operation has a checked Iris refinement theorem `mf_wp`
and specification corollary `mf_spec_wp`. These cover both branches,
copying, paired quicksort, grouping, tie-breaking, raw-buffer cleanup,
and input preservation. Benchmarks measure emitted native performance;
they do not establish the correctness of the printer or native compiler.
