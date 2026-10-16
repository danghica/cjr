# hash_map

All example-specific assets live here. Existing Rocq definitions, specifications, and proofs remain together in `rocq/`, with their original `cjr.examples.*` import names. Generated Cangjie is in `extracted/`, runtime tests in `test/`, and rendered specifications and dependency diagrams in `docs/rocq/`. Existing benchmarks and papers are under `benchmark/` and `docs/`.

Open [the offline report](index.html) or [all examples](../index.html). From this directory run `make build`, `make extract`, `make test`, `make docs`, or `make assemble`. Set `EXPLANATIONS=offline` to reuse explanation caches without model requests. `make benchmark` runs timed measurements only where a harness exists. Shared libraries and sibling examples are resolved through the repository build configuration.

The map mixes integer keys with `((k % 2147483647) * 1000000007) % 2147483647` before normalizing by capacity. `hash_product_int64` proves the multiplication fits `Int64` for every key. The model's integer multiplication remains unbounded, and this bound does not establish safety of arbitrary capacity growth.

The [benchmark report](benchmark/results/report.html) uses three processes and seven samples per process with Cangjie 1.0.5 and `-O2`. The unchanged capacity-spaced workload is named `hashmap_collision`; it collided systematically under the former direct-remainder hash. [Baseline report](benchmark/before-multiplication/report.html), [summary measurements](benchmark/before-multiplication/summary.json), [raw samples](benchmark/before-multiplication/raw.csv), and [compiler/source metadata](benchmark/before-multiplication/metadata.json) were recorded immediately before this change for comparison.

## Reading the measurements

The latest timings were recorded on October 16, 2026: 630 samples across
15 workload/size combinations, two implementations, three processes, and
seven trials. The [raw CSV](benchmark/results/raw.csv) and
[summary](benchmark/results/summary.json) retain the measurements; rebuilding
reports redraws these samples without changing their provenance.

`hashmap_build_scan` constructs an empty map, inserts sequential keys with
natural growth, and retrieves every value by key. Time is divided by the
number of keys, so one unit includes insertion and retrieval, plus its share
of allocation and rehashing. It does not measure a traversal of internal slots.
CJR costs 32.93, 37.95, and 35.04 ns/key at 256, 4096, and 16384 keys;
the standard library costs 16.33, 17.25, and 18.41 ns/key.

The new hash improves CJR capacity-spaced lookups by 38-658 times against
the immediately preceding CJR baseline. The keys are `i * (2*n)`: with the
old `key % capacity` hash and final capacity `2*n`, every key began in bucket
zero. Mixing spreads this workload; at 4096 keys, CJR falls from 3308.59 to
5.03 ns/query. The standard-library comparator in the new run takes 1021.15
ns/query. These are two different comparisons: the 658-fold improvement is
against the old CJR implementation.

Ordinary hits and build-and-scan become 10-37% slower than the CJR baseline.
Misses at 4096 and 16384 keys roughly double; the largest rises from 3.13 to
6.33 ns/query. Sequential keys already occupied distinct consecutive slots
under the old hash, and the chosen missing keys immediately reached the
empty half of the table. Mixing adds arithmetic and can add probes. Individual
hashing, probing, and memory costs have not been profiled separately.

The generic chart renderer was corrected on October 16: dot positions had
ignored measured medians. Corrected dots now encode nanoseconds per operation
on a shared time axis, and whiskers mark Q1 and Q3. Raw timings and numeric
summaries were unaffected. Lower time means faster; IQR describes sample
spread, not a confidence interval.
