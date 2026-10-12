# Unit test report

Date: 3 October 2026.

Compiler: Cangjie 1.0.5 (cjnative), target aarch64-apple-darwin.

Each extracted file was compiled on its own with its test file, because every file declares `malloc`, `free`, and `main`, and both `array.cj` and `array_list.cj` declare `class Array`. The quicksort files declare that class as well, and `qsort_array_list.cj` also declares `class ArrayList`. The command was:

```sh
cjc generated/cj/<name>.cj test/<name>_test.cj --test -o test/bin/<name>_test
```

The tests use `@Test`, `@TestCase`, and `@Expect` from the Cangjie `std.unittest` framework. The test files are ordinary Cangjie. The files under test are the extracted CJR programs in `generated/cj/`, unchanged.

The bundled linker in this SDK does not read the macOS 27 `libSystem.tbd`. The binaries were linked with `SDKROOT` pointed at a copy of the macOS 26 SDK whose stub files also list `arm64-macos`. That change is outside the repository.

Array-list indexes outside `[0, size)` now compile to `throw Exception("CJR panic")`. Three new cases verify invalid `get`, `set`, and `remove` operations raise an exception. The CJR semantics leaves `Panic` stuck; the proofs show it is unreachable under the methods’ valid-index preconditions. `cell` discards the value it loads, so its test only checks that the call returns.

## Results

54 cases ran across the 15 base generated programs. 54 passed. 0 failed.

All fifteen generated programs were rebuilt and rerun, including the 13 hash map cases, six list reversal cases, and three explicit panic cases.

| Program | Cases | Result |
|---|---:|---|
| `arith.cj` | 1 | passed |
| `struct_upd.cj` | 2 | passed |
| `cell.cj` | 1 | passed |
| `swap.cj` | 1 | passed |
| `sum_block.cj` | 1 | passed |
| `class_upd.cj` | 1 | passed |
| `frame_call.cj` | 1 | passed |
| `vtable.cj` | 1 | passed |
| `list.cj` | 3 | passed |
| `list_rev.cj` | 6 | passed |
| `array.cj` | 3 | passed |
| `array_list.cj` | 9 | passed |
| `hash_map.cj` | 13 | passed |
| `qsort_array.cj` | 5 | passed |
| `qsort_array_list.cj` | 6 | passed |

## What passed

`sumOne` returned 1.

`bump` returned 1. `bumpKeep` returned 0.

`cell` returned.

`swap` of cells holding 1 and 2 left 2 and 1.

`sumAt` of a word holding 4 returned 4.

`classBump` returned 0.

`frameCall` returned 3, the written pointer held 9, and the other pointer still held 3.

`run` returned 1.

`nil` is empty and its head is 0. `cons(1, nil)` is not empty, its head is 1, and its tail is empty with head 0. `tail` of `cons(7, cons(1, nil))` has head 1, and the tail of that tail is empty.

`make(4)` had length 4. A fresh array read back 0 at indexes 0 and 3. After writes, index 0 read back 7, index 2 read back 9, and the length stayed 4.

A fresh array list had size 0, capacity 16, version 0, and `isEmpty` true. Two appends left size 2, values 1 and 2, and version 2. `set` at index 0 stored 9, left the other element and the size and the capacity unchanged, and left the version at 2. Removing the last element returned that element, restored the preceding value, left the capacity at 16, and set the version to 3. Removing index 0 of `[1, 2, 3]` returned 1 and left `[2, 3]`. Sixteen appends left the capacity at 16. The seventeenth append left the capacity at 32, kept the earlier elements, stored 99 at index 16, and set the version to 17.

`sort` on an array left a one-element array holding 7, left `[1, 2, 3, 4]` in order, turned `[4, 3, 2, 1]` into `[1, 2, 3, 4]`, turned `[2, 2, 1, 2]` into `[1, 2, 2, 2]`, and turned `[3, 1, 4, 1, 5]` into `[1, 1, 3, 4, 5]`. Every index was checked.

`sort` on an empty array list left size 0, capacity 16, and version 0. The same five inputs, written with `add` and then sorted, produced the same sequences. After each sort the size, the capacity, and the version were the values `add` had left.


## List reversal verification — 30 September 2026

The unchanged generated `example/list_rev/extracted/list_rev.cj` was compiled together with `example/list_rev/test/list_rev_test.cj` using Cangjie 1.0.5 (cjnative), aarch64-apple-darwin. The six cases ran and all passed: 0 failures, 0 errors, 0 skipped. This run is separate from the historical 32-case run above.

```sh
CANGJIE_HOME=/private/tmp/cangjie-sdk/cangjie \
SDKROOT=/private/tmp/cj-sdk \
DYLD_LIBRARY_PATH=/private/tmp/cangjie-sdk/cangjie/runtime/lib/darwin_aarch64_cjnative \
/private/tmp/cangjie-sdk/cangjie/bin/cjc \
  example/list_rev/extracted/list_rev.cj example/list_rev/test/list_rev_test.cj --test -o test/bin/list_rev_test
DYLD_LIBRARY_PATH=/private/tmp/cangjie-sdk/cangjie/runtime/lib/darwin_aarch64_cjnative \
  test/bin/list_rev_test
```

- `emptyList`: the result is empty, has sentinel value 0, and its tail is empty; the original sentinel remains empty.
- `singleton`: `[7]` stays `[7]` and the original cons node ends in an empty sentinel.
- `severalNodes`: `[1, 2, 3, 4]` becomes `[4, 3, 2, 1]`, checking every element and the end.
- `duplicatesAndNegativeValues`: `[-2, 0, -2, 9]` becomes `[9, -2, 0, -2]`, checking every element and the end.
- `doubleReversal`: two calls restore `[5, -1, 5]`.
- `rewiresOriginalNodesAndFramesOtherList`: references saved before reversing `[1, 2, 3]` observe the changed links `3 -> 2 -> 1 -> empty`; the original sentinel and a disjoint `[42]` list remain empty and unchanged, respectively. This detects copying that leaves the original links intact.

The Coq module compiles. `make check-axioms` reports 29/29 audited theorems closed under the global context, including `reverse_spec` and `reverse_twice_spec`. The reversal theorem chain contains no `Admitted`, `admit`, or added `Axiom`. `make cj` produces the standalone reversal file and rebuilds the tutorial PDF.

The specification is a partial-correctness and safety theorem for the CJR term. The runtime cases check the printed Cangjie, rather than a separately handwritten reversal. They do not constitute a formal proof of the printer or compiler.

The three existing `list.cj` cases were also compiled and rerun on the same compiler; all passed. The list regression total for this run is 9/9 (six reversal cases plus three existing list cases). `coqchk` succeeds for the reversal module and `make check-proofs` completes for the project. The project-wide `make check-no-cheats` gate now passes: the hash map obligations have been completed, and the source contains no admitted proofs or declared axioms.

## Hash map verification — 30 September 2026

The regenerated `hash_map.cj` is compiled directly with `example/hash_map/test/hash_map_test.cj`. All 13 cases pass. Eight regression cases extend the five original cases:

- `collisionsAndWraparound` checks three colliding keys starting at the last slot and an absent colliding key.
- `tombstoneDoesNotHideExistingKey` removes the first key, updates a later colliding key without duplicating it, and inserts another key into a reusable slot.
- `negativeKeysAndZeroValues` distinguishes a stored zero from absence and checks negative colliding keys.
- `updateAtLoadLimitDoesNotGrow` keeps capacity 16 and size eight while updating an existing entry.
- `growthPreservesEveryEntry` inserts nine colliding keys, checks capacity 32, and reads every value afterward.
- `repeatedGrowthAndRemoval` inserts 80 keys through several doublings, checks every entry, removes 40, checks a missing removal, and reinserts the deleted keys with new values.
- `explicitGrowthPreservesContents` doubles a populated map and checks its size and colliding entries.
- `tombstonesAcrossEntireProbeCycle` turns all 16 slots into tombstones, checks a bounded absent lookup, and successfully reuses a slot.

The Coq module contains no admissions. `make verify` checks all 23 compiled modules with `coqchk`, rejects source bypasses, and audits 29 theorems as closed under the global context. The audit covers all public hash map methods, the remainder, scan, insertion, and rehash kernels, and the initialization and insertion client compositions. `make cj` regenerates the implementation and rebuilds the detailed tutorial, including complete checked proof listings.

The printer changes also warranted rebuilding and rerunning every extracted-program test: all 54 cases across 15 programs pass. Compiler logs and binaries were kept outside the repository. The macOS SDK workaround described above was still required. The compiler reports benign unused-variable warnings for the retained growth hint and illustrative main result.

The formal results concern the CJR expressions, whose integers are unbounded. Runtime tests validate the printed `Int64` programs on the tested inputs; the printer, compiler, and freedom from arbitrary machine-integer overflow are not formally verified. `grow(minCap)` performs one doubling, rather than guaranteeing an arbitrary requested minimum.

## Standard-library performance comparison — 3 October 2026

The optimized benchmark suites compile the generated `list.cj`, `array.cj`, `array_list.cj`, and `hash_map.cj`
directly beside comparisons with
their standard-library counterparts. All twelve suite executions passed
(three processes for each of four suites). Each measured batch's checksum
passed: 1,512 observations, covering 36 workload/size points and 21 observations
per implementation at each point. The complete 54-case functional suite was rerun separately.

The Apple M4 / Cangjie 1.0.5 `-O2` results are mixed. At the largest tested
sizes, list prepend-and-scan takes 0.29x standard time, array indexed read
1.22x, array-list append-and-scan 0.84x, front rotation 15.77x, and ordinary
hash-map hit 2.45x. Large-key lookup in a 256-entry map is roughly 286x
slower. The tutorial includes two charts, absolute timings, and limitations;
`example/benchmark-history/README.md` documents the inputs and timing protocol. Full raw
data and source/configuration hashes are retained under `benchmark/results/`.
Only the generated array-list invalid-index branch changed for this rerun; benchmark
inputs use valid indexes. Raw-memory initialization and reclamation gaps remain, and
the comparison does not prove performance parity.

## Most-frequent integer (3 October 2026)

The source is now genuinely emitted by `p_most_frequent` in `emit_cj.v`
from the concrete terms in `most_frequent.v`. The Cangjie 1.0.5 `-O2`
build passes all **11** methods in `most_frequent_test.cj`: nine required
edge-case methods, exhaustive small arrays, and paired-record sorting.
The exhaustive method checks all 3,280 arrays of lengths 0–7 over
`{-1,0,1}` against an independent quadratic oracle. Every result test
checks input preservation. The pair-sort test checks increasing
lexicographic order, unique original indices, and value provenance.
Boundary values include both `Int64` extremes.

Empty inputs are represented by a zero-length view over a positive
allocation; they do not depend on `malloc(0)`. The emitted operation
allocates nothing on empty input and frees both raw temporary buffers
before returning on nonempty input. Its group guard is an explicit `If`
so the eager CJR `AndOp` cannot read one past the last cell.

```sh
cjc example/most_frequent/extracted/most_frequent.cj example/most_frequent/test/most_frequent_test.cj --test -O2 -o /tmp/most_frequent_tests
/tmp/most_frequent_tests
```

The comparative benchmark produces 693 timed samples with all checks
passing. See `example/most_frequent/benchmark/results/` and the tutorial section
for methodology and charts. The complete functional `mf_sort_scan_correct`
theorem proves run-summary completeness, minimum original indices, and
the specified result without an oracle or assumed grouping correctness.

The complete actual CJR operation now has `mf_nonempty_wp`, `mf_wp`, and
`mf_spec_wp` Iris theorems. They prove allocation and full initialization
of both buffers, paired quicksort, the guarded inner run scan, the outer
best-summary scan with the first-occurrence tie rule, both final raw-buffer
frees, and preservation of the input. Expression equalities connect the
copy, partition, and group-loop contracts to the concrete terms supplied
to the printer. Empty input requires only a zero length field; positive
input requires the initialized array representation. The final result is
exactly the checked functional sort-and-scan result. The representative
assumption audit includes 73 theorems; the printer and native compiler
remain outside the CJR semantic correctness theorem.

## Unchecked array-list get — 9 October 2026

Array-list `get` now reads the backing buffer directly. Its Iris specification still requires an existing element (`xs !! i = Some x`); the proof preserves the array-list representation. `set` and `remove` retain their range checks and explicit panic branches. The former invalid-get exception test was removed because unchecked `get` no longer promises that behavior.

Both affected generated programs were regenerated from `cj_bundle` and compiled with Cangjie 1.0.5. All eight array-list cases and all six array-list sorting cases passed (14 total, no failures or errors). The SDK compatibility stubs used for linking were prepared in `/private/tmp/cjr-get-sdk`, outside the repository.

`make -j2 all` completed successfully, including the dependent sorting and most-frequent proofs and `verify_assumptions.v`. The assumption checks printed “Closed under the global context”. `make check-no-cheats` and `git diff --check` also passed.

## Removal of the panic operation — 9 October 2026

The `Panic` constructor and its substitution and printing cases have been removed from CJR. Array-list `get`, `set`, and `remove` now access the backing buffer without bounds checks; their proved contracts retain valid-index preconditions. The unused range-check lemma and error alias were deleted, and the invalid-set and invalid-remove exception tests were removed. Earlier sections of this report describe historical versions.

All 16 generated programs were regenerated from `cj_bundle` and compiled with Cangjie 1.0.5. Their 62 runtime tests passed with no failures or errors. No current Coq source or generated Cangjie file contains the panic operation. The language, array-list, and sorting proof modules also passed independent `coqchk` kernel checking. The source scan for admissions and declared axioms and `git diff --check` passed.

The full `make -j2 all` build completed successfully, including every dependent proof and `verify_assumptions.v`; the assumption audit reported the checked theorems closed under the global context.

## Primitive signed remainder — 9 October 2026

Added `RemOp`, modeled by `Z.rem` for integer operands with a nonzero divisor,
and printed as Cangjie `%`. The new `wp_rem` rule requires a nonzero divisor.
Core regression examples check all four operand-sign combinations, rejection
of a zero divisor, and rejection of a non-integer operand.

HashMap normalization now uses one primitive remainder and at most one
addition. `residue_spec` proves the original nonnegative mathematical-modulo
contract for positive capacity; `residue_wp` proves the new implementation.
The loop recurrences and their stack-slot proofs have been removed.

All 16 printer-emitted programs were regenerated, compiled with Cangjie 1.0.5
cjnative, and tested using the SDK linker workaround described above.
All **64 tests passed**, with no failures or errors. HashMap now has 15 cases:
the two new cases check signed remainder and normalization, both Int64
extremes at capacities 3 and 16, and insertion, lookup, and removal of extreme
keys. The remaining 49 cases also pass, including the 11 most-frequent cases.
Logs and binaries remain outside the repository.

`make -j4 verify` passed: all 25 modules were checked independently by
`coqchk`, the source scans found no admissions or declared axioms, and all
75 audited theorem reports were closed under the global context. The audit
now includes `wp_rem` and the normalized `residue_spec` contract.

Both complete benchmark suites were rerun sequentially after verification:
all 1,512 collection measurements and 693 most-frequent measurements passed
their checksum checks. Metadata hashes match the measured generated sources.
The benchmark tables and figures were regenerated, and the tutorial PDF was
rebuilt and visually checked. `git diff --check` passes. Benchmark runners now
write LF-terminated CSV records to avoid trailing-whitespace diagnostics.

## Zero-filled allocation and iterative HashMap lookup — 9 October 2026

The printer now emits `calloc(count, 8)` for primitive allocation, supplying
zero-filled `Int64` storage on successful native allocations. The core's
allocation rule and existing zero-array proofs are unchanged. Direct raw
allocations in the frame-call, swap, and sum-block test fixtures use the same
foreign allocator.

HashMap `get` and `contains` now use a dedicated bounded while loop returning
`Int64Option`. It skips tombstones, wraps once, and terminates on an empty
slot, a matching key, or capacity exhaustion. Insertion and removal retain
the slot-aware probe. `lookup_loop_spec`, `lookup_buffer_spec`, and
`lookup_spec` connect the new implementation to the existing pure probe and
abstract map; the public lookup contracts remain unchanged.

All 16 printer-emitted programs were regenerated and compiled with Cangjie
1.0.5 cjnative using the SDK linker workaround above. All **66 native tests
passed** with no failures or errors. HashMap has 17 cases, including repeated
dirty/free/reallocate checks of fresh arrays and all three map buffers, and
lookup through tombstones across a wraparound collision chain. The existing
full-cycle tombstone miss test also passed.

`make -j4 verify` passed: `coqchk` checked all 25 modules, source scans found
no admissions or declared axioms, and all **79 audited theorem reports** were
closed under the global context. The four added audit entries cover the
stopped loop, loop induction, local-state wrapper, and abstract lookup.

Both benchmark suites passed all checksum checks: **1,512 collection samples**
and **693 most-frequent samples**. The saved metadata hashes match the measured
sources. Figures, tables, benchmark commentary, and the tutorial were updated.
Collision lookup at n=4,096 is 3.48 microseconds for CJR versus 1.02 for stdlib,
with median paired ratio 3.43; the preceding saved CJR median was 19.41
microseconds. These are separate desktop runs with allocation and lookup
changed together, not an isolated timing study of either change.

Successful native allocation now supplies the initialization required by the
proofs. Allocation failure, arbitrary finite-machine overflow, and correctness
of the printer and compiler remain outside the formal results.

The tutorial PDF was compiled twice after the final documentation edits
(129 pages) and its updated lookup proofs, benchmark pages, figures, and
allocation discussion were visually checked. All 29 HashMap proof listings
cover complete current lemma ranges. `git diff --check` passed.

## Native bulk copying for ArrayList — 9 October 2026

The printer recognizes the exact verified ArrayList `grow` and `remove`
method bodies and emits `memmove` for their internal copy loop. Growth copies
between separate allocations; removal moves a suffix left inside one buffer.
The emitted byte count is eight times the number of `Int64` words. A positive
length guard skips empty copies. Tail clearing, size, capacity, version,
returned values, and the public contracts are preserved.

The CJR loop bodies and their Iris proofs are unchanged. Recognition is
restricted because an arbitrary forward-copy loop with right overlap can
propagate overwritten values, unlike snapshot `memmove`. Four Rocq
regressions check enabled canonical methods and disabled unrelated bodies.
The native FFI and printer are still outside the formal correctness theorem.

All 16 printer-emitted programs were regenerated and compiled with Cangjie
1.0.5 cjnative. All **69 native tests passed**, with no failures or errors.
ArrayList now has nine cases, including three new cases for repeated
front-removal/append cycles across capacities, middle removal after multiple
growths with tail clearing and subsequent append, and empty growth with a
zero-length copy followed by single-element removal.

`make -j4 verify` passed: all 25 modules were kernel-checked by `coqchk`,
source scans found no admissions or declared axioms, and all **88 audited
reports** were closed under the global context. The nine added entries cover
the two copy kernels, growth, append, removal, and the four recognition
regressions.

The complete collection benchmark refresh passed all **1,512 checked
measurements**. At n=4,096, front removal plus append fell from 4,995.85 to
309.01 ns per pair (about 16.2 times faster), versus 316.96 ns for stdlib;
the median paired ratio is 0.97, down from 15.76. At n=256 and 1,024, CJR
improved by about 14.1 and 15.7 times respectively. Append-and-scan at
n=16,384 fell from 4.82 to 3.60 ns per item. These comparisons span separate
desktop runs. Front removal retains linear complexity.

The most-frequent source is unchanged and its existing saved measurements
remain valid; its source hash was checked. Collection figures and tables,
benchmark commentary, and the tutorial were refreshed for the new results.

The final tutorial PDF compiled successfully in two passes (130 pages).
The emitted bulk-copy code, copy-domain explanation, result table, comparison
figure, and benchmark interpretation were rendered and visually checked.
Metadata hashes match the measured sources; list, array, HashMap, and
most-frequent generated sources are unchanged by this repair. All 29
HashMap proof listings retain complete current source ranges.
`git diff --check` passed.
