# Unit test report

Date: 30 September 2026.

Compiler: Cangjie 1.0.5 (cjnative), target aarch64-apple-darwin.

Each extracted file was compiled on its own with its test file, because every file declares `malloc`, `free`, and `main`, and both `array.cj` and `array_list.cj` declare `class Array`. The quicksort files declare that class as well, and `qsort_array_list.cj` also declares `class ArrayList`. The command was:

```sh
cjc generated/cj/<name>.cj test/<name>_test.cj --test -o test/bin/<name>_test
```

The tests use `@Test`, `@TestCase`, and `@Expect` from the Cangjie `std.unittest` framework. The test files are ordinary Cangjie. The files under test are the extracted CJR programs in `generated/cj/`, unchanged.

The bundled linker in this SDK does not read the macOS 27 `libSystem.tbd`. The binaries were linked with `SDKROOT` pointed at a copy of the macOS 26 SDK whose stub files also list `arm64-macos`. That change is outside the repository.

Out-of-range indexes are not called. In the extracted array list those arms are a null read, which stops the process. `cell` discards the value it loads, so its test only checks that the call returns.

## Results

51 cases ran. 51 passed. 0 failed.

All fifteen generated programs were rebuilt and rerun, including the 13 hash map cases and six list reversal cases.

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
| `array_list.cj` | 6 | passed |
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

The unchanged generated `generated/cj/list_rev.cj` was compiled together with `test/list_rev_test.cj` using Cangjie 1.0.5 (cjnative), aarch64-apple-darwin. The six cases ran and all passed: 0 failures, 0 errors, 0 skipped. This run is separate from the historical 32-case run above.

```sh
CANGJIE_HOME=/private/tmp/cangjie-sdk/cangjie \
SDKROOT=/private/tmp/cj-sdk \
DYLD_LIBRARY_PATH=/private/tmp/cangjie-sdk/cangjie/runtime/lib/darwin_aarch64_cjnative \
/private/tmp/cangjie-sdk/cangjie/bin/cjc \
  generated/cj/list_rev.cj test/list_rev_test.cj --test -o test/bin/list_rev_test
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

The regenerated `hash_map.cj` is compiled directly with `test/hash_map_test.cj`. All 13 cases pass. Eight regression cases extend the five original cases:

- `collisionsAndWraparound` checks three colliding keys starting at the last slot and an absent colliding key.
- `tombstoneDoesNotHideExistingKey` removes the first key, updates a later colliding key without duplicating it, and inserts another key into a reusable slot.
- `negativeKeysAndZeroValues` distinguishes a stored zero from absence and checks negative colliding keys.
- `updateAtLoadLimitDoesNotGrow` keeps capacity 16 and size eight while updating an existing entry.
- `growthPreservesEveryEntry` inserts nine colliding keys, checks capacity 32, and reads every value afterward.
- `repeatedGrowthAndRemoval` inserts 80 keys through several doublings, checks every entry, removes 40, checks a missing removal, and reinserts the deleted keys with new values.
- `explicitGrowthPreservesContents` doubles a populated map and checks its size and colliding entries.
- `tombstonesAcrossEntireProbeCycle` turns all 16 slots into tombstones, checks a bounded absent lookup, and successfully reuses a slot.

The Coq module contains no admissions. `make verify` checks all 23 compiled modules with `coqchk`, rejects source bypasses, and audits 29 theorems as closed under the global context. The audit covers all public hash map methods, the remainder, scan, insertion, and rehash kernels, and the initialization and insertion client compositions. `make cj` regenerates the implementation and rebuilds the detailed tutorial, including complete checked proof listings.

The printer changes also warranted rebuilding and rerunning every existing extracted-program test: all 51 cases across 15 programs pass. Compiler logs and binaries were kept outside the repository. The macOS SDK workaround described above was still required. The compiler reports benign unused-variable warnings for the retained growth hint and illustrative main result.

The formal results concern the CJR expressions, whose integers are unbounded. Runtime tests validate the printed `Int64` programs on the tested inputs; the printer, compiler, and freedom from arbitrary machine-integer overflow are not formally verified. `grow(minCap)` performs one doubling, rather than guaranteeing an arbitrary requested minimum.
