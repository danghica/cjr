# Unit test report

Date: 29 September 2026.

Compiler: Cangjie 1.0.5 (cjnative), target aarch64-apple-darwin.

Each extracted file was compiled on its own with its test file, because every file declares `malloc`, `free`, and `main`, and both `array.cj` and `array_list.cj` declare `class Array`. The quicksort files declare that class as well, and `qsort_array_list.cj` also declares `class ArrayList`. The command was:

```sh
cjc generated/cj/<name>.cj test/<name>_test.cj --test -o test/bin/<name>_test
```

The tests use `@Test`, `@TestCase`, and `@Expect` from the Cangjie `std.unittest` framework. The test files are ordinary Cangjie. The files under test are the extracted CJR programs in `generated/cj/`, unchanged.

The bundled linker in this SDK does not read the macOS 27 `libSystem.tbd`. The binaries were linked with `SDKROOT` pointed at a copy of the macOS 26 SDK whose stub files also list `arm64-macos`. That change is outside the repository.

Out-of-range indexes are not called. In the extracted array list those arms are a null read, which stops the process. `cell` discards the value it loads, so its test only checks that the call returns.

## Results

32 cases ran. 32 passed. 0 failed.

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
| `array.cj` | 3 | passed |
| `array_list.cj` | 6 | passed |
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
