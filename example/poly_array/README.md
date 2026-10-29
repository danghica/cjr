# Polymorphic arrays

This is a separate adaptation of the original [integer array](../array/README.md).
The original implementation, proofs, extraction, and clients remain unchanged.
`PolyArray<T>` has a static factory `PolyArray<T>.make(n, seed)` and instance
methods `a.length()`, `a.get(i)`, and `a.set(i, x)`. The class supplies `T`;
the instance calls need no repeated type arguments. The explicit seed replaces
integer zero initialization.

```cangjie
let a = PolyArray<Bool>.make(3, false)
a.set(1, true)
let x = a.get(1) // true
```

## Representation and proofs

[poly_array.v](rocq/poly_array.v) adapts `array.is_array` by replacing `list Z`
with `list val`: the object still owns its length, data pointer, block metadata,
and a separating conjunction of indexed cells. `poly_int_adaptation` proves
that integer instances of the new predicate are equivalent to the original
predicate. This is a core-model equivalence, not a native-layout claim.

The public contracts prove seeded construction, length, lookup, and update.
The derived `poly_set_get_same`, `poly_set_get_other`, `poly_set_length`, and
`poly_fresh_get` results recover the original array equations for any element
representation. Construction requires a positive length; access requires an
in-range index. Seeds and values supplied to update must be closed under term
substitution, including closed functions if functions are stored.

`poly_array_rep R xs a` adds one `R v` resource per element to structural array
ownership. The owned read returns `R v` and a separating implication that
restores the full array when `R v` is returned. The owned update consumes the
new resource and returns the overwritten resource. Neither duplicates it.
Seeded construction requires one resource per repeated occurrence; a single
resource suffices when it is persistent. Repeating an object reference creates
aliases, not independently owned copies of the referenced object. The nested
singleton proof demonstrates ownership transfer into an array of arrays.

[buffer.v](../../theories/buffer.v) defines initialized storage entirely with
existing core operations. [buffer_laws.v](../../theories/buffer_laws.v) proves
the recursive fill and allocation contracts. `GTBuffer` and the three
`GEBuffer*` source forms participate in scope checks, type substitution, and
both erasure laws. The static factory uses `GEStaticCall`; the instance
operations use `GEMethod`. Both resolve the explicit `PolyArray` owner and
erase to the same argument-tuple calling convention used by other methods. `poly_main_adequate` derives safety for the concrete Boolean
constructor through the existing CJR adequacy theorem. This does not establish
general typing soundness or relational parametricity.

## Extraction boundary

The generic printer emits managed `std.core.Array<T>` storage under the reserved
alias `CjrBuffer`. Unconstrained `CPointer<T>` is rejected by Cangjie 1.0.5
because its elements must satisfy `CType`; no native byte width for an arbitrary
`T` is assumed. The old integer array continues to use raw `CPointer<Int64>`.

The core models a word per value. The correspondence between its derived
allocation/fill and the native managed array remains in the printer/runtime
trust boundary. Garbage collection and allocation failure are not modeled.
Native lengths must fit `Int64`. Native bounds checks stay enabled; the proofs
require valid indices. Receiver and write annotations are checked by the native
compiler. A store's buffer, index, and value are evaluated once, in order, as
arguments to a typed helper before assignment.

## Reproduce

From the repository root:

```sh
make -C example/poly_array test
make -C example/poly_array benchmark
make verify
make cj
```

The eight native tests cover seeded initialization, integers, booleans,
independent arrays, nested aliasing, generic structs, functions, and unit.
Rocq regressions cover nested instantiation, scope/arity rejection, erasure,
integer/Boolean round trips, and nested ownership. Shared extraction tests
reject incompatible buffer annotations and stores and execute a side-effect
trace that checks evaluation order for all three buffer forms.

## Benchmark

The [comparison harness](benchmark/poly_array_bench.cj) uses the same workloads
and sizes as the existing monomorphic array benchmark. Both complete generated
implementations are compiled together at `-O2`; the [build helper](benchmark/compile.py)
omits only their final demonstration entry points and never edits either source.

At lengths 256, 4,096, and 65,536, it measures permuted reads and permuted
writes followed by sequential reads. Both arrays are populated before timing.
Three independent processes each take seven samples per implementation, with
alternating execution order, warm-up, independent calibration towards 20 ms,
and checked checksums: 252 measurements in total. Raw-block cleanup occurs
after timing. Allocation and initialization costs are excluded.

The saved [report](benchmark/results/report.html), [raw samples](benchmark/results/raw.csv),
[summary](benchmark/results/summary.json), and [metadata](benchmark/results/metadata.json)
record the measurements and source hashes. The measurements from before the
method refactor are retained in [free-functions/](benchmark/results/free-functions/).
The workloads and compiler settings are unchanged. This comparison includes managed
storage, bounds checks, wrappers, and compiler choices; it does not isolate the
cost of a type parameter or predict results for other types. The tutorial has
a separate chapter with the logical treatment and measured results.
