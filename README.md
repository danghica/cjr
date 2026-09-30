# cjr

This is a mechanization of a performance-parity Cangjie fragment (called Cangjie Radical) in Coq with [Iris](https://iris-project.org/). 
This allows the formal specification and proof of cjr programs using Iris.  

The language is sequential and monomorphic. Mutable `var` bindings are stack slots, `CPointer` blocks are a raw word heap, and final class fields live on a separate object heap. The program logic is Iris's weakest precondition over an evaluation-context semantics.

Actual compilable and executable Cangjie code is extracted from the the verification files using a Galina printer. 

## Build

The development is checked with Coq 8.20.1, coq-stdpp 1.12.0, and coq-iris 4.4.0.

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.1 coq-stdpp.1.12.0 coq-iris.4.4.0
eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make
make verify    # optional: coqchk + Print Assumptions audit (see Makefile.local-late)
```

Coq is invoked with `-w +admitted-proof` (and a few other promoted warnings in `_CoqProject`), and `make verify` additionally rejects `Admitted` and declared `Axiom` bypasses in the source. We do not use `-w +all` here: on Coq 8.20 it turns a benign Iris/stdlib `Fin.vo` notice into a build error. `make verify` runs `coqchk` on all `.vo` files (Coq 8.20 has no `--admit-opaque` switch; opaque `Qed` proofs are checked unless you pass `-admit`) and checks that representative adequacy theorems print **Closed under the global context** (`theories/verify_assumptions.v`).

## Layout

- `theories/lang.v` — syntax, three-region state, small-step semantics
- `theories/primitive_laws.v` — points-to facts and weakest-precondition rules
- `theories/adequacy.v` — a proved specification does not get stuck
- `theories/examples/` — local arithmetic, stack structs, raw blocks, classes, framing, and a hand-written vtable

Generics, inheritance, `enum`/`match`, concurrency, garbage collection, and a translation from full Cangjie are out of scope.

## Extracted Cangjie

`make cj` prints each file in `theories/examples/` to `generated/cj/`. Counts are `wc -l` of the whole file. A `.v` file includes the program, the specification, and the proofs.

| Spec | Lines | Extracted | Lines | Spec / extracted |
|---|---:|---|---:|---:|
| `theories/examples/arith.v` | 78 | `generated/cj/arith.cj` | 18 | 4.3 |
| `theories/examples/struct_upd.v` | 57 | `generated/cj/struct_upd.cj` | 27 | 2.1 |
| `theories/examples/cell.v` | 35 | `generated/cj/cell.cj` | 15 | 2.3 |
| `theories/examples/swap.v` | 40 | `generated/cj/swap.cj` | 18 | 2.2 |
| `theories/examples/sum_block.v` | 90 | `generated/cj/sum_block.cj` | 20 | 4.5 |
| `theories/examples/class_upd.v` | 45 | `generated/cj/class_upd.cj` | 23 | 2.0 |
| `theories/examples/frame_call.v` | 37 | `generated/cj/frame_call.cj` | 20 | 1.9 |
| `theories/examples/vtable.v` | 70 | `generated/cj/vtable.cj` | 33 | 2.1 |
| `theories/examples/list.v` | 227 | `generated/cj/list.cj` | 54 | 4.2 |
| `theories/examples/list_rev.v` | 287 | `generated/cj/list_rev.cj` | 65 | 4.4 |
| `theories/examples/array.v` | 354 | `generated/cj/array.cj` | 39 | 9.1 |
| `theories/examples/array_list.v` | 2416 | `generated/cj/array_list.cj` | 153 | 15.8 |
| `theories/examples/qsort.v` | 1749 | `generated/cj/qsort_array.cj` (76), `generated/cj/qsort_array_list.cj` (153) | 229 | 7.6 |
| `theories/examples/hash_map.v` | 3116 | `generated/cj/hash_map.cj` | 251 | 12.4 |
| **Total** | **8601** | | **965** | **8.9** |


The shared `hm_tactics.v` evaluation-context automation adds 110 supporting lines outside the example counts above.

## In-place list reversal

`theories/examples/list_rev.v` reuses `list.is_list`, reverses existing cons links, and proves `reverse_spec` and `reverse_twice_spec` without admissions or additional axioms. The loop theorem establishes an empty remainder and a reversed accumulator. One fresh empty sentinel separates the two owned chains.

The tutorial includes a detailed subsection for each definition and lemma, complete checked proof listings, and explanations of the invariant, each memory step, the induction, and the final scope cleanup. `make cj` includes the standalone `generated/cj/list_rev.cj`; `test/list_rev_test.cj` covers six runtime cases, including changes observed through references to the original nodes. See `test/report.md` for the dated results.

## Verified hash map

`theories/examples/hash_map.v` now proves every operation and its supporting kernels without admissions. A bounded probe wraps indexes safely, searches beyond tombstones for existing keys, and returns a precise finite-map lookup result. Insertion grows only for a missing key at the half-full limit; rehashing preserves every live entry, skips tombstones, and restores placement under doubled capacity. The stored size agrees with the finite map throughout.

The tutorial explains the representation, remainder and probe invariants, array ownership, insertion and removal proofs, rehash induction, and client compositions in detail. The generated implementation uses `ProbeResult` and `Int64Option` value structs. `test/hash_map_test.cj` contains 13 runtime cases, including collisions, wraparound, negative keys, zero values, tombstone reuse, and repeated growth. `make verify` audits the public contracts and supporting kernels in addition to the existing adequacy and reversal theorems.

`add_spec` and its client theorems retain the resulting capacity existentially because insertion can grow. `grow(minCap)` performs one doubling; the retained argument does not promise arbitrary minimum capacity. The CJR integer model is unbounded; the proof does not establish absence of `Int64` overflow for arbitrary machine inputs.
